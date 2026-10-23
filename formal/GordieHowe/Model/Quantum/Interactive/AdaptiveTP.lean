-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.Adaptive
public import GordieHowe.Model.QROM.CircuitCount
public import GordieHowe.Model.Quantum.Interactive.Output

@[expose] public section

/-!
# The trace-preserving form of an adversary with run-time kinds

The model's semantics of an adversary with run-time kinds (`AdaptiveIAlg.toKindAlg`,
`GordieHowe/Model/Quantum/Interactive/Adaptive.lean`) loses weight in two ways: the adversary's own Kraus maps are
trace-non-increasing (non-termination), and a branch that asks for one query slot more than its
budget is projected away. The trace-preserving form `AdaptiveIAlg.toTPKindAlg` (proof-internal)
keeps that weight: such a branch moves to the **ended** value `budget + 1` of the query counter (for
non-termination, with the adversary's workspace given by the halting operator of its Kraus map), and
an ended branch requests at every later slot, so it makes no queries of its own. It has the
registers of `toKindAlg`.

On the branches that have not ended, the two compositions with a challenger run alike, and an ended
branch never comes back (`intertwined_fullCircBoth`): the state of the model's composition is the
part of the trace-preserving composition on the branches that have not ended. So every event of the
composed registers has at most the probability under the trace-preserving composition
(`AdaptiveIAlg.realLaw_composeBothOut_le`). The extractor of simulation-sound extractability runs
the trace-preserving form, whose Kraus maps are all trace preserving.

## Intertwining

`cutTo S ρ` is `P ρ P` for the projector `P` onto the basis states in `S`. Two circuits with
reprogrammed queries are intertwined on a set `S` of the work register (`Intertwined`) when they
have the same shape, the same reprogrammed queries, and at each Kraus map
`cutTo S (K₂ ρ) = K₁ (cutTo S ρ)`; then the same holds for their runs (`Intertwined.run`).
-/

open Finset Matrix
open scoped BigOperators ENNReal Kronecker

namespace GordieHowe.Quantum

/-! ### The part of a matrix on a set of basis states -/

section Cut

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open Classical in
/-- **The part of a matrix on a set `S` of basis states**: `P ρ P` for the projector `P` onto the
span of `S`. -/
noncomputable def cutTo (S : Set ι) (ρ : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  fun i j => if i ∈ S ∧ j ∈ S then ρ i j else 0

open Classical in
/-- The projector onto the span of `S`. -/
noncomputable def projOn (S : Set ι) : Matrix ι ι ℂ :=
  Matrix.diagonal fun i => if i ∈ S then 1 else 0

theorem projOn_conjTranspose (S : Set ι) : (projOn S)ᴴ = projOn S := by
  classical
  rw [projOn, Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  by_cases h : i ∈ S <;> simp [h]

theorem cutTo_eq (S : Set ι) (ρ : Matrix ι ι ℂ) : cutTo S ρ = projOn S * ρ * projOn S := by
  classical
  ext i j
  simp only [cutTo, projOn, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> simp [hi, hj]

theorem cutTo_add (S : Set ι) (ρ σ : Matrix ι ι ℂ) : cutTo S (ρ + σ) = cutTo S ρ + cutTo S σ := by
  rw [cutTo_eq, cutTo_eq, cutTo_eq, Matrix.mul_add, Matrix.add_mul]

theorem cutTo_sum {κ : Type*} (S : Set ι) (s : Finset κ) (ρ : κ → Matrix ι ι ℂ) :
    cutTo S (∑ k ∈ s, ρ k) = ∑ k ∈ s, cutTo S (ρ k) := by
  simp_rw [cutTo_eq, Finset.mul_sum, Finset.sum_mul]

omit [Fintype ι] [DecidableEq ι] in
theorem cutTo_cutTo (S : Set ι) (ρ : Matrix ι ι ℂ) : cutTo S (cutTo S ρ) = cutTo S ρ := by
  classical
  ext i j
  simp only [cutTo]
  split_ifs <;> simp_all

/-- A matrix that keeps the classes of `S` commutes with the projector onto `S`. -/
theorem projOn_mul_comm {M : Matrix ι ι ℂ} {S : Set ι}
    (hM : ∀ i j, M i j ≠ 0 → (i ∈ S ↔ j ∈ S)) : projOn S * M = M * projOn S := by
  classical
  ext i j
  simp only [projOn, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases h : M i j = 0
  · simp [h]
  · have := hM i j h
    by_cases hi : i ∈ S
    · simp [hi, this.1 hi]
    · have hj : j ∉ S := fun h' => hi (this.2 h')
      simp [hi, hj]

end Cut

namespace KrausMap

variable {R R₁ T : Type*} {ι : Type*} [Fintype R] [Fintype R₁] [Fintype T] [Fintype ι]
  [DecidableEq ι]

/-- **A Kraus map that keeps the classes of `S` commutes with the part on `S`.** -/
theorem cutTo_apply_of_keeps (K : KrausMap R ι ι) {S : Set ι}
    (hK : ∀ r i j, K.op r i j ≠ 0 → (i ∈ S ↔ j ∈ S)) (ρ : Matrix ι ι ℂ) :
    cutTo S (K ρ) = K (cutTo S ρ) := by
  rw [KrausMap.apply, KrausMap.apply, cutTo_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [cutTo_eq, cutTo_eq]
  have h := projOn_mul_comm (hK r)
  have h' : (K.op r)ᴴ * projOn S = projOn S * (K.op r)ᴴ := by
    have := congrArg Matrix.conjTranspose h
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, projOn_conjTranspose] at this
  simp only [Matrix.mul_assoc]
  rw [h', ← Matrix.mul_assoc (projOn S) (K.op r), h]
  simp only [Matrix.mul_assoc]

/-- **Kraus maps whose operators agree on `S` agree on matrices on `S`.** -/
theorem apply_cutTo_congr {K₁ K₂ : KrausMap R ι ι} {S : Set ι}
    (h : ∀ r, K₂.op r * projOn S = K₁.op r * projOn S) (ρ : Matrix ι ι ℂ) :
    K₂ (cutTo S ρ) = K₁ (cutTo S ρ) := by
  simp only [KrausMap.apply, cutTo_eq]
  refine Finset.sum_congr rfl fun r _ => ?_
  have h' : projOn S * (K₂.op r)ᴴ = projOn S * (K₁.op r)ᴴ := by
    rw [← projOn_conjTranspose S, ← Matrix.conjTranspose_mul, h r, Matrix.conjTranspose_mul]
  calc K₂.op r * (projOn S * ρ * projOn S) * (K₂.op r)ᴴ
      = (K₂.op r * projOn S) * ρ * (projOn S * (K₂.op r)ᴴ) := by simp only [Matrix.mul_assoc]
    _ = (K₁.op r * projOn S) * ρ * (projOn S * (K₁.op r)ᴴ) := by rw [h r, h']
    _ = _ := by simp only [Matrix.mul_assoc]

/-- **A Kraus map with more operators, that never leaves `Sᶜ`, intertwines on `S`** with a Kraus
map whose operators are the first family's on `S`: if the operators `K₂.op (inl r)` restricted to
`S` and cut to `S` are `K₁.op r` on `S`, the operators `K₂.op (inr t)` send nothing into `S`, and no
operator of `K₂` sends `Sᶜ` into `S`, then `cutTo S (K₂ ρ) = K₁ (cutTo S ρ)`. -/
theorem cutTo_apply_of_absorbing {K₁ : KrausMap R₁ ι ι} {K₂ : KrausMap (R₁ ⊕ T) ι ι} {S : Set ι}
    (hl : ∀ r, projOn S * K₂.op (.inl r) * projOn S = K₁.op r * projOn S)
    (hr : ∀ t, projOn S * K₂.op (.inr t) = 0)
    (habs : ∀ x i j, K₂.op x i j ≠ 0 → j ∉ S → i ∉ S) (ρ : Matrix ι ι ℂ) :
    cutTo S (K₂ ρ) = K₁ (cutTo S ρ) := by
  classical
  have hP : ∀ x, projOn S * K₂.op x = projOn S * K₂.op x * projOn S := by
    intro x
    ext i j
    simp only [projOn, Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hi : i ∈ S
    · by_cases hj : j ∈ S
      · simp [hi, hj]
      · simp only [hi, hj, if_true, if_false, one_mul, mul_zero]
        by_contra hne
        exact habs x i j hne hj hi
    · simp [hi]
  rw [KrausMap.apply, KrausMap.apply, cutTo_sum, Fintype.sum_sum_type]
  have hzero : ∀ t, cutTo S (K₂.op (.inr t) * ρ * (K₂.op (.inr t))ᴴ) = 0 := by
    intro t
    rw [cutTo_eq, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hr, Matrix.zero_mul, Matrix.zero_mul,
      Matrix.zero_mul]
  simp only [hzero, Finset.sum_const_zero, add_zero]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [cutTo_eq, cutTo_eq]
  have h1 : projOn S * (K₂.op (.inl r) * ρ * (K₂.op (.inl r))ᴴ) * projOn S =
      (projOn S * K₂.op (.inl r)) * ρ * (projOn S * K₂.op (.inl r))ᴴ := by
    rw [Matrix.conjTranspose_mul, projOn_conjTranspose]
    simp only [Matrix.mul_assoc]
  rw [h1, hP, hl r, Matrix.conjTranspose_mul, projOn_conjTranspose]
  simp only [Matrix.mul_assoc]

end KrausMap

namespace KrausMap

variable {R R₁ T : Type*} {ι : Type*} [Fintype R] [Fintype R₁] [Fintype T] [Fintype ι]
  [DecidableEq ι]

/-- `cutTo_apply_of_absorbing` with its hypotheses stated on entries. -/
theorem cutTo_apply_of_absorbing' {K₁ : KrausMap R₁ ι ι} {K₂ : KrausMap (R₁ ⊕ T) ι ι}
    {S : Set ι} [DecidablePred (· ∈ S)]
    (hl : ∀ r i j, j ∈ S → (if i ∈ S then K₂.op (.inl r) i j else 0) = K₁.op r i j)
    (hr : ∀ t i j, i ∈ S → K₂.op (.inr t) i j = 0)
    (habs : ∀ x i j, K₂.op x i j ≠ 0 → j ∉ S → i ∉ S) (ρ : Matrix ι ι ℂ) :
    cutTo S (K₂ ρ) = K₁ (cutTo S ρ) := by
  classical
  refine cutTo_apply_of_absorbing (fun r => ?_) (fun t => ?_) habs ρ
  · ext i j
    simp only [projOn, Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hj : j ∈ S
    · have := hl r i j hj
      by_cases hi : i ∈ S
      · simpa [hi, hj] using this
      · simp only [hi, if_false] at this
        simp [hi, hj, ← this]
    · simp [hj]
  · ext i j
    simp only [projOn, Matrix.diagonal_mul, Matrix.zero_apply]
    by_cases hi : i ∈ S
    · simp [hi, hr t i j hi]
    · simp [hi]

/-- The entries of a Kraus map on the first factor, moved along a basis equivalence. -/
theorem tensorId_reindex_op_apply {L κ : Type*} [Fintype L] [DecidableEq L] [Fintype κ]
    [DecidableEq κ] (K : KrausMap R ι ι) (e : ι × L ≃ κ) (r : R) (i j : κ) :
    ((K.tensorId L).reindex e).op r i j =
      K.op r (e.symm i).1 (e.symm j).1 * (1 : Matrix L L ℂ) (e.symm i).2 (e.symm j).2 := by
  simp [KrausMap.reindex, KrausMap.tensorId, Matrix.kroneckerMap_apply]

/-- **Intertwining on a factor**: `cutTo_apply_of_absorbing'` for Kraus maps on the first factor
moved along a basis equivalence, with the set read on the first factor. -/
theorem cutTo_tensorId_reindex_of_absorbing {L κ : Type*} [Fintype L] [DecidableEq L] [Fintype κ]
    [DecidableEq κ] {K₁ : KrausMap R₁ ι ι} {K₂ : KrausMap (R₁ ⊕ T) ι ι} {S : Set ι}
    [DecidablePred (· ∈ S)]
    (hl : ∀ r i j, j ∈ S → (if i ∈ S then K₂.op (.inl r) i j else 0) = K₁.op r i j)
    (hr : ∀ t i j, i ∈ S → K₂.op (.inr t) i j = 0)
    (habs : ∀ x i j, K₂.op x i j ≠ 0 → j ∉ S → i ∉ S) (e : ι × L ≃ κ) (ρ : Matrix κ κ ℂ) :
    cutTo {p | (e.symm p).1 ∈ S} (((K₂.tensorId L).reindex e) ρ) =
      ((K₁.tensorId L).reindex e) (cutTo {p | (e.symm p).1 ∈ S} ρ) := by
  classical
  refine cutTo_apply_of_absorbing' (fun r i j hj => ?_) (fun t i j hi => ?_)
    (fun x i j h hj => ?_) ρ
  · rw [tensorId_reindex_op_apply, tensorId_reindex_op_apply, ← hl r _ _ hj]
    by_cases hi : (e.symm i).1 ∈ S
    · have hi' : i ∈ {p | (e.symm p).1 ∈ S} := hi
      rw [if_pos hi', if_pos hi]
    · have hi' : i ∉ {p | (e.symm p).1 ∈ S} := hi
      rw [if_neg hi', if_neg hi, zero_mul]
  · rw [tensorId_reindex_op_apply, hr t _ _ hi, zero_mul]
  · rw [tensorId_reindex_op_apply] at h
    exact habs x _ _ (left_ne_zero_of_mul h) hj

end KrausMap

/-! ### Intertwined circuits with reprogrammed queries -/

theorem cutTo_submatrix {ι : Type*} [Fintype ι] [DecidableEq ι] {S : Set ι} {π : Equiv.Perm ι}
    (hπ : ∀ i, π.symm i ∈ S ↔ i ∈ S) (ρ : Matrix ι ι ℂ) :
    cutTo S (ρ.submatrix π.symm π.symm) = (cutTo S ρ).submatrix π.symm π.symm := by
  classical
  ext i j
  simp only [cutTo, Matrix.submatrix_apply, hπ]

namespace ReprogrammedCircuit

variable {V X Y : Type} [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y]

/-- The basis states whose work register lies in `Sv`. -/
abbrev workIn (Sv : Set V) : Set (QueryReg V 1 X Y) := {p | p.1 ∈ Sv}

/-- **Two circuits intertwined on a set `Sv` of the work register**: the same shape, the same
reprogrammed queries, and at each pair of Kraus maps `cutTo S (K₂ ρ) = K₁ (cutTo S ρ)` for the basis
states `S` with work register in `Sv`. -/
def Intertwined (Sv : Set V) : ReprogrammedCircuit V X Y → ReprogrammedCircuit V X Y → Prop
  | nil, nil => True
  | kraus K₁ c₁, kraus K₂ c₂ => (∀ ρ, cutTo (workIn Sv) (K₂ ρ) = K₁ (cutTo (workIn Sv) ρ)) ∧
      Intertwined Sv c₁ c₂
  | rquery a₁ c₁, rquery a₂ c₂ => a₁ = a₂ ∧ Intertwined Sv c₁ c₂
  | _, _ => False

variable [AddGroup Y]

/-- **Intertwined circuits have intertwined runs.** -/
theorem Intertwined.run {Sv : Set V} (H : X → Y) : ∀ {c₁ c₂ : ReprogrammedCircuit V X Y},
    Intertwined Sv c₁ c₂ → ∀ ρ, cutTo (workIn Sv) (c₂.run H ρ) = c₁.run H (cutTo (workIn Sv) ρ)
  | nil, nil, _, _ => rfl
  | kraus K₁ c₁, kraus K₂ c₂, ⟨hK, hc⟩, ρ => by
    rw [ReprogrammedCircuit.run, ReprogrammedCircuit.run, hc.run H, hK]
  | rquery a₁ c₁, rquery a₂ c₂, ⟨ha, hc⟩, ρ => by
    subst ha
    rw [ReprogrammedCircuit.run, ReprogrammedCircuit.run, hc.run H,
      cutTo_submatrix (fun p => Iff.rfl)]
  | nil, kraus _ _, h, _ => h.elim
  | nil, rquery _ _, h, _ => h.elim
  | kraus _ _, nil, h, _ => h.elim
  | kraus _ _, rquery _ _, h, _ => h.elim
  | rquery _ _, nil, h, _ => h.elim
  | rquery _ _, kraus _ _, h, _ => h.elim

omit [AddGroup Y] in
theorem Intertwined.append {Sv : Set V} : ∀ {c₁ c₂ d₁ d₂ : ReprogrammedCircuit V X Y},
    Intertwined Sv c₁ c₂ → Intertwined Sv d₁ d₂ → Intertwined Sv (c₁ ++ d₁) (c₂ ++ d₂)
  | nil, nil, _, _, _, hd => hd
  | kraus _ c₁, kraus _ c₂, _, _, ⟨hK, hc⟩, hd => ⟨hK, Intertwined.append (c₁ := c₁) hc hd⟩
  | rquery _ c₁, rquery _ c₂, _, _, ⟨ha, hc⟩, hd => ⟨ha, Intertwined.append (c₁ := c₁) hc hd⟩
  | nil, kraus _ _, _, _, h, _ => h.elim
  | nil, rquery _ _, _, _, h, _ => h.elim
  | kraus _ _, nil, _, _, h, _ => h.elim
  | kraus _ _, rquery _ _, _, _, h, _ => h.elim
  | rquery _ _, nil, _, _, h, _ => h.elim
  | rquery _ _, kraus _ _, _, _, h, _ => h.elim

omit [AddGroup Y] in
theorem Intertwined.concat {Sv : Set V} : ∀ {cs ds : List (ReprogrammedCircuit V X Y)},
    List.Forall₂ (Intertwined Sv) cs ds → Intertwined Sv (ReprogrammedCircuit.concat cs) (ReprogrammedCircuit.concat ds)
  | [], [], _ => trivial
  | _ :: _, _ :: _, .cons h hs => h.append (Intertwined.concat hs)

/-- **Every Kraus map of the circuit keeps the classes of `Sv`.** -/
def KeepsAll (Sv : Set V) : ReprogrammedCircuit V X Y → Prop
  | nil => True
  | kraus K c => (∀ r i j, K.op r i j ≠ 0 → (i ∈ workIn Sv ↔ j ∈ workIn Sv)) ∧ KeepsAll Sv c
  | rquery _ c => KeepsAll Sv c

omit [AddGroup Y] in
/-- A circuit whose Kraus maps keep the classes of `Sv` is intertwined with itself. -/
theorem KeepsAll.intertwined {Sv : Set V} : ∀ {c : ReprogrammedCircuit V X Y}, KeepsAll Sv c →
    Intertwined Sv c c
  | nil, _ => trivial
  | kraus K c, ⟨hK, hc⟩ => ⟨fun ρ => K.cutTo_apply_of_keeps hK ρ, KeepsAll.intertwined (c := c) hc⟩
  | rquery _ c, hc => ⟨rfl, KeepsAll.intertwined (c := c) hc⟩

omit [AddGroup Y] in
theorem KeepsAll.append {Sv : Set V} : ∀ {c d : ReprogrammedCircuit V X Y}, KeepsAll Sv c →
    KeepsAll Sv d → KeepsAll Sv (c ++ d)
  | nil, _, _, hd => hd
  | kraus _ c, _, ⟨hK, hc⟩, hd => ⟨hK, KeepsAll.append (c := c) hc hd⟩
  | rquery _ c, _, hc, hd => KeepsAll.append (c := c) hc hd

omit [AddGroup Y] in
theorem KeepsAll.concat {Sv : Set V} : ∀ {cs : List (ReprogrammedCircuit V X Y)},
    (∀ c ∈ cs, KeepsAll Sv c) → KeepsAll Sv (ReprogrammedCircuit.concat cs)
  | [], _ => trivial
  | c :: cs, h => (h c (List.mem_cons_self ..)).append
      (KeepsAll.concat (cs := cs) fun d hd => h d (List.mem_cons_of_mem _ hd))

omit [AddGroup Y] in
/-- A basis permutation that keeps the classes of `Sv` keeps them as a Kraus map. -/
theorem keeps_ofPerm {Sv : Set V} {π : Equiv.Perm (QueryReg V 1 X Y)}
    (hπ : ∀ p, ((π p).1 ∈ Sv ↔ p.1 ∈ Sv)) :
    ∀ r i j, (KrausMap.ofPerm π).op r i j ≠ 0 → (i ∈ workIn Sv ↔ j ∈ workIn Sv) := by
  intro r i j h
  rw [KrausMap.ofPerm_op_apply] at h
  split_ifs at h with hij
  · rw [hij]
    exact hπ j
  · exact absurd rfl h

end ReprogrammedCircuit

/-! ### The trace-preserving form -/

namespace AdaptiveIAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  (A : AdaptiveIAlg X Y Req Resp O)

/-- The adversary's registers with a query counter. -/
abbrev CReg := DReg (A.W × Fin (A.budget + 2)) A.width X Y Req Resp

/-- **The ended value** `budget + 1` of the query counter. -/
def ended : Fin (A.budget + 2) := Fin.last (A.budget + 1)

/-- A permutation of the workspace with its counter, on the adversary's registers. -/
def wPerm (π : Equiv.Perm (A.W × Fin (A.budget + 2))) : Equiv.Perm A.CReg :=
  Equiv.prodCongr (Equiv.prodCongr π (Equiv.refl _)) (Equiv.refl _)

/-- The counter advanced from `c < budget` to `c + 1`, `budget` sent to `0`, and the ended value
kept. -/
def rot : Equiv.Perm (Fin (A.budget + 2)) :=
  (finRotate _).trans (Equiv.swap 0 A.ended)

/-- The counter advanced on the branches whose kind is a query, the ended value kept. -/
def tpShift : Equiv.Perm A.CReg :=
  A.wPerm (Equiv.prodShear (Equiv.refl A.W) fun w => if A.kind w then Equiv.refl _ else A.rot)

/-- The counter values `budget` and `budget + 1` exchanged. -/
def endSwap : Equiv.Perm A.CReg :=
  A.wPerm (Equiv.prodCongr (Equiv.refl A.W) (Equiv.swap (Fin.castSucc (Fin.last A.budget)) A.ended))

/-- The adversary's Kraus map number `k`, on its registers with the counter. -/
def cntKraus (k : StepIdx A.slots A.post) : KrausMap A.R A.CReg A.CReg :=
  ((A.step k).tensorId (Fin (A.budget + 2))).reindex A.cntSplit.symm

theorem toKindAlg_step (k : StepIdx A.slots A.post) :
    A.toKindAlg.step k = if (k : ℕ) < A.slots then
      ((A.cntKraus k).restrict A.inBudget).permConj (Equiv.refl _) A.cntShift
    else A.cntKraus k :=
  rfl

/-- The operators of the trace-preserving form: at a slot, the adversary's operator within the
budget followed by the counter advanced on query branches, and the adversary's operator on a branch
over the budget followed by the move to the ended value; the halting operator of the adversary's
Kraus map, ending the branch, at every counter value. -/
noncomputable def tpOp (k : StepIdx A.slots A.post) :
    A.R ⊕ (A.R ⊕ Fin (A.budget + 2)) → Matrix A.CReg A.CReg ℂ
  | .inl r => if (k : ℕ) < A.slots then
      (((A.cntKraus k).restrict A.inBudget).permConj (Equiv.refl _) A.tpShift).op r
    else (A.cntKraus k).op r
  | .inr (.inl r) => if (k : ℕ) < A.slots then
      (((A.cntKraus k).restrict fun d => !A.inBudget d).permConj (Equiv.refl _) A.endSwap).op r
    else 0
  | .inr (.inr c) =>
      ((A.step k).haltOp ⊗ₖ Matrix.single A.ended c (1 : ℂ)).submatrix A.cntSplit A.cntSplit

theorem restrict_permConj_conjTranspose_mul {R ι : Type*} [Fintype R] [Fintype ι] [DecidableEq ι]
    (K : KrausMap R ι ι) (p : ι → Bool) (τ : Equiv.Perm ι) (r : R) :
    (((K.restrict p).permConj (Equiv.refl _) τ).op r)ᴴ * ((K.restrict p).permConj (Equiv.refl _) τ).op r =
      (K.op r)ᴴ * Matrix.diagonal (fun i => if p i then 1 else 0) * K.op r := by
  simp only [KrausMap.permConj, KrausMap.restrict]
  rw [conjTranspose_submatrix, submatrix_mul_equiv]
  simp only [Equiv.coe_refl, Matrix.submatrix_id_id]
  rw [Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose]
  have hD : (Matrix.diagonal fun i => if p i then (1 : ℂ) else 0) *
      Matrix.diagonal (fun i => if p i then 1 else 0) =
      Matrix.diagonal fun i => if p i then 1 else 0 := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases hp : p i <;> simp [hp]
  have hs : (star fun i => if p i then (1 : ℂ) else 0) = fun i => if p i then 1 else 0 := by
    funext i
    by_cases hp : p i <;> simp [hp]
  rw [hs, Matrix.mul_assoc, ← Matrix.mul_assoc _ _ (K.op r), hD, Matrix.mul_assoc]

/-- **The trace-preserving form preserves the trace.** -/
theorem tpOp_tp (k : StepIdx A.slots A.post) :
    ∑ x, (A.tpOp k x)ᴴ * A.tpOp k x = 1 := by
  have hK : ∑ r, ((A.cntKraus k).op r)ᴴ * (A.cntKraus k).op r =
      ((∑ r, ((A.step k).op r)ᴴ * (A.step k).op r) ⊗ₖ (1 : Matrix (Fin (A.budget + 2))
        (Fin (A.budget + 2)) ℂ)).submatrix A.cntSplit A.cntSplit := by
    rw [sum_kronecker, submatrix_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [cntKraus, KrausMap.reindex, KrausMap.tensorId, Equiv.symm_symm]
    rw [conjTranspose_submatrix, submatrix_mul_equiv, conjTranspose_kronecker, conjTranspose_one,
      ← mul_kronecker_mul, Matrix.one_mul]
  have hH : ∑ c : Fin (A.budget + 2), (((A.step k).haltOp ⊗ₖ Matrix.single A.ended c (1 : ℂ)).submatrix
      A.cntSplit A.cntSplit)ᴴ * ((A.step k).haltOp ⊗ₖ Matrix.single A.ended c (1 : ℂ)).submatrix
      A.cntSplit A.cntSplit = ((((A.step k).haltOp)ᴴ * (A.step k).haltOp) ⊗ₖ
        (1 : Matrix (Fin (A.budget + 2)) (Fin (A.budget + 2)) ℂ)).submatrix A.cntSplit A.cntSplit := by
    have h1 : ∀ c : Fin (A.budget + 2), (((A.step k).haltOp ⊗ₖ Matrix.single A.ended c (1 : ℂ)).submatrix
        A.cntSplit A.cntSplit)ᴴ * ((A.step k).haltOp ⊗ₖ Matrix.single A.ended c (1 : ℂ)).submatrix
        A.cntSplit A.cntSplit = ((((A.step k).haltOp)ᴴ * (A.step k).haltOp) ⊗ₖ
          Matrix.single c c (1 : ℂ)).submatrix A.cntSplit A.cntSplit := fun c => by
      rw [conjTranspose_submatrix, submatrix_mul_equiv, conjTranspose_kronecker,
        conjTranspose_single, star_one, ← mul_kronecker_mul, single_mul_single_same, mul_one]
    simp only [h1]
    have hks : (((A.step k).haltOp)ᴴ * (A.step k).haltOp) ⊗ₖ
        (∑ c : Fin (A.budget + 2), Matrix.single c c (1 : ℂ)) =
        ∑ c : Fin (A.budget + 2), (((A.step k).haltOp)ᴴ * (A.step k).haltOp) ⊗ₖ
          Matrix.single c c (1 : ℂ) :=
      map_sum ({ toFun := fun M => (((A.step k).haltOp)ᴴ * (A.step k).haltOp) ⊗ₖ M
                 map_zero' := kronecker_zero _
                 map_add' := fun M N => kronecker_add _ M N } :
        Matrix (Fin (A.budget + 2)) (Fin (A.budget + 2)) ℂ →+ _) _ _
    rw [← submatrix_sum, ← hks, Matrix.sum_single_one]
  have hsplit : ∑ x, (A.tpOp k x)ᴴ * A.tpOp k x =
      ∑ r, ((A.cntKraus k).op r)ᴴ * (A.cntKraus k).op r + ∑ c : Fin (A.budget + 2),
        (((A.step k).haltOp ⊗ₖ Matrix.single A.ended c (1 : ℂ)).submatrix A.cntSplit A.cntSplit)ᴴ *
          ((A.step k).haltOp ⊗ₖ Matrix.single A.ended c (1 : ℂ)).submatrix A.cntSplit A.cntSplit := by
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type, ← add_assoc]
    congr 1
    by_cases hk : (k : ℕ) < A.slots
    · simp only [tpOp, hk, if_true, restrict_permConj_conjTranspose_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [← Matrix.add_mul, ← Matrix.mul_add, Matrix.diagonal_add]
      have hI : (fun i => (if A.inBudget i then (1 : ℂ) else 0) + if !A.inBudget i then 1 else 0) =
          fun _ => 1 := by
        funext i
        cases A.inBudget i <;> simp
      rw [hI, Matrix.diagonal_one, Matrix.mul_one]
    · simp [tpOp, hk]
  rw [hsplit, hK, hH]
  calc _ = ((∑ r, ((A.step k).op r)ᴴ * (A.step k).op r + ((A.step k).haltOp)ᴴ * (A.step k).haltOp)
        ⊗ₖ (1 : Matrix (Fin (A.budget + 2)) (Fin (A.budget + 2)) ℂ)).submatrix A.cntSplit
          A.cntSplit := by
        rw [add_kronecker]
        rfl
    _ = 1 := by
        rw [← (A.step k).haltOp_spec, add_sub_cancel, one_kronecker_one, submatrix_one_equiv]

/-- **The trace-preserving form** of an adversary with run-time kinds (proof-internal): the
registers of `toKindAlg`, the kind of a branch read as a request once its counter has the ended
value, and the Kraus maps `tpOp`, which are trace preserving (`tpOp_tp`). A branch over the budget,
and the weight the adversary's Kraus map loses, move to the ended value. -/
noncomputable abbrev toTPKindAlg : KindAlg X Y Req Resp O :=
  { A.toKindAlg with
    kind := fun w => A.kind w.1 || decide (w.2 = A.ended)
    R := A.R ⊕ (A.R ⊕ Fin (A.budget + 2))
    instFintypeR := inferInstance
    step := fun k => KrausChannel.toKrausMap ⟨A.tpOp k, A.tpOp_tp k⟩ }

theorem toTPKindAlg_step_tp (k : StepIdx A.slots A.post) :
    ∑ x, ((A.toTPKindAlg.step k).op x)ᴴ * (A.toTPKindAlg.step k).op x = 1 :=
  A.tpOp_tp k

/-! ### The trace-preserving form agrees with the model on the branches that have not ended -/

/-- The adversary's registers whose counter has not ended. -/
def aliveD : Set A.CReg := {d | d.workspace.2 ≠ A.ended}

instance : DecidablePred (· ∈ A.aliveD) := fun d => inferInstanceAs (Decidable (_ ≠ _))

theorem cntKraus_op_apply (k : StepIdx A.slots A.post) (r : A.R) (y x : A.CReg) :
    (A.cntKraus k).op r y x = (A.step k).op r (A.cntSplit y).1 (A.cntSplit x).1 *
      (1 : Matrix (Fin (A.budget + 2)) (Fin (A.budget + 2)) ℂ) y.workspace.2 x.workspace.2 := by
  rw [cntKraus, KrausMap.tensorId_reindex_op_apply, Equiv.symm_symm]
  rfl

theorem cntKraus_op_ne_zero {k : StepIdx A.slots A.post} {r : A.R} {y x : A.CReg}
    (h : (A.cntKraus k).op r y x ≠ 0) : y.workspace.2 = x.workspace.2 := by
  rw [cntKraus_op_apply] at h
  by_contra hne
  exact h (by rw [Matrix.one_apply_ne hne, mul_zero])

theorem restrict_permConj_op_apply {R ι : Type*} [Fintype R] [Fintype ι] [DecidableEq ι]
    (K : KrausMap R ι ι) (p : ι → Bool) (τ : Equiv.Perm ι) (r : R) (y x : ι) :
    ((K.restrict p).permConj (Equiv.refl _) τ).op r y x =
      (if p (τ.symm y) then 1 else 0) * K.op r (τ.symm y) x := by
  simp [KrausMap.permConj, KrausMap.restrict, Matrix.diagonal_mul]

theorem inBudget_of_alive_kind (d : A.CReg) :
    A.inBudget d = true ↔ (A.kind d.workspace.1 = true ∨
      d.workspace.2 ≠ Fin.castSucc (Fin.last A.budget)) := by
  simp [inBudget]

/-- Within the budget and before the end, the trace-preserving counter step is the model's, and
it does not reach the ended value. -/
theorem tpShift_eq_cntShift {z : A.CReg} (hz : A.inBudget z = true) (ha : z ∈ A.aliveD) :
    A.tpShift z = A.cntShift z ∧ A.cntShift z ∈ A.aliveD := by
  obtain ⟨⟨⟨w, c⟩, rq, rs⟩, p⟩ := z
  simp only [aliveD, Set.mem_setOf_eq, DReg.workspace] at ha
  rw [inBudget_of_alive_kind] at hz
  simp only [DReg.workspace] at hz
  cases hkw : A.kind w
  · have hc : (c : ℕ) < A.budget := by
      have h1 : c ≠ Fin.castSucc (Fin.last A.budget) := by simpa [hkw] using hz
      have h2 : (c : ℕ) ≠ A.budget := fun h => h1 (Fin.ext (by simpa using h))
      have h3 : (c : ℕ) ≠ A.budget + 1 := fun h => ha (Fin.ext (by simpa [ended] using h))
      omega
    have hnl : c ≠ Fin.last (A.budget + 1) := fun h => by
      have := congrArg Fin.val h
      simp at this
      omega
    have h1 := coe_finRotate_of_ne_last hnl
    have hr0 : finRotate (A.budget + 2) c ≠ 0 := fun h => by
      have := congrArg Fin.val h
      simp only [h1, Fin.val_zero] at this
      omega
    have hre : finRotate (A.budget + 2) c ≠ A.ended := fun h => by
      have := congrArg Fin.val h
      simp only [h1, ended, Fin.val_last] at this
      omega
    have hrot : A.rot c = finRotate (A.budget + 2) c := by
      rw [rot, Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne hr0 hre]
    refine ⟨?_, ?_⟩
    · simp [tpShift, cntShift, wPerm, hkw, hrot]
    · simpa [aliveD, cntShift, hkw, DReg.workspace] using hre
  · refine ⟨?_, ?_⟩
    · simp [tpShift, cntShift, wPerm, hkw]
    · simpa [aliveD, cntShift, hkw, DReg.workspace] using ha

theorem tpShift_ended {z : A.CReg} (hz : z.workspace.2 = A.ended) :
    (A.tpShift z).workspace.2 = A.ended := by
  obtain ⟨⟨⟨w, c⟩, rq, rs⟩, p⟩ := z
  simp only [DReg.workspace] at hz
  subst hz
  cases hkw : A.kind w
  · have h0 : finRotate (A.budget + 2) A.ended = 0 := by
      simp [ended]
    simp [tpShift, wPerm, hkw, rot, h0, DReg.workspace]
  · simp [tpShift, wPerm, hkw, DReg.workspace]

theorem endSwap_ended {z : A.CReg} (hz : A.inBudget z = false) :
    (A.endSwap z).workspace.2 = A.ended := by
  obtain ⟨⟨⟨w, c⟩, rq, rs⟩, p⟩ := z
  have h : c = Fin.castSucc (Fin.last A.budget) := by
    by_contra hc
    have := (A.inBudget_of_alive_kind (((w, c), rq, rs), p)).2 (Or.inr hc)
    rw [hz] at this
    exact Bool.false_ne_true this
  subst h
  simp [endSwap, wPerm, DReg.workspace]

theorem not_inBudget_alive {z : A.CReg} (hz : A.inBudget z = false) : z ∈ A.aliveD := by
  obtain ⟨⟨⟨w, c⟩, rq, rs⟩, p⟩ := z
  have h : c = Fin.castSucc (Fin.last A.budget) := by
    by_contra hc
    have := (A.inBudget_of_alive_kind (((w, c), rq, rs), p)).2 (Or.inr hc)
    rw [hz] at this
    exact Bool.false_ne_true this
  subst h
  intro he
  have := congrArg Fin.val he
  simp [ended, DReg.workspace] at this

theorem tpOp_inl_apply (k : StepIdx A.slots A.post) (r : A.R) (y x : A.CReg) :
    (A.toTPKindAlg.step k).op (.inl r) y x = A.tpOp k (.inl r) y x :=
  rfl

/-- On the branches that have not ended, the trace-preserving operators are the model's. -/
theorem tp_hl (k : StepIdx A.slots A.post) (r : A.R) (y x : A.CReg) (hx : x ∈ A.aliveD) :
    (if y ∈ A.aliveD then (A.toTPKindAlg.step k).op (.inl r) y x else 0) =
      (A.toKindAlg.step k).op r y x := by
  rw [tpOp_inl_apply, toKindAlg_step]
  by_cases hk : (k : ℕ) < A.slots
  · simp only [tpOp, hk, if_true, restrict_permConj_op_apply, Equiv.refl_symm, Equiv.refl_apply]
    set z := A.tpShift.symm y
    set z' := A.cntShift.symm y
    have hzy : A.tpShift z = y := Equiv.apply_symm_apply _ _
    have hzy' : A.cntShift z' = y := Equiv.apply_symm_apply _ _
    by_cases hL : (if A.inBudget z then (1 : ℂ) else 0) * (A.cntKraus k).op r z x = 0
    · rw [hL, ite_self]
      by_contra hR
      have hb : A.inBudget z' = true := by
        by_contra hb
        simp [hb] at hR
      have hK : (A.cntKraus k).op r z' x ≠ 0 := fun h => hR (by rw [h, mul_zero])
      have ha : z' ∈ A.aliveD := by
        simp only [aliveD, Set.mem_setOf_eq, A.cntKraus_op_ne_zero hK]
        exact hx
      obtain ⟨h1, h2⟩ := A.tpShift_eq_cntShift hb ha
      have hz : z = z' := by
        rw [← hzy'] at hzy
        exact A.tpShift.injective (hzy.trans h1.symm)
      rw [hz] at hL
      exact hR hL.symm
    · have hb : A.inBudget z = true := by
        by_contra hb
        simp [hb] at hL
      have hK : (A.cntKraus k).op r z x ≠ 0 := fun h => hL (by rw [h, mul_zero])
      have ha : z ∈ A.aliveD := by
        simp only [aliveD, Set.mem_setOf_eq, A.cntKraus_op_ne_zero hK]
        exact hx
      obtain ⟨h1, h2⟩ := A.tpShift_eq_cntShift hb ha
      have hz' : z' = z := by
        rw [← A.cntShift.symm_apply_apply z, ← h1, hzy]
      have hy : y ∈ A.aliveD := by
        rw [← hzy, h1]
        exact h2
      rw [if_pos hy, hz']
  · simp only [tpOp, hk, if_false]
    by_cases hy : y ∈ A.aliveD
    · rw [if_pos hy]
    · rw [if_neg hy]
      by_contra hR
      exact hy (by
        simp only [aliveD, Set.mem_setOf_eq, A.cntKraus_op_ne_zero (Ne.symm hR)]
        exact hx)

/-- The extra operators of the trace-preserving form end the branch. -/
theorem tp_hr (k : StepIdx A.slots A.post) (t : A.R ⊕ Fin (A.budget + 2)) (y x : A.CReg)
    (hy : y ∈ A.aliveD) : (A.toTPKindAlg.step k).op (.inr t) y x = 0 := by
  change A.tpOp k (.inr t) y x = 0
  rcases t with r | c
  · by_cases hk : (k : ℕ) < A.slots
    · simp only [tpOp, hk, if_true, restrict_permConj_op_apply]
      by_cases hb : A.inBudget (A.endSwap.symm y)
      · simp [hb]
      · have := A.endSwap_ended (Bool.of_not_eq_true hb)
        rw [Equiv.apply_symm_apply] at this
        exact absurd this hy
    · simp [tpOp, hk]
  · simp only [tpOp, Matrix.submatrix_apply, Matrix.kroneckerMap_apply]
    rw [Matrix.single_apply, if_neg, mul_zero]
    rintro ⟨h, -⟩
    exact hy h.symm

/-- **An ended branch stays ended** in the trace-preserving form. -/
theorem tp_habs (k : StepIdx A.slots A.post) (z : A.R ⊕ (A.R ⊕ Fin (A.budget + 2)))
    (y x : A.CReg) (h : (A.toTPKindAlg.step k).op z y x ≠ 0) (hx : x ∉ A.aliveD) :
    y ∉ A.aliveD := by
  change A.tpOp k z y x ≠ 0 at h
  simp only [aliveD, Set.mem_setOf_eq, not_not] at hx ⊢
  rcases z with r | r | c
  · by_cases hk : (k : ℕ) < A.slots
    · simp only [tpOp, hk, if_true, restrict_permConj_op_apply] at h
      have hK : (A.cntKraus k).op r (A.tpShift.symm y) x ≠ 0 := fun h' => h (by rw [h', mul_zero])
      have := A.tpShift_ended ((A.cntKraus_op_ne_zero hK).trans hx)
      rwa [Equiv.apply_symm_apply] at this
    · simp only [tpOp, hk, if_false] at h
      exact (A.cntKraus_op_ne_zero h).trans hx
  · by_cases hk : (k : ℕ) < A.slots
    · simp only [tpOp, hk, if_true, restrict_permConj_op_apply] at h
      exfalso
      by_cases hb : A.inBudget (A.endSwap.symm y)
      · exact h (by simp [hb])
      · have hK : (A.cntKraus k).op r (A.endSwap.symm y) x ≠ 0 := fun h' =>
          h (by rw [h', mul_zero])
        exact A.not_inBudget_alive (Bool.of_not_eq_true hb)
          ((A.cntKraus_op_ne_zero hK).trans hx)
    · simp [tpOp, hk] at h
  · simp only [tpOp, Matrix.submatrix_apply, Matrix.kroneckerMap_apply] at h
    rw [Matrix.single_apply] at h
    by_contra hne
    exact h (by rw [if_neg (fun h' => hne h'.1.symm), mul_zero])

/-! ### The compositions with a challenger -/

section Compose

variable (C : Challenger X Y Req Resp)

/-- The composed registers whose adversary branch has not ended. -/
def aliveC : Set (A.toKindAlg.CW C) := {v | v.adv.workspace.2 ≠ A.ended}

instance : DecidablePred (· ∈ ReprogrammedCircuit.workIn (X := X) (Y := Y) (A.aliveC C)) := fun p =>
  inferInstanceAs (Decidable (_ ≠ _))

theorem measReq_op_apply {B : KindAlg X Y Req Resp O} (j : Fin B.slots) (o : Option Req × Unit)
    (y x : QueryReg (B.CW C) 1 X Y) :
    (B.measReq C j).op o y x =
      (if y = B.copyReq C j x then 1 else 0) * (if B.reqOutcome C x = o.1 then 1 else 0) := by
  simp only [KindAlg.measReq, KrausMap.comp, Matrix.mul_apply, KrausMap.ofPerm_op_apply,
    KrausMap.measureFn, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single x]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

variable [Nonempty X] [AddGroup Y]

/-- **The adversary's Kraus maps intertwine** on the branches that have not ended. -/
theorem advKraus_intertwine (k : StepIdx A.slots A.post) (ρ : Matrix (QueryReg (A.toKindAlg.CW C) 1 X Y)
    (QueryReg (A.toKindAlg.CW C) 1 X Y) ℂ) :
    cutTo (ReprogrammedCircuit.workIn (A.aliveC C)) ((A.toTPKindAlg.advKraus C k) ρ) =
      (A.toKindAlg.advKraus C k) (cutTo (ReprogrammedCircuit.workIn (A.aliveC C)) ρ) := by
  exact KrausMap.cutTo_tensorId_reindex_of_absorbing (A.tp_hl k) (A.tp_hr k) (A.tp_habs k)
    (A.toKindAlg.advSplit C) ρ

/-- **The request measurements intertwine**: they keep the counter, and on the branches that have
not ended both read the same kind. -/
theorem measReq_intertwine (j : Fin A.slots) (ρ : Matrix (QueryReg (A.toKindAlg.CW C) 1 X Y)
    (QueryReg (A.toKindAlg.CW C) 1 X Y) ℂ) :
    cutTo (ReprogrammedCircuit.workIn (A.aliveC C)) ((A.toTPKindAlg.measReq C j) ρ) =
      (A.toKindAlg.measReq C j) (cutTo (ReprogrammedCircuit.workIn (A.aliveC C)) ρ) := by
  have hkind : ∀ x : QueryReg (A.toKindAlg.CW C) 1 X Y,
      x ∈ ReprogrammedCircuit.workIn (A.aliveC C) →
        A.toTPKindAlg.kind x.1.adv.workspace = A.toKindAlg.kind x.1.adv.workspace := by
    intro x hx
    change (A.kind _ || decide (_ = A.ended)) = A.kind _
    rw [decide_eq_false hx, Bool.or_false]
  refine (KrausMap.cutTo_apply_of_keeps _ (fun o y x h => ?_) ρ).trans ?_
  rotate_left
  · refine KrausMap.apply_cutTo_congr (fun o => ?_) ρ
    ext y x
    simp only [projOn, Matrix.mul_diagonal]
    split_ifs with hx
    · rw [mul_one, mul_one]
      refine (measReq_op_apply C (B := A.toTPKindAlg) j o y x).trans
        (Eq.trans ?_ (measReq_op_apply C (B := A.toKindAlg) j o y x).symm)
      have hk := hkind x hx
      have hπ : A.toTPKindAlg.copyReq C j x = A.toKindAlg.copyReq C j x := by
        change (if A.toTPKindAlg.kind x.1.adv.workspace then _ else x) =
          (if A.toKindAlg.kind x.1.adv.workspace then _ else x)
        rw [hk]
      have hf : A.toTPKindAlg.reqOutcome C x = A.toKindAlg.reqOutcome C x := by
        change (if A.toTPKindAlg.kind x.1.adv.workspace then _ else none) =
          (if A.toKindAlg.kind x.1.adv.workspace then _ else none)
        rw [hk]
      rw [hπ, hf]
    · rw [mul_zero, mul_zero]
  · rw [show (A.toTPKindAlg.measReq C j).op o y x = _ from
      measReq_op_apply C (B := A.toTPKindAlg) j o y x] at h
    have hy : y = A.toTPKindAlg.copyReq C j x := by
      by_contra hne
      exact h (mul_eq_zero_of_left (if_neg hne) _)
    subst hy
    simp only [KindAlg.copyReq, Function.Involutive.coe_toPerm]
    by_cases hc : (A.kind x.1.adv.workspace.1 || decide (x.1.adv.workspace.2 = A.ended)) = true
    · simp only [hc, ↓reduceIte]
      exact Iff.rfl
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]

open ReprogrammedCircuit in
theorem keepsAll_chalQueries (j : Fin A.slots) :
    KeepsAll (X := X) (Y := Y) (A.aliveC C) (A.toKindAlg.chalQueries C j) := by
  refine KeepsAll.concat fun c hc => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hc
  exact ⟨keeps_ofPerm fun p => Iff.rfl, keeps_ofPerm fun p => Iff.rfl, trivial⟩

open ReprogrammedCircuit in
theorem keepsAll_advQueries (ass : A.toKindAlg.CW C → List (Assignment X Y)) :
    KeepsAll (A.aliveC C) (A.toKindAlg.advQueries C ass) := by
  refine KeepsAll.concat fun c hc => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hc
  exact ⟨keeps_ofPerm fun p => Iff.rfl, keeps_ofPerm fun p => Iff.rfl, trivial⟩

open ReprogrammedCircuit in
theorem keeps_writeReply (j : Fin A.slots) :
    ∀ r i i', (KrausMap.ofPerm (A.toKindAlg.writeReply C j)).op r i i' ≠ 0 →
      (i ∈ workIn (A.aliveC C) ↔ i' ∈ workIn (A.aliveC C)) :=
  keeps_ofPerm fun p => by
    change (if (p.1.chal.logs j).isSome = true then _ else p).1 ∈ _ ↔ _
    split_ifs <;> exact Iff.rfl

open ReprogrammedCircuit in
/-- **A slot of the two compositions intertwines.** -/
theorem intertwined_slotCircBoth (j : Fin A.slots) :
    Intertwined (A.aliveC C) (A.toKindAlg.slotCircBoth C j) (A.toTPKindAlg.slotCircBoth C j) :=
  ⟨fun ρ => A.advKraus_intertwine C (slotStep j) ρ, fun ρ => A.measReq_intertwine C j ρ,
    Intertwined.append (A.keepsAll_chalQueries C j).intertwined
      ⟨fun ρ => (KrausMap.ofPerm (A.toKindAlg.writeReply C j)).cutTo_apply_of_keeps
        (A.keeps_writeReply C j) ρ, (A.keepsAll_advQueries C _).intertwined⟩⟩

open ReprogrammedCircuit in
/-- **A post batch of the two compositions intertwines.** -/
theorem intertwined_postCirc (b : Fin A.post) :
    Intertwined (A.aliveC C) (A.toKindAlg.postCirc C b) (A.toTPKindAlg.postCirc C b) :=
  ⟨fun ρ => A.advKraus_intertwine C (postStep b) ρ, (A.keepsAll_advQueries C _).intertwined⟩

open ReprogrammedCircuit in
/-- **The two compositions with a challenger intertwine** on the branches that have not ended. -/
theorem intertwined_fullCircBoth :
    Intertwined (A.aliveC C) (A.toKindAlg.fullCircBoth C) (A.toTPKindAlg.fullCircBoth C) :=
  Intertwined.append (Intertwined.append
    (Intertwined.concat (List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2
      (List.forall₂_same.2 fun j _ => A.intertwined_slotCircBoth C j))))
    (Intertwined.concat (List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2
      (List.forall₂_same.2 fun b _ => A.intertwined_postCirc C b)))))
    ⟨fun ρ => A.advKraus_intertwine C lastStep ρ, trivial⟩

end Compose

/-! ### The law of the model's composition is dominated by the trace-preserving one -/

section Law

variable (C : Challenger X Y Req Resp) [Nonempty X] [AddGroup Y] [Nonempty Y]

theorem init_mat_eq_zero (a b : A.CReg) (h : a.workspace.2 ≠ 0 ∨ b.workspace.2 ≠ 0) :
    (MState.reindex A.cntSplit.symm (A.init.tensorKet (0 : Fin (A.budget + 2)))).mat a b = 0 := by
  change (A.init.mat ⊗ₖ Matrix.single (0 : Fin (A.budget + 2)) 0 (1 : ℂ)) (A.cntSplit a)
    (A.cntSplit b) = 0
  rw [Matrix.kroneckerMap_apply, Matrix.single_apply, if_neg, mul_zero]
  rintro ⟨h1, h2⟩
  rcases h with h | h
  · exact h h1.symm
  · exact h h2.symm

theorem ended_ne_zero : A.ended ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  simp [ended] at this

/-- The initial state of the composition has counter `0`, so it lies on the branches that have
not ended. -/
theorem cutTo_initSys :
    cutTo (ReprogrammedCircuit.workIn (A.aliveC C)) (A.toTPKindAlg.initSys C).mat =
      (A.toTPKindAlg.initSys C).mat := by
  classical
  ext i j
  simp only [cutTo]
  split_ifs with h
  · rfl
  · symm
    have hz : ∀ a b : A.CReg, (a.workspace.2 = A.ended ∨ b.workspace.2 = A.ended) →
        (MState.reindex A.cntSplit.symm (A.init.tensorKet (0 : Fin (A.budget + 2)))).mat a b = 0 :=
      fun a b hab => A.init_mat_eq_zero a b (hab.imp (fun h => by rw [h]; exact A.ended_ne_zero)
        (fun h => by rw [h]; exact A.ended_ne_zero))
    have hab : i.1.adv.workspace.2 = A.ended ∨ j.1.adv.workspace.2 = A.ended := by
      rw [not_and_or] at h
      exact h.imp not_not.1 not_not.1
    simp only [KindAlg.initSys, MState.mix, MState.reindex, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.submatrix_apply, MState.tensorKet_mat, Matrix.kroneckerMap_apply]
    refine Finset.sum_eq_zero fun ω _ => ?_
    have := hz i.1.adv j.1.adv hab
    simp only [MState.reindex, MState.tensorKet_mat] at this
    simp only [KindAlg.advSplit, Equiv.coe_fn_symm_mk, smul_eq_mul, mul_eq_zero]
    exact Or.inr (Or.inl this)

/-- **The composition of a core algorithm with run-time kinds and a challenger, with an output read
from all composed registers** (as `IAlg.composeOut`): the compiled circuit `fullCircBoth` on the
composed registers with the clean ancilla, the output `f` of the composed registers. -/
noncomputable abbrev _root_.GordieHowe.Quantum.KindAlg.composeBothOut (B : KindAlg X Y Req Resp O)
    {O' : Type} (f : B.CW C → O') : Alg X Y O' :=
  (B.fullCircBoth C).toCircuit.toAlg (MState.withAnc KindAlg.x₀ (B.initSys C)) fun v => f v.1

/-- **The final state of the model's composition is the part of the trace-preserving one on the
branches that have not ended.** -/
theorem final_composeBothOut_apply {O' : Type} (f : A.toKindAlg.CW C → O') (H : X → Y)
    (p : ReprogrammedQueryReg (A.toKindAlg.CW C) X Y) :
    (A.toKindAlg.composeBothOut C f).final H p p =
      if (p.1.1, p.2) ∈ ReprogrammedCircuit.workIn (A.aliveC C) then
        (A.toTPKindAlg.composeBothOut C f).final H p p else 0 := by
  have e₁ : (A.toKindAlg.composeBothOut C f).final H = withAnc KindAlg.x₀
      ((A.toKindAlg.fullCircBoth C).run H (A.toKindAlg.initSys C).mat) := by
    rw [Circuit.toAlg_final]
    exact ReprogrammedCircuit.run_toCircuit H _ _ _
  have e₂ : (A.toTPKindAlg.composeBothOut C f).final H = withAnc KindAlg.x₀
      ((A.toTPKindAlg.fullCircBoth C).run H (A.toTPKindAlg.initSys C).mat) := by
    rw [Circuit.toAlg_final]
    exact ReprogrammedCircuit.run_toCircuit H _ _ _
  rw [e₁, e₂]
  have hrun : (A.toKindAlg.fullCircBoth C).run H (A.toKindAlg.initSys C).mat =
      cutTo (ReprogrammedCircuit.workIn (A.aliveC C))
        ((A.toTPKindAlg.fullCircBoth C).run H (A.toTPKindAlg.initSys C).mat) := by
    rw [(A.intertwined_fullCircBoth C).run H, A.cutTo_initSys C]
    rfl
  simp only [withAnc]
  rw [hrun]
  simp only [cutTo, and_self]
  split_ifs <;> simp

/-- **The model's output law is dominated** by the trace-preserving form's, at every output. -/
theorem outLaw_composeBothOut_le {O' : Type} [DecidableEq O'] (f : A.toKindAlg.CW C → O')
    (H : X → Y) (o : O') :
    (A.toKindAlg.composeBothOut C f).outLaw H (some o) ≤
      (A.toTPKindAlg.composeBothOut C f).outLaw H (some o) := by
  rw [Alg.outLaw, Alg.outLaw]
  refine le_of_eq_of_le (map_basisLaw_apply_some _ _ _ _ o)
    (le_of_le_of_eq ?_ (map_basisLaw_apply_some _ _ _ _ o).symm)
  refine Finset.sum_le_sum fun p _ => ?_
  split_ifs with h
  · rw [A.final_composeBothOut_apply C f H p]
    split_ifs
    · exact le_rfl
    · simp
  · exact le_rfl

/-- **Every event of a terminating run has at most the probability under the trace-preserving
form**: for an event `S` of outcomes whose output is not `none`, the probability under the model's
composition (`H` uniform, read through `e`) is at most the probability under the composition of the
trace-preserving form. -/
theorem realLaw_composeBothOut_le {O' B : Type} [DecidableEq O'] (f : A.toKindAlg.CW C → O')
    (e : Y ≃ B) (S : Set (Outcome (Option O') X B)) (hS : ∀ p ∈ S, p.out ≠ none) :
    ((A.toKindAlg.composeBothOut C f).realLaw e).toOuterMeasure S ≤
      ((A.toTPKindAlg.composeBothOut C f).realLaw e).toOuterMeasure S := by
  rw [Alg.realLaw, Alg.realLaw, PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
  refine ENNReal.tsum_le_tsum fun H => mul_le_mul' le_rfl ?_
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply,
    PMF.toOuterMeasure_apply]
  refine ENNReal.tsum_le_tsum fun o => ?_
  rcases o with _ | o
  · have hn : (none : Option O') ∉ (fun o => (⟨o, e ∘ H⟩ : Outcome (Option O') X B)) ⁻¹' S :=
      fun h => hS _ h rfl
    rw [Set.indicator_of_notMem hn, Set.indicator_of_notMem hn]
  · by_cases hm : some o ∈ (fun o => (⟨o, e ∘ H⟩ : Outcome (Option O') X B)) ⁻¹' S
    · rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm]
      exact A.outLaw_composeBothOut_le C f H o
    · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm]

end Law

end AdaptiveIAlg

/-! ### The composition with run-time kinds is supported on consistent registers -/

namespace KindAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y]
  [Nonempty Y] (A : KindAlg X Y Req Resp O) (C : Challenger X Y Req Resp)

theorem composeBothOut_final {O' : Type} (f : A.CW C → O') (H : X → Y) :
    (A.composeBothOut C f).final H = (A.composeBoth C).final H :=
  rfl

/-- **The final state of the composition with run-time kinds is supported on consistent
registers**. -/
theorem composeBoth_final_apply_eq_zero (H : X → Y) {p : ReprogrammedQueryReg (A.CW C) X Y}
    (hp : ¬ A.Consistent C H p.1.1) : (A.composeBoth C).final H p p = 0 := by
  rw [composeBoth_final]
  simp only [withAnc]
  rw [Matrix.sum_apply, Finset.sum_eq_zero, zero_mul]
  intro c _
  rw [Matrix.smul_apply, embed_apply_of_notMem_left, smul_zero]
  intro r hr
  apply hp
  have h1 := congrArg (fun q => q.1.chal.coins) hr
  have h2 := congrArg (fun q => q.1.chal.queries) hr
  have h3 := congrArg (fun q => q.1.chal.logs) hr
  simp only [KindAlg.emb, KindAlg.advSplit, Equiv.coe_fn_mk] at h1 h2 h3
  simp only [Consistent, ← h1, ← h2, ← h3]

/-- **An output of inconsistent registers has probability `0`.** -/
theorem outLaw_composeBothOut_eq_zero (H : X → Y) {v : A.CW C} (hv : ¬ A.Consistent C H v) :
    (A.composeBothOut C id).outLaw H (some v) = 0 := by
  rw [Alg.outLaw]
  refine (map_basisLaw_apply_some _ _ _ _ v).trans (Finset.sum_eq_zero fun p _ => ?_)
  split_ifs with h
  · have hp : p.1.1 = v := (Option.some_inj.1 h).symm
    rw [composeBothOut_final, A.composeBoth_final_apply_eq_zero C H (hp ▸ hv), Complex.zero_re,
      ENNReal.ofReal_zero]
  · rfl

/-- **Every terminating event of the composition with run-time kinds in the random-oracle model
has the probability of its intersection with consistency**. -/
theorem realLaw_composeBothOut_inter {B : Type} (e : Y ≃ B) (P : A.CW C → (X → B) → Prop) :
    ((A.composeBothOut C id).realLaw e).toOuterMeasure {p | ∃ v, p.out = some v ∧ P v p.oracle} =
      ((A.composeBothOut C id).realLaw e).toOuterMeasure
        {p | ∃ v, p.out = some v ∧ P v p.oracle ∧ A.Consistent C (e.symm ∘ p.oracle) v} := by
  refine le_antisymm ?_ (MeasureTheory.measure_mono fun p ⟨v, hv, hP, _⟩ => ⟨v, hv, hP⟩)
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply]
  refine ENNReal.tsum_le_tsum fun p => ?_
  by_cases hp : p ∈ {p : Outcome (Option (A.CW C)) X B |
      ∃ v, p.out = some v ∧ P v p.oracle ∧ A.Consistent C (e.symm ∘ p.oracle) v}
  · rw [Set.indicator_of_mem hp]
    exact Set.indicator_le_self _ _ _
  · by_cases hS : p ∈ {p : Outcome (Option (A.CW C)) X B | ∃ v, p.out = some v ∧ P v p.oracle}
    · rw [Set.indicator_of_mem hS, Set.indicator_of_notMem hp]
      obtain ⟨v, hv, hPv⟩ := hS
      have hc : ¬ A.Consistent C (e.symm ∘ p.oracle) v := fun hc => hp ⟨v, hv, hPv, hc⟩
      obtain ⟨o, f⟩ := p
      simp only at hv hPv hc
      subst hv
      rw [Alg.realLaw, PMF.bind_apply, tsum_fintype]
      refine le_of_eq (Finset.sum_eq_zero fun H _ => ?_)
      rw [PMF.map_apply, tsum_fintype]
      refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun o' _ => ?_)
      split_ifs with h
      · obtain ⟨rfl, rfl⟩ := Outcome.mk.inj h
        refine A.outLaw_composeBothOut_eq_zero C H fun hv => hc ?_
        simpa [Function.comp_def] using hv
      · rfl
    · rw [Set.indicator_of_notMem hS]
      exact zero_le

end KindAlg

end GordieHowe.Quantum
