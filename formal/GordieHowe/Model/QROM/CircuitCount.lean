-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.QROM.QueryCount
public import GordieHowe.Model.QROM.CircuitClasses
public import GordieHowe.Model.Quantum.Interactive.PureGame
public import GordieHowe.Model.QROM.CoherentBridgeCore

@[expose] public section

/-!
# A per-branch query count for compiled circuits with reprogrammed queries

A circuit with reprogrammed queries (`ReprogrammedCircuit`, `GordieHowe/Model/Quantum/Core/Reprogram.lean`)
compiles into the core by the one-query sub-circuit of `reprogPerm`: on a basis state whose query
input the assignment list assigns, `reprogSwap` exchanges the query pair with the clean ancilla,
whose answer register is in the uniform superposition, so the query to `H` does nothing there. A
query whose assignment list assigns every input on a branch is therefore padded on that branch.
This file turns that into the hypothesis of the measured-database bound with a per-branch count
(`QueryCount`, `GordieHowe/Model/QROM/QueryCount.lean`) for the pure algorithm of the compiled circuit.

## Carrying an invariance through a Kraus map

`KrausMap.Carries K σ σ' S S'`: on inputs in `S` the operators of `K` satisfy
`op r (σ' i') (σ i) = op r i' i` and send `S` into `S'`. Then the Stinespring map of `K` sends a
`σ`-invariant vector on `S` to a `σ'`-invariant vector on `S'`. The property composes along a chain
(`Carries.comp`).

## The frames of the compiled circuit

Before query `k` with assignment list `a`, the clean ancilla has been exchanged by `reprogSwap a`
on the branches where the query input is assigned. The run there is invariant under
`frameShift a c = reprogSwap a ∘ ancShift c ∘ reprogSwap a`, where `ancShift c` adds `c` to the
answer register of the ancilla, and lies on `{p | reprogSwap a p ∈ CleanSupp}`. Every segment of
the compiled circuit carries the frame before it to the frame after it (`carries_seg_toCircuit`):
`reprogSwap` changes the frame, `reprogAdd` and the circuit's own Kraus maps act as the identity
on the ancilla.
-/

open Finset Matrix
open scoped BigOperators

namespace GordieHowe.Quantum

/-! ### Kraus maps that carry an invariance -/

namespace KrausMap

variable {R R₁ R₂ : Type*} {ι : Type} [Fintype R] [Fintype R₁] [Fintype R₂] [Fintype ι]
  [DecidableEq ι]

/-- **A Kraus map carries `(σ, S)` to `(σ', S')`**: on inputs in `S` its operators satisfy
`op r (σ' i') (σ i) = op r i' i` and send `S` into `S'`. Its Stinespring map then sends a
`σ`-invariant vector supported in `S` to a `σ'`-invariant vector supported in `S'`. -/
structure Carries (K : KrausMap R ι ι) (σ σ' : Equiv.Perm ι) (S S' : Set ι) : Prop where
  entry : ∀ r i' i, i ∈ S → K.op r (σ' i') (σ i) = K.op r i' i
  supp : ∀ r i' i, i ∈ S → K.op r i' i ≠ 0 → i' ∈ S'

theorem Carries.comp {K₁ : KrausMap R₁ ι ι} {K₂ : KrausMap R₂ ι ι} {σ τ ρ : Equiv.Perm ι}
    {S T U : Set ι} (h₁ : K₁.Carries σ τ S T) (h₂ : K₂.Carries τ ρ T U) :
    (K₂.comp K₁).Carries σ ρ S U where
  entry r i' i hi := by
    change (K₂.op r.2 * K₁.op r.1) (ρ i') (σ i) = (K₂.op r.2 * K₁.op r.1) i' i
    rw [Matrix.mul_apply, Matrix.mul_apply, ← Equiv.sum_comp τ]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [h₁.entry r.1 m i hi]
    by_cases hm : K₁.op r.1 m i = 0
    · rw [hm, mul_zero, mul_zero]
    · rw [h₂.entry r.2 i' m (h₁.supp r.1 m i hi hm)]
  supp r i' i hi hne := by
    change (K₂.op r.2 * K₁.op r.1) i' i ≠ 0 at hne
    rw [Matrix.mul_apply] at hne
    obtain ⟨m, -, hm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    exact h₂.supp r.2 i' m (h₁.supp r.1 m i hi (right_ne_zero_of_mul hm)) (left_ne_zero_of_mul hm)

theorem carries_identity (σ : Equiv.Perm ι) (S : Set ι) :
    (KrausMap.identity ι).Carries σ σ S S where
  entry _ i' i _ := by
    simp only [KrausMap.identity, Matrix.one_apply, σ.injective.eq_iff]
  supp _ i' i hi hne := by
    simp only [KrausMap.identity, Matrix.one_apply] at hne
    split_ifs at hne with h
    · rwa [h]
    · exact absurd rfl hne

theorem ofPerm_op_apply (π : Equiv.Perm ι) (r : Unit) (i' i : ι) :
    (KrausMap.ofPerm π).op r i' i = if i' = π i then 1 else 0 := by
  simp only [KrausMap.ofPerm, KrausMap.permConj, KrausMap.identity, Matrix.submatrix_apply,
    Equiv.refl_apply, Matrix.one_apply]
  exact if_congr (Equiv.symm_apply_eq π) rfl rfl

/-- A basis permutation carries `(σ, S)` to `(σ', S')` when it intertwines `σ` with `σ'` and maps
`S` into `S'`. -/
theorem carries_ofPerm {π σ σ' : Equiv.Perm ι} {S S' : Set ι} (hint : ∀ i, σ' (π i) = π (σ i))
    (hS : ∀ i ∈ S, π i ∈ S') : (KrausMap.ofPerm π).Carries σ σ' S S' where
  entry r i' i _ := by
    rw [ofPerm_op_apply, ofPerm_op_apply, ← hint]
    exact if_congr σ'.injective.eq_iff rfl rfl
  supp r i' i hi hne := by
    rw [ofPerm_op_apply] at hne
    split_ifs at hne with h
    · rw [h]
      exact hS i hi
    · exact absurd rfl hne

theorem carries_sigmaEmbed {n : ℕ} {G : Fin n → IndexedKrausMap ι} {k : Fin n}
    {σ σ' : Equiv.Perm ι} {S S' : Set ι} (h : (G k).K.Carries σ σ' S S') :
    (KrausMap.sigmaEmbed G k).Carries σ σ' S S' where
  entry p i' i hi := by
    simp only [sigmaEmbed]
    split_ifs with hh
    · exact h.entry _ i' i hi
    · rfl
  supp p i' i hi hne := by
    simp only [sigmaEmbed] at hne
    split_ifs at hne with hh
    · exact h.supp _ i' i hi hne
    · exact absurd rfl hne

end KrausMap

/-! ### The frames of a reprogrammed query -/

section Frames

variable {V X Y : Type} [DecidableEq X] [AddGroup Y]

/-- **The answer register of the reprogramming ancilla shifted by `c`.** -/
def ancShift (c : Y) : Equiv.Perm (ReprogrammedQueryReg V X Y) where
  toFun p := ((p.1.1, (p.1.2.1, p.1.2.2.1 + c, p.1.2.2.2)), p.2)
  invFun p := ((p.1.1, (p.1.2.1, p.1.2.2.1 - c, p.1.2.2.2)), p.2)
  left_inv p := by simp
  right_inv p := by simp

/-- The basis states with a clean ancilla input and flag: input `x₀`, flag `false`. -/
def CleanSupp (x₀ : X) : Set (ReprogrammedQueryReg V X Y) :=
  {p | p.1.2.1 = x₀ ∧ p.1.2.2.2 = false}

variable (ass : V → List (Assignment X Y))

/-- **The frame before a reprogrammed query with assignment list `ass`**: the ancilla shift
conjugated by `reprogSwap ass`. On the branches where the query input is assigned, `reprogSwap`
has moved the ancilla into the query register, and this is the shift of the query answer. -/
def frameShift (c : Y) : Equiv.Perm (ReprogrammedQueryReg V X Y) :=
  (reprogSwap ass).trans ((ancShift c).trans (reprogSwap ass))

/-- The support before a reprogrammed query with assignment list `ass`: the clean basis states
after `reprogSwap ass`. -/
def frameSupp (x₀ : X) : Set (ReprogrammedQueryReg V X Y) :=
  {p | reprogSwap ass p ∈ CleanSupp x₀}

omit [AddGroup Y] in
theorem reprogSwap_reprogSwap (p : ReprogrammedQueryReg V X Y) :
    reprogSwap ass (reprogSwap ass p) = p := by
  conv_lhs => rw [← reprogSwap_symm ass]
  exact Equiv.symm_apply_apply _ p

theorem frameShift_apply (c : Y) (p : ReprogrammedQueryReg V X Y) :
    frameShift ass c p = reprogSwap ass (ancShift c (reprogSwap ass p)) :=
  rfl

end Frames

section FrameCarries

variable {V X Y : Type} [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [AddCommGroup Y] (ass : V → List (Assignment X Y)) (x₀ : X) (c : Y)

/-- **`reprogSwap` before the query carries the clean frame to the frame of the query.** -/
theorem carries_reprogSwap :
    (KrausMap.ofPerm (reprogSwap ass)).Carries (ancShift c) (frameShift ass c) (CleanSupp x₀)
      (frameSupp ass x₀) :=
  KrausMap.carries_ofPerm (fun p => by rw [frameShift_apply, reprogSwap_reprogSwap])
    fun p hp => by
      change reprogSwap ass (reprogSwap ass p) ∈ CleanSupp x₀
      rwa [reprogSwap_reprogSwap]

/-- **`reprogSwap` after the query carries the frame of the query back to the clean frame.** -/
theorem carries_reprogSwap_back :
    (KrausMap.ofPerm (reprogSwap ass)).Carries (frameShift ass c) (ancShift c) (frameSupp ass x₀)
      (CleanSupp x₀) :=
  KrausMap.carries_ofPerm (fun p => by rw [frameShift_apply, reprogSwap_reprogSwap])
    fun _ hp => hp

/-- `reprogAdd` changes only the query answer, so it keeps the clean frame. -/
theorem carries_reprogAdd :
    (KrausMap.ofPerm (reprogAdd ass)).Carries (ancShift c) (ancShift c) (CleanSupp x₀)
      (CleanSupp x₀) :=
  KrausMap.carries_ofPerm (fun p => by
      obtain ⟨⟨v, ax, ay, af⟩, q⟩ := p
      rfl)
    fun _ hp => hp

/-- **A Kraus map of the circuit acts as the identity on the ancilla**, so its lift keeps the clean
frame. -/
theorem carries_liftAnc {R : Type} [Fintype R]
    (K : KrausMap R (QueryReg V 1 X Y) (QueryReg V 1 X Y)) :
    K.liftAnc.Carries (ancShift c) (ancShift c) (CleanSupp x₀) (CleanSupp x₀) where
  entry r i' i _ := by
    obtain ⟨⟨v', ax', ay', af'⟩, q'⟩ := i'
    obtain ⟨⟨v, ax, ay, af⟩, q⟩ := i
    simp only [KrausMap.liftAnc, KrausMap.reindex, KrausMap.tensorId, Matrix.submatrix_apply,
      Equiv.symm_symm, Matrix.kroneckerMap_apply, Matrix.one_apply]
    congr 1
    simp only [ancSplit, ancShift, Equiv.coe_fn_mk, Prod.mk.injEq, add_left_inj]
  supp r i' i hi hne := by
    obtain ⟨⟨v', ax', ay', af'⟩, q'⟩ := i'
    obtain ⟨⟨v, ax, ay, af⟩, q⟩ := i
    simp only [KrausMap.liftAnc, KrausMap.reindex, KrausMap.tensorId, Matrix.submatrix_apply,
      Equiv.symm_symm, Matrix.kroneckerMap_apply, Matrix.one_apply] at hne
    have h2 := right_ne_zero_of_mul hne
    split_ifs at h2 with h
    · simp only [ancSplit, Equiv.coe_fn_mk, Prod.mk.injEq] at h
      obtain ⟨rfl, -, rfl⟩ := h
      exact hi
    · exact absurd rfl h2

end FrameCarries

/-! ### The segments of the compiled circuit carry the frames -/

theorem Circuit.seg_nil {ι : Type} [Fintype ι] [DecidableEq ι] :
    ∀ k, Circuit.seg (Circuit.nil : Circuit ι) k = ⟨Unit, KrausMap.identity ι⟩
  | 0 => rfl
  | k + 1 => Circuit.seg_nil k

namespace ReprogrammedCircuit

variable {V X Y : Type} [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [AddCommGroup Y]

/-- **The frame before query `k`** of the compiled circuit: `frameShift a` for the assignment
list `a` of the `k`-th reprogrammed query, and the ancilla shift after the last one. -/
def frameAt : ReprogrammedCircuit V X Y → ℕ → Y → Equiv.Perm (ReprogrammedQueryReg V X Y)
  | nil, _, cy => ancShift cy
  | kraus _ c, k, cy => frameAt c k cy
  | rquery a _, 0, cy => frameShift a cy
  | rquery _ c, k + 1, cy => frameAt c k cy

/-- **The support before query `k`** of the compiled circuit: `frameSupp a` for the assignment
list `a` of the `k`-th reprogrammed query, and the clean basis states after the last one. -/
def frameSuppAt (x₀ : X) : ReprogrammedCircuit V X Y → ℕ → Set (ReprogrammedQueryReg V X Y)
  | nil, _ => CleanSupp x₀
  | kraus _ c, k => frameSuppAt x₀ c k
  | rquery a _, 0 => frameSupp a x₀
  | rquery _ c, k + 1 => frameSuppAt x₀ c k

/-- The frame at the start of segment `k`: the clean frame for `k = 0`, else the frame before
query `k - 1` (a query keeps it). -/
def frameIn (c : ReprogrammedCircuit V X Y) : ℕ → Y → Equiv.Perm (ReprogrammedQueryReg V X Y)
  | 0, cy => ancShift cy
  | k + 1, cy => frameAt c k cy

/-- The support at the start of segment `k`. -/
def frameSuppIn (x₀ : X) (c : ReprogrammedCircuit V X Y) : ℕ → Set (ReprogrammedQueryReg V X Y)
  | 0 => CleanSupp x₀
  | k + 1 => frameSuppAt x₀ c k

/-- **Every segment of the compiled circuit carries the frame before it to the frame after it**:
segment `k` (the Kraus maps between query `k - 1` and query `k`) carries `(frameIn k, frameSuppIn k)`
to `(frameAt k, frameSuppAt k)`. -/
theorem carries_seg_toCircuit (x₀ : X) (cy : Y) : ∀ (c : ReprogrammedCircuit V X Y) (k : ℕ),
    ((toCircuit c).seg k).K.Carries (c.frameIn k cy) (c.frameAt k cy) (frameSuppIn x₀ c k)
      (frameSuppAt x₀ c k)
  | nil, k => by
    rw [toCircuit, Circuit.seg_nil]
    cases k <;> exact KrausMap.carries_identity _ _
  | kraus K c, 0 => by
    change ((Circuit.head (toCircuit c)).K.comp K.liftAnc).Carries _ _ _ _
    exact (carries_liftAnc x₀ cy K).comp (carries_seg_toCircuit x₀ cy c 0)
  | kraus K c, k + 1 => carries_seg_toCircuit x₀ cy c (k + 1)
  | rquery a c, 0 => by
    change ((KrausMap.identity _).comp (KrausMap.ofPerm (reprogSwap a))).Carries _ _ _ _
    exact (carries_reprogSwap a x₀ cy).comp (KrausMap.carries_identity _ _)
  | rquery a c, 1 => by
    change ((Circuit.head (toCircuit c)).K.comp ((KrausMap.ofPerm (reprogAdd a)).comp
      (KrausMap.ofPerm (reprogSwap a)))).Carries _ _ _ _
    exact ((carries_reprogSwap_back a x₀ cy).comp (carries_reprogAdd a x₀ cy)).comp
      (carries_seg_toCircuit x₀ cy c 0)
  | rquery a c, k + 2 => carries_seg_toCircuit x₀ cy c (k + 1)

end ReprogrammedCircuit

/-! ### The certificate of a circuit and its segments -/

namespace ReprogrammedCircuit

variable {V X Y : Type} [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [AddCommGroup Y]

/-- **A certificate of the per-branch query count of a circuit with reprogrammed queries**, with
record sets `C i` and support sets `G k` of the work register, read with `k` reprogrammed queries
before the circuit, from the support `P` of the work register to `Q`: every Kraus map is trace
preserving, keeps the records `C i` of the earlier queries, and maps the support onward; before the
reprogrammed query `k` the support lies in `G k`, and on `G k` outside `C k` its assignment list
assigns every input (the query is padded there); after it the support is `G k`. -/
def Valid (C G : ℕ → Set V) : ReprogrammedCircuit V X Y → ℕ → Set V → Set V → Prop
  | nil, _, P, Q => P ⊆ Q
  | kraus K c, k, P, Q => (∑ r, (K.op r)ᴴ * K.op r = 1) ∧
      (∀ i < k, ∀ r p' p, K.op r p' p ≠ 0 → (p'.1 ∈ C i ↔ p.1 ∈ C i)) ∧
      ∃ P', (∀ r p' p, p.1 ∈ P → K.op r p' p ≠ 0 → p'.1 ∈ P') ∧ Valid C G c k P' Q
  | rquery a c, k, P, Q => P ⊆ G k ∧ (∀ v ∈ G k, v ∉ C k → ∀ x, (lastAssign (a v) x).isSome) ∧
      Valid C G c (k + 1) (G k) Q

theorem Valid.mono_left {C G : ℕ → Set V} : ∀ {c : ReprogrammedCircuit V X Y} {k : ℕ}
    {P P' Q : Set V}, P' ⊆ P → Valid C G c k P Q → Valid C G c k P' Q
  | nil, _, _, _, _, h, hv => h.trans hv
  | kraus _ _, _, _, _, _, h, ⟨htp, hk, P'', hs, hv⟩ =>
    ⟨htp, hk, P'', fun r p' p hp hne => hs r p' p (h hp) hne, hv⟩
  | rquery _ _, _, _, _, _, h, ⟨hG, hpad, hv⟩ => ⟨h.trans hG, hpad, hv⟩

theorem Valid.append {C G : ℕ → Set V} : ∀ {c d : ReprogrammedCircuit V X Y} {k : ℕ}
    {P Q R : Set V}, Valid C G c k P Q → Valid C G d (k + c.queries) Q R →
      Valid C G (c ++ d) k P R
  | nil, _, _, _, _, _, hc, hd => hd.mono_left hc
  | kraus _ c, _, _, _, _, _, ⟨htp, hk, P', hs, hc⟩, hd =>
    ⟨htp, hk, P', hs, Valid.append (c := c) hc hd⟩
  | rquery _ c, d, k, _, _, _, ⟨hG, hpad, hc⟩, hd => by
    refine ⟨hG, hpad, Valid.append (c := c) hc ?_⟩
    rw [show k + 1 + c.queries = k + (rquery _ c).queries by simp [queries]; omega]
    exact hd

/-- **A segment of the compiled circuit respects the certificate** (proof-internal): it is trace
preserving, keeps the records `C i` for `i < n` and maps the support `P` of the work register into
`P'`. -/
structure SegOK {R : Type*} [Fintype R] (K : KrausMap R (ReprogrammedQueryReg V X Y) (ReprogrammedQueryReg V X Y))
    (C : ℕ → Set V) (n : ℕ) (P P' : Set V) : Prop where
  tp : ∑ r, (K.op r)ᴴ * K.op r = 1
  keeps : ∀ i < n, ∀ r p' p, K.op r p' p ≠ 0 → (p'.1.1 ∈ C i ↔ p.1.1 ∈ C i)
  supp : ∀ r p' p, p.1.1 ∈ P → K.op r p' p ≠ 0 → p'.1.1 ∈ P'

theorem SegOK.comp {R₁ R₂ : Type*} [Fintype R₁] [Fintype R₂]
    {K₁ : KrausMap R₁ (ReprogrammedQueryReg V X Y) (ReprogrammedQueryReg V X Y)}
    {K₂ : KrausMap R₂ (ReprogrammedQueryReg V X Y) (ReprogrammedQueryReg V X Y)}
    {C : ℕ → Set V} {n : ℕ} {P P' P'' : Set V} (h₁ : SegOK K₁ C n P P') (h₂ : SegOK K₂ C n P' P'') :
    SegOK (K₂.comp K₁) C n P P'' where
  tp := (KrausMap.Keeps.comp (F := fun _ : ReprogrammedQueryReg V X Y => ()) ⟨h₂.tp, fun _ _ _ _ => rfl⟩
    ⟨h₁.tp, fun _ _ _ _ => rfl⟩).tp
  keeps i hi r p' p hne := by
    change (K₂.op r.2 * K₁.op r.1) p' p ≠ 0 at hne
    rw [Matrix.mul_apply] at hne
    obtain ⟨m, -, hm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    exact (h₂.keeps i hi r.2 p' m (left_ne_zero_of_mul hm)).trans
      (h₁.keeps i hi r.1 m p (right_ne_zero_of_mul hm))
  supp r p' p hp hne := by
    change (K₂.op r.2 * K₁.op r.1) p' p ≠ 0 at hne
    rw [Matrix.mul_apply] at hne
    obtain ⟨m, -, hm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    exact h₂.supp r.2 p' m (h₁.supp r.1 m p hp (right_ne_zero_of_mul hm)) (left_ne_zero_of_mul hm)

/-- A basis permutation that keeps the work register respects every certificate. -/
theorem segOK_ofPerm {π : Equiv.Perm (ReprogrammedQueryReg V X Y)} (hπ : ∀ p, (π p).1.1 = p.1.1)
    (C : ℕ → Set V) (n : ℕ) {P P' : Set V} (hP : P ⊆ P') : SegOK (KrausMap.ofPerm π) C n P P' where
  tp := (KrausMap.keeps_ofPerm (F := fun _ : ReprogrammedQueryReg V X Y => ()) fun _ => rfl).tp
  keeps i _ r p' p hne := by
    rw [KrausMap.ofPerm_op_apply] at hne
    split_ifs at hne with h
    · rw [h, hπ]
    · exact absurd rfl hne
  supp r p' p hp hne := by
    rw [KrausMap.ofPerm_op_apply] at hne
    split_ifs at hne with h
    · rw [h, hπ]
      exact hP hp
    · exact absurd rfl hne

theorem segOK_identity (C : ℕ → Set V) (n : ℕ) {P P' : Set V} (hP : P ⊆ P') :
    SegOK (KrausMap.identity (ReprogrammedQueryReg V X Y)) C n P P' := by
  have h : KrausMap.identity (ReprogrammedQueryReg V X Y) =
      KrausMap.ofPerm (Equiv.refl _) := by
    simp only [KrausMap.ofPerm, KrausMap.permConj, KrausMap.identity, Equiv.refl_symm,
      Equiv.coe_refl, Matrix.submatrix_id_id]
  rw [h]
  exact segOK_ofPerm (fun _ => rfl) C n hP

theorem segOK_reprogSwap (a : V → List (Assignment X Y)) (C : ℕ → Set V) (n : ℕ) {P P' : Set V}
    (hP : P ⊆ P') : SegOK (KrausMap.ofPerm (reprogSwap a)) C n P P' :=
  segOK_ofPerm (fun p => by rw [reprogSwap_apply]; split_ifs <;> rfl) C n hP

theorem segOK_reprogAdd (a : V → List (Assignment X Y)) (C : ℕ → Set V) (n : ℕ) {P P' : Set V}
    (hP : P ⊆ P') : SegOK (KrausMap.ofPerm (reprogAdd a)) C n P P' :=
  segOK_ofPerm (fun _ => rfl) C n hP

theorem segOK_liftAnc {R : Type} [Fintype R] {K : KrausMap R (QueryReg V 1 X Y) (QueryReg V 1 X Y)}
    {C : ℕ → Set V} {n : ℕ} {P P' : Set V} (htp : ∑ r, (K.op r)ᴴ * K.op r = 1)
    (hk : ∀ i < n, ∀ r p' p, K.op r p' p ≠ 0 → (p'.1 ∈ C i ↔ p.1 ∈ C i))
    (hs : ∀ r p' p, p.1 ∈ P → K.op r p' p ≠ 0 → p'.1 ∈ P') : SegOK K.liftAnc C n P P' where
  tp := (KrausMap.Keeps.reindex (F := fun _ : QueryReg V 1 X Y × (X × Y × Bool) => ())
    (KrausMap.Keeps.tensorId (F := fun _ : QueryReg V 1 X Y => ()) ⟨htp, fun _ _ _ _ => rfl⟩)
    (ancSplit V X Y).symm (F' := fun _ => ()) fun _ => rfl).tp
  keeps i hi r p' p hne := by
    simp only [KrausMap.liftAnc, KrausMap.reindex, KrausMap.tensorId, Matrix.submatrix_apply,
      Equiv.symm_symm, Matrix.kroneckerMap_apply] at hne
    exact hk i hi r _ _ (left_ne_zero_of_mul hne)
  supp r p' p hp hne := by
    simp only [KrausMap.liftAnc, KrausMap.reindex, KrausMap.tensorId, Matrix.submatrix_apply,
      Equiv.symm_symm, Matrix.kroneckerMap_apply] at hne
    exact hs r _ _ hp (left_ne_zero_of_mul hne)

/-- The support after segment `j` of a circuit with `d` reprogrammed queries read from offset `k`:
`G (k + j)` before a query, `Q` after the last. -/
def segOut (G : ℕ → Set V) (Q : Set V) (k d j : ℕ) : Set V :=
  if j < d then G (k + j) else Q

/-- The support before segment `j`: `P` for `j = 0`, else `G (k + j - 1)`. -/
def segIn (G : ℕ → Set V) (P : Set V) (k : ℕ) : ℕ → Set V
  | 0 => P
  | j + 1 => G (k + j)

/-- **Every segment of the compiled circuit respects the certificate.** -/
theorem segOK_seg_toCircuit {C G : ℕ → Set V} : ∀ (c : ReprogrammedCircuit V X Y) {k : ℕ}
    {P Q : Set V}, Valid C G c k P Q → ∀ j ≤ c.queries,
      SegOK ((toCircuit c).seg j).K C (k + j) (segIn G P k j) (segOut G Q k c.queries j)
  | nil, k, P, Q, hv, j, hj => by
    obtain rfl : j = 0 := by simpa [queries] using hj
    rw [toCircuit, Circuit.seg_nil]
    refine segOK_identity C _ ?_
    simp only [segIn, segOut, queries, lt_irrefl, if_false]
    exact hv
  | kraus K c, k, P, Q, ⟨htp, hk, P', hs, hv⟩, 0, _ =>
    (segOK_liftAnc htp hk hs).comp (segOK_seg_toCircuit c hv 0 (Nat.zero_le _))
  | kraus K c, k, P, Q, ⟨_, _, P', _, hv⟩, j + 1, hj =>
    segOK_seg_toCircuit c hv (j + 1) hj
  | rquery a c, k, P, Q, ⟨hG, _, _⟩, 0, _ => by
    refine (segOK_reprogSwap a C _ hG).comp (segOK_identity C _ ?_)
    simp [segOut, queries]
  | rquery a c, k, P, Q, ⟨_, _, hv⟩, 1, hj => by
    have h := segOK_seg_toCircuit c hv 0 (Nat.zero_le _)
    refine ((segOK_reprogSwap a C _ (subset_refl _)).comp (segOK_reprogAdd a C _
      (subset_refl _))).comp ?_
    have e : segOut G Q k (rquery a c).queries 1 = segOut G Q (k + 1) c.queries 0 := by
      simp [segOut, queries]
    rw [e]
    exact h
  | rquery a c, k, P, Q, ⟨_, _, hv⟩, j + 2, hj => by
    have h := segOK_seg_toCircuit c hv (j + 1) (by simp [queries] at hj; omega)
    have e1 : k + 1 + (j + 1) = k + (j + 2) := by omega
    have e2 : segIn G (G k) (k + 1) (j + 1) = segIn G P k (j + 2) := by
      simp only [segIn]
      congr 1
      omega
    have e3 : segOut G Q (k + 1) c.queries (j + 1) = segOut G Q k (rquery a c).queries (j + 2) := by
      show (if j + 1 < c.queries then G (k + 1 + (j + 1)) else Q) =
        (if j + 2 < c.queries + 1 then G (k + (j + 2)) else Q)
      rw [show k + 1 + (j + 1) = k + (j + 2) by omega]
      exact if_congr (by omega) rfl rfl
    rw [e1, e2, e3] at h
    exact h

end ReprogrammedCircuit

/-! ### The Stinespring map carries an invariance -/

section KrausAct

variable {R ι A C : Type*} [Fintype R] [Fintype ι] [Fintype A] [Fintype C] [DecidableEq ι]
  {e : A ≃ R × C} {r₀ : R}

omit [Fintype C] in
/-- **The Stinespring map carries an invariance**: if on inputs in `S` the operators satisfy
`op r (σ' i') (σ i) = op r i' i`, a `σ`-invariant vector supported in `S` (on the system) goes to a
`σ'`-invariant vector. -/
theorem krausAct_invariant (K : KrausChannel R ι ι) {σ σ' : Equiv.Perm ι} {S : Set ι}
    (hK : ∀ r i' i, i ∈ S → K.op r (σ' i') (σ i) = K.op r i' i) {ψ : QState (ι × A)}
    (hS : ∀ i a, i ∉ S → ψ (i, a) = 0) (hσ : ∀ i a, ψ (σ i, a) = ψ (i, a)) (k : ι) (a : A) :
    krausAct e r₀ K ψ (σ' k, a) = krausAct e r₀ K ψ (k, a) := by
  rw [krausAct_apply, krausAct_apply, ← Equiv.sum_comp σ]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hσ]
  by_cases hj : j ∈ S
  · rw [hK _ k j hj]
  · rw [hS j _ hj, mul_zero, mul_zero]

omit [Fintype C] in
/-- The Stinespring map sends a vector supported in `S` (on the system) to one supported in `S'`
when the operators send `S` into `S'`. -/
theorem krausAct_supported (K : KrausChannel R ι ι) {S S' : Set ι}
    (hK : ∀ r i' i, i ∈ S → K.op r i' i ≠ 0 → i' ∈ S') {ψ : QState (ι × A)}
    (hS : ∀ i a, i ∉ S → ψ (i, a) = 0) (k : ι) (a : A) (hk : k ∉ S') :
    krausAct e r₀ K ψ (k, a) = 0 := by
  rw [krausAct_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : j ∈ S
  · by_cases h0 : K.op (e a).1 k j = 0
    · rw [h0, zero_mul]
    · exact absurd (hK _ k j hj h0) hk
  · rw [hS j _ hj, mul_zero]

end KrausAct

/-! ### The halting completion carries an invariance on the running branches -/

namespace KrausMap

variable {R : Type*} {ι : Type} [Fintype R] [Fintype ι] [DecidableEq ι]

/-- The operators of the completion of a trace-preserving Kraus map, on running inputs, carry
what the map's operators carry; halted outputs get no weight. -/
theorem complete_entry {K : KrausMap R ι ι} (htp : ∑ r, (K.op r)ᴴ * K.op r = 1)
    {σ σ' : Equiv.Perm ι} {S S' : Set ι} (h : K.Carries σ σ' S S') :
    ∀ r i' i, i ∈ {p : ι × Bool | p.1 ∈ S ∧ p.2 = false} →
      K.complete.op r ((σ'.prodCongr (Equiv.refl Bool)) i') ((σ.prodCongr (Equiv.refl Bool)) i) =
        K.complete.op r i' i := by
  rintro (r | b) ⟨i', b'⟩ ⟨i, bi⟩ ⟨hi, rfl⟩
  · simp only [complete, completeOp, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply,
      Matrix.kroneckerMap_apply]
    rw [h.entry r i' i hi]
  · cases b
    · simp [complete, completeOp, KrausMap.haltOp_eq_zero htp]
    · simp [complete, completeOp, Matrix.kroneckerMap_apply, Matrix.single_apply]

theorem complete_supp {K : KrausMap R ι ι} (htp : ∑ r, (K.op r)ᴴ * K.op r = 1)
    {σ σ' : Equiv.Perm ι} {S S' : Set ι} (h : K.Carries σ σ' S S') :
    ∀ r i' i, i ∈ {p : ι × Bool | p.1 ∈ S ∧ p.2 = false} → K.complete.op r i' i ≠ 0 →
      i' ∈ {p : ι × Bool | p.1 ∈ S' ∧ p.2 = false} := by
  rintro (r | b) ⟨i', b'⟩ ⟨i, bi⟩ ⟨hi, rfl⟩ hne
  · simp only [complete, completeOp, Matrix.kroneckerMap_apply, Matrix.single_apply] at hne
    split_ifs at hne with hb
    · exact ⟨h.supp r i' i hi fun h0 => hne (by rw [h0, zero_mul]), hb.1.symm⟩
    · exact absurd (mul_zero _) hne
  · cases b
    · simp [complete, completeOp, KrausMap.haltOp_eq_zero htp] at hne
    · simp [complete, completeOp, Matrix.kroneckerMap_apply, Matrix.single_apply] at hne

end KrausMap

/-! ### The frame of a query on its branches -/

section FrameCases

variable {V X Y : Type} [DecidableEq X] [AddGroup Y] (ass : V → List (Assignment X Y))

/-- **The query answer shifted by `c`.** -/
def qShift (c : Y) : Equiv.Perm (ReprogrammedQueryReg V X Y) where
  toFun p := (p.1, fun _ => ((p.2 0).1, (p.2 0).2 + c))
  invFun p := (p.1, fun _ => ((p.2 0).1, (p.2 0).2 - c))
  left_inv p := by
    obtain ⟨w, q⟩ := p
    simp only [Prod.mk.injEq, true_and, add_sub_cancel_right]
    exact funext fun i => by rw [Subsingleton.elim i 0]
  right_inv p := by
    obtain ⟨w, q⟩ := p
    simp only [Prod.mk.injEq, true_and, sub_add_cancel]
    exact funext fun i => by rw [Subsingleton.elim i 0]

omit [DecidableEq X] in
theorem qShift_apply (c : Y) (p : ReprogrammedQueryReg V X Y) :
    qShift c p = (p.1, fun _ => ((p.2 0).1, (p.2 0).2 + c)) :=
  rfl

/-- **On a swapped branch whose ancilla input is assigned, the frame shifts the query answer**: the
ancilla is in the query register there. -/
theorem frameShift_of_swapped (c : Y) {p : ReprogrammedQueryReg V X Y} (hf : p.1.2.2.2 = true)
    (ha : (lastAssign (ass p.1.1) p.1.2.1).isSome) : frameShift ass c p = qShift c p := by
  obtain ⟨⟨v, ax, ay, af⟩, q⟩ := p
  simp only at hf ha
  subst hf
  simp [frameShift_apply, reprogSwap_apply, reprogCond, swapFlip, ancShift, qShift_apply, ha]

/-- **On a branch with flag `false` whose query input is not assigned, the frame shifts the
ancilla answer.** -/
theorem frameShift_of_unassigned (c : Y) {p : ReprogrammedQueryReg V X Y} (hf : p.1.2.2.2 = false)
    (hq : ¬ (lastAssign (ass p.1.1) (p.2 0).1).isSome) : frameShift ass c p = ancShift c p := by
  obtain ⟨⟨v, ax, ay, af⟩, q⟩ := p
  simp only at hf hq
  subst hf
  simp [frameShift_apply, reprogSwap_apply, reprogCond, ancShift, hq]

/-- **Where every input is assigned, the frame shifts the query answer** on both kinds of branch:
the query is padded there. -/
theorem frameShift_of_padded (c : Y) {p : ReprogrammedQueryReg V X Y}
    (hp : ∀ x, (lastAssign (ass p.1.1) x).isSome) : frameShift ass c p = qShift c p := by
  obtain ⟨⟨v, ax, ay, af⟩, q⟩ := p
  cases af
  · simp [frameShift_apply, reprogSwap_apply, reprogCond, swapFlip, ancShift, qShift_apply, hp]
  · exact frameShift_of_swapped ass c rfl (hp _)

/-- The frame keeps the flag. -/
theorem flag_frameShift (c : Y) (p : ReprogrammedQueryReg V X Y) :
    (frameShift ass c p).1.2.2.2 = p.1.2.2.2 := by
  obtain ⟨⟨v, ax, ay, af⟩, q⟩ := p
  cases af <;> by_cases h1 : (lastAssign (ass v) ax).isSome <;>
    by_cases h2 : (lastAssign (ass v) (q 0).1).isSome <;>
    simp [frameShift_apply, reprogSwap_apply, reprogCond, swapFlip, ancShift, h1, h2]

/-- The frame keeps the work register. -/
theorem work_frameShift (c : Y) (p : ReprogrammedQueryReg V X Y) :
    (frameShift ass c p).1.1 = p.1.1 := by
  obtain ⟨⟨v, ax, ay, af⟩, q⟩ := p
  cases af <;> by_cases h1 : (lastAssign (ass v) ax).isSome <;>
    by_cases h2 : (lastAssign (ass v) (q 0).1).isSome <;>
    simp [frameShift_apply, reprogSwap_apply, reprogCond, swapFlip, ancShift, h1, h2]

omit [AddGroup Y] in
/-- **On the support of a frame, a branch with flag `false` has its query input unassigned and the
clean ancilla.** -/
theorem of_mem_frameSupp_of_flag_false {x₀ : X} {p : ReprogrammedQueryReg V X Y}
    (hp : p ∈ frameSupp ass x₀) (hf : p.1.2.2.2 = false) :
    ¬ (lastAssign (ass p.1.1) (p.2 0).1).isSome ∧ p ∈ CleanSupp x₀ := by
  obtain ⟨⟨v, ax, ay, af⟩, q⟩ := p
  simp only at hf
  subst hf
  by_cases h : (lastAssign (ass v) (q 0).1).isSome
  · simp [frameSupp, CleanSupp, reprogSwap_apply, reprogCond, swapFlip, h] at hp
  · refine ⟨h, ?_⟩
    simpa [frameSupp, CleanSupp, reprogSwap_apply, reprogCond, h] using hp

omit [AddGroup Y] in
/-- **On the support of a frame, a branch with flag `true` has its ancilla input assigned.** -/
theorem of_mem_frameSupp_of_flag_true {x₀ : X} {p : ReprogrammedQueryReg V X Y}
    (hp : p ∈ frameSupp ass x₀) (hf : p.1.2.2.2 = true) :
    (lastAssign (ass p.1.1) p.1.2.1).isSome := by
  obtain ⟨⟨v, ax, ay, af⟩, q⟩ := p
  simp only at hf
  subst hf
  by_contra h
  simp [frameSupp, CleanSupp, reprogSwap_apply, reprogCond, h] at hp

/-- The frame at `-c` undoes the frame at `c`. -/
theorem frameShift_neg (c : Y) (p : ReprogrammedQueryReg V X Y) :
    frameShift ass (-c) (frameShift ass c p) = p := by
  rw [frameShift_apply, frameShift_apply, reprogSwap_reprogSwap]
  have : ancShift (-c) (ancShift c (reprogSwap ass p)) = reprogSwap ass p := by
    obtain ⟨⟨v, ax, ay, af⟩, q⟩ := reprogSwap ass p
    simp [ancShift]
  rw [this, reprogSwap_reprogSwap]

omit [AddGroup Y] in
/-- A branch with flag `false`, its query input unassigned and the clean ancilla is on the support
of the frame (`reprogSwap` fixes it). -/
theorem mem_frameSupp_of_unassigned {x₀ : X} {p : ReprogrammedQueryReg V X Y}
    (hf : p.1.2.2.2 = false) (hq : ¬ (lastAssign (ass p.1.1) (p.2 0).1).isSome)
    (hc : p ∈ CleanSupp x₀) : p ∈ frameSupp ass x₀ := by
  obtain ⟨⟨v, ax, ay, af⟩, q⟩ := p
  simp only at hf hq
  subst hf
  simpa [frameSupp, reprogSwap_apply, reprogCond, hq] using hc

/-- The branches with flag `false`, the query input unassigned and the clean ancilla: on them
`reprogSwap` does nothing and the frame is the ancilla shift. -/
def cleanUnassigned (x₀ : X) : Set (ReprogrammedQueryReg V X Y) :=
  {p | p.1.2.2.2 = false ∧ ¬ (lastAssign (ass p.1.1) (p.2 0).1).isSome ∧ p ∈ CleanSupp x₀}

/-- The frame comes back to `cleanUnassigned` only from it. -/
theorem mem_cleanUnassigned_of_frameShift {x₀ : X} (c : Y) {p : ReprogrammedQueryReg V X Y}
    (h : frameShift ass c p ∈ cleanUnassigned ass x₀) : p ∈ cleanUnassigned ass x₀ := by
  have hp : p = ancShift (-c) (frameShift ass c p) := by
    rw [← frameShift_of_unassigned ass (-c) h.1 h.2.1, frameShift_neg]
  rw [hp]
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

end FrameCases

/-! ### The dilation of the compiled circuit carries the frames -/

namespace KrausMap

variable {R : Type*} {ι : Type} [Fintype R] [Fintype ι] [DecidableEq ι]

/-- On running inputs, the operators of the completion of a trace-preserving Kraus map send what
the map's operators send. -/
theorem complete_supp_of {K : KrausMap R ι ι} (htp : ∑ r, (K.op r)ᴴ * K.op r = 1) {S S' : Set ι}
    (hK : ∀ r i' i, i ∈ S → K.op r i' i ≠ 0 → i' ∈ S') :
    ∀ r i' i, i ∈ {p : ι × Bool | p.1 ∈ S ∧ p.2 = false} → K.complete.op r i' i ≠ 0 →
      i' ∈ {p : ι × Bool | p.1 ∈ S' ∧ p.2 = false} :=
  complete_supp htp (σ := Equiv.refl ι) (σ' := Equiv.refl ι)
    ⟨fun _ _ _ _ => rfl, hK⟩

end KrausMap

namespace ReprogrammedCircuit

variable {V X Y O' : Type} [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [AddCommGroup Y] [Nonempty Y]

/-- **The core algorithm of a circuit with reprogrammed queries**: its compilation with the clean
ancilla appended to the initial state `ρ`, the output read by `out`. -/
noncomputable abbrev compiledAlg (c : ReprogrammedCircuit V X Y) (x₀ : X)
    (ρ : MState (QueryReg V 1 X Y)) (out : V × (X × Y × Bool) → O') : Alg X Y O' :=
  (toCircuit c).toAlg (MState.withAnc x₀ ρ) out

/-- **The coherent pure algorithm of the compiled circuit** (`Alg.toQueryAlgCoh`), with its output
read through `g`. -/
noncomputable abbrev compiledQueryAlg {O : Type} (c : ReprogrammedCircuit V X Y) (x₀ : X)
    (ρ : MState (QueryReg V 1 X Y)) (out : V × (X × Y × Bool) → O') (g : Option O' → O) :
    QueryAlg X Y (compiledAlg c x₀ ρ out).depth O :=
  (compiledAlg c x₀ ρ out).toQueryAlgCoh.mapOut g

variable (c : ReprogrammedCircuit V X Y) (x₀ : X) (ρ : MState (QueryReg V 1 X Y))
  (out : V × (X × Y × Bool) → O')

/-- The basis of the halting completion of the compiled algorithm has decidable equality (stated
because instance search does not find it through the compiled algorithm's work register). -/
instance instDecidableEqHaltingReg :
    DecidableEq (QueryReg (compiledAlg c x₀ ρ out).V 1 X Y × Bool) :=
  @instDecidableEqProd _ _ inferInstance inferInstance

theorem segOK_sigmaEmbed {n : ℕ} {G : Fin n → IndexedKrausMap (ReprogrammedQueryReg V X Y)}
    {k : Fin n} {C : ℕ → Set V} {j : ℕ} {P P' : Set V} (h : SegOK (G k).K C j P P') :
    SegOK (KrausMap.sigmaEmbed G k) C j P P' where
  tp := (KrausMap.keeps_sigmaEmbed (F := fun _ : ReprogrammedQueryReg V X Y => ())
    ⟨h.tp, fun _ _ _ _ => rfl⟩).tp
  keeps i hi p p' q hne := by
    simp only [KrausMap.sigmaEmbed] at hne
    split_ifs at hne with hh
    · exact h.keeps i hi _ p' q hne
    · exact absurd rfl hne
  supp p p' q hq hne := by
    simp only [KrausMap.sigmaEmbed] at hne
    split_ifs at hne with hh
    · exact h.supp _ p' q hq hne
    · exact absurd rfl hne

/-- The step of the dilation of the compiled circuit on a vector clean from `k` on is the
Stinespring map of the halting completion of the compiled algorithm's map `k`. -/
theorem dilStep_compiled_eq {k : ℕ} (hk : k ≤ c.queries)
    [Nonempty (QueryReg (V × (X × Y × Bool)) 1 X Y × Bool)]
    {ψ : QState ((QueryReg (V × (X × Y × Bool)) 1 X Y × Bool) ×
      (compiledAlg c x₀ ρ out).HaltAnc)} (hclean : MixedAlg.CleanVec k ψ) :
    ∃ hkd : k < (compiledAlg c x₀ ρ out).depth + 1,
      (compiledAlg c x₀ ρ out).halting.dilStep () k ψ = krausAct (MixedAlg.stepSplit ⟨k, hkd⟩)
        (Classical.arbitrary ((compiledAlg c x₀ ρ out).R ⊕ Bool))
        ((compiledAlg c x₀ ρ out).halting.step () ⟨k, hkd⟩) ψ := by
  have hkd : k < (compiledAlg c x₀ ρ out).depth + 1 := by
    change k < (toCircuit c).queries + 1
    rw [queries_toCircuit]
    omega
  refine ⟨hkd, ?_⟩
  simp only [MixedAlg.dilStep, hkd, dite_true]
  exact stinespring_apply_of_fresh _ (hclean.fresh (k := ⟨k, hkd⟩) le_rfl)

/-- The compiled algorithm's map `k` respects the certificate as segment `k` of the circuit. -/
theorem segOK_step_compiled {C G : ℕ → Set V} {P Q : Set V} (hv : Valid C G c 0 P Q) {k : ℕ}
    (hk : k ≤ c.queries) (hkd : k < (compiledAlg c x₀ ρ out).depth + 1) :
    SegOK ((compiledAlg c x₀ ρ out).step ⟨k, hkd⟩) C k (segIn G P 0 k)
      (segOut G Q 0 c.queries k) := by
  have h := segOK_sigmaEmbed (G := fun j : Fin ((toCircuit c).queries + 1) => (toCircuit c).seg j)
    (k := ⟨k, hkd⟩) (segOK_seg_toCircuit c hv k hk)
  rwa [zero_add] at h

/-- **One step of the dilation of the compiled circuit moves the support of the work register**
(proof-internal): from `segIn` to `segOut`, on running branches, clean from `k` to `k + 1`. -/
theorem dilStep_compiled_supp {C G : ℕ → Set V} {P Q : Set V} (hv : Valid C G c 0 P Q) {k : ℕ}
    (hk : k ≤ c.queries) [Nonempty (QueryReg (V × (X × Y × Bool)) 1 X Y × Bool)]
    {ψ : QState ((QueryReg (V × (X × Y × Bool)) 1 X Y × Bool) ×
      (compiledAlg c x₀ ρ out).HaltAnc)}
    (hclean : MixedAlg.CleanVec k ψ)
    (hS : ∀ i a, ¬ (i.1.1.1 ∈ segIn G P 0 k ∧ i.2 = false) → ψ (i, a) = 0) :
    MixedAlg.CleanVec (k + 1) ((compiledAlg c x₀ ρ out).halting.dilStep () k ψ) ∧
      ∀ i a, ¬ (i.1.1.1 ∈ segOut G Q 0 c.queries k ∧ i.2 = false) →
        (compiledAlg c x₀ ρ out).halting.dilStep () k ψ (i, a) = 0 := by
  set A := compiledAlg c x₀ ρ out
  obtain ⟨hkd, hstep⟩ := dilStep_compiled_eq c x₀ ρ out hk hclean
  have hseg := segOK_step_compiled c x₀ ρ out hv hk hkd
  refine ⟨(A.halting.dilStep_spec () hclean).1, fun i a hi => ?_⟩
  rw [hstep]
  exact krausAct_supported _
    (S := {p : QueryReg A.V 1 X Y × Bool | p.1.1.1 ∈ segIn G P 0 k ∧ p.2 = false})
    (S' := {p : QueryReg A.V 1 X Y × Bool | p.1.1.1 ∈ segOut G Q 0 c.queries k ∧ p.2 = false})
    (KrausMap.complete_supp_of hseg.tp (S := {p | p.1.1 ∈ segIn G P 0 k})
      (S' := {p | p.1.1 ∈ segOut G Q 0 c.queries k}) fun r i' i hi hne => hseg.supp r i' i hi hne)
    (fun i a hi => hS i a hi) i a hi

/-- **One step of the dilation of the compiled circuit keeps the records of the earlier queries**
(proof-internal): a running vector clean from `k` on whose work register lies in `C i` (or
outside it), `i < k`, keeps this. -/
theorem dilStep_compiled_keeps {C G : ℕ → Set V} {P Q : Set V} (hv : Valid C G c 0 P Q) {k i : ℕ}
    (hk : k ≤ c.queries) (hi : i < k) [Nonempty (QueryReg (V × (X × Y × Bool)) 1 X Y × Bool)]
    (T : Set V) (hT : T = C i ∨ T = (C i)ᶜ)
    {ψ : QState ((QueryReg (V × (X × Y × Bool)) 1 X Y × Bool) ×
      (compiledAlg c x₀ ρ out).HaltAnc)}
    (hclean : MixedAlg.CleanVec k ψ)
    (hS : ∀ i a, ¬ (i.1.1.1 ∈ T ∧ i.2 = false) → ψ (i, a) = 0) :
    ∀ i a, ¬ (i.1.1.1 ∈ T ∧ i.2 = false) →
      (compiledAlg c x₀ ρ out).halting.dilStep () k ψ (i, a) = 0 := by
  set A := compiledAlg c x₀ ρ out
  obtain ⟨hkd, hstep⟩ := dilStep_compiled_eq c x₀ ρ out hk hclean
  have hseg := segOK_step_compiled c x₀ ρ out hv hk hkd
  intro i' a hi'
  rw [hstep]
  refine krausAct_supported _
    (S := {p : QueryReg A.V 1 X Y × Bool | p.1.1.1 ∈ T ∧ p.2 = false})
    (S' := {p : QueryReg A.V 1 X Y × Bool | p.1.1.1 ∈ T ∧ p.2 = false})
    (KrausMap.complete_supp_of hseg.tp (S := {p | p.1.1 ∈ T}) (S' := {p | p.1.1 ∈ T})
      fun r j' j hj hne => ?_) (fun i a hi => hS i a hi) i' a hi'
  have hkeep := hseg.keeps i hi r j' j hne
  rcases hT with rfl | rfl
  · exact hkeep.2 hj
  · exact fun h => hj (hkeep.1 h)

/-- **One step of the dilation of the compiled circuit carries the frames** (proof-internal): a
running vector clean from `k` on, supported in the frame before segment `k` and invariant under
it, goes to a vector supported in the frame after it and invariant under that frame. -/
theorem dilStep_compiled_frame {C G : ℕ → Set V} {P Q : Set V} (hv : Valid C G c 0 P Q) {k : ℕ}
    (hk : k ≤ c.queries) [Nonempty (QueryReg (V × (X × Y × Bool)) 1 X Y × Bool)]
    {ψ : QState ((QueryReg (V × (X × Y × Bool)) 1 X Y × Bool) ×
      (compiledAlg c x₀ ρ out).HaltAnc)}
    (hclean : MixedAlg.CleanVec k ψ)
    (hS : ∀ i a, ¬ (i.1 ∈ frameSuppIn x₀ c k ∧ i.2 = false) → ψ (i, a) = 0)
    (hinv : ∀ cy i a, ψ (((c.frameIn k cy) i.1, i.2), a) = ψ (i, a)) :
    (∀ i a, ¬ (i.1 ∈ frameSuppAt x₀ c k ∧ i.2 = false) →
        (compiledAlg c x₀ ρ out).halting.dilStep () k ψ (i, a) = 0) ∧
      ∀ cy i a, (compiledAlg c x₀ ρ out).halting.dilStep () k ψ (((c.frameAt k cy) i.1, i.2), a) =
        (compiledAlg c x₀ ρ out).halting.dilStep () k ψ (i, a) := by
  set A := compiledAlg c x₀ ρ out
  obtain ⟨hkd, hstep⟩ := dilStep_compiled_eq c x₀ ρ out hk hclean
  have hseg := segOK_step_compiled c x₀ ρ out hv hk hkd
  have hcar : ∀ cy, (A.step ⟨k, hkd⟩).Carries (c.frameIn k cy) (c.frameAt k cy)
      (frameSuppIn x₀ c k) (frameSuppAt x₀ c k) := fun cy =>
    KrausMap.carries_sigmaEmbed (G := fun j : Fin ((toCircuit c).queries + 1) => (toCircuit c).seg j)
      (carries_seg_toCircuit x₀ cy c k)
  refine ⟨fun i a hi => ?_, fun cy i a => ?_⟩
  · rw [hstep]
    exact krausAct_supported _
      (S := {p : QueryReg A.V 1 X Y × Bool | p.1 ∈ frameSuppIn x₀ c k ∧ p.2 = false})
      (S' := {p : QueryReg A.V 1 X Y × Bool | p.1 ∈ frameSuppAt x₀ c k ∧ p.2 = false})
      (KrausMap.complete_supp hseg.tp (hcar 0)) (fun i a hi => hS i a hi) i a hi
  · rw [hstep]
    exact krausAct_invariant _ (σ := (c.frameIn k cy).prodCongr (Equiv.refl Bool))
      (σ' := (c.frameAt k cy).prodCongr (Equiv.refl Bool))
      (S := {p | p.1 ∈ frameSuppIn x₀ c k ∧ p.2 = false})
      (KrausMap.complete_entry hseg.tp (hcar cy))
      (fun i a hi => hS i a hi) (fun i a => hinv cy i a) i a

end ReprogrammedCircuit

/-! ### The initial state and the final measurement of the dilation -/

section Purify

variable {ι A : Type*} [Fintype ι] [Fintype A]

/-- **A vector whose reduced density matrix has row `σ i` equal to row `i` has equal entries at
`σ i` and `i`**: `∑_a |ψ(σ i, a) − ψ(i, a)|²` is a combination of the four entries of the reduced
matrix, which cancel. -/
theorem apply_perm_eq_of_reduce {ψ : QState (ι × A)} {σ : Equiv.Perm ι} {i : ι}
    (h : ∀ j, reduce ψ (σ i) j = reduce ψ i j) (a : A) : ψ (σ i, a) = ψ (i, a) := by
  have hsum : ∑ a', (ψ (σ i, a') - ψ (i, a')) * star (ψ (σ i, a') - ψ (i, a')) = 0 := by
    have e : ∑ a', (ψ (σ i, a') - ψ (i, a')) * star (ψ (σ i, a') - ψ (i, a')) =
        reduce ψ (σ i) (σ i) - reduce ψ (σ i) i - (reduce ψ i (σ i) - reduce ψ i i) := by
      simp only [reduce_apply, ← Finset.sum_sub_distrib, star_sub]
      refine Finset.sum_congr rfl fun a' _ => ?_
      ring
    rw [e, h, h]
    ring
  have hre := congrArg Complex.re hsum
  simp only [Complex.re_sum, Complex.zero_re] at hre
  have hterm : ∀ a', 0 ≤ ((ψ (σ i, a') - ψ (i, a')) * star (ψ (σ i, a') - ψ (i, a'))).re :=
    fun a' => by
      rw [RCLike.star_def, Complex.mul_conj, Complex.ofReal_re]
      exact Complex.normSq_nonneg _
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun a' _ => hterm a').1 hre a (Finset.mem_univ _)
  rw [RCLike.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_zero,
    sub_eq_zero] at h0
  exact h0

end Purify

namespace ReprogrammedCircuit

variable {V X Y O' : Type} [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [AddCommGroup Y] [Nonempty Y]
  (c : ReprogrammedCircuit V X Y) (x₀ : X) (ρ : MState (QueryReg V 1 X Y))
  (out : V × (X × Y × Bool) → O')

open Classical in
/-- **The initial state of the dilation of the compiled circuit** is running, has the clean
ancilla, and does not depend on the ancilla's answer register; its work register lies in the
support `P` of `ρ`. -/
theorem dilInit_compiled {P : Set V} (hP : ∀ p, ρ.mat p p ≠ 0 → p.1 ∈ P)
    [Nonempty (QueryReg (V × (X × Y × Bool)) 1 X Y × Bool)] :
    (∀ i a, ¬ (i.2 = false ∧ i.1 ∈ CleanSupp x₀ ∧ i.1.1.1 ∈ P) →
      (compiledAlg c x₀ ρ out).halting.dilInit () (i, a) = 0) ∧
    ∀ cy i a, (compiledAlg c x₀ ρ out).halting.dilInit () (((ancShift cy) i.1, i.2), a) =
      (compiledAlg c x₀ ρ out).halting.dilInit () (i, a) := by
  set A := compiledAlg c x₀ ρ out
  have hmat : ∀ i j : QueryReg A.V 1 X Y × Bool, (A.halting.init ()).mat i j =
      Quantum.withAnc x₀ ρ.mat i.1 j.1 * Matrix.single false false (1 : ℂ) i.2 j.2 := fun i j => rfl
  refine ⟨fun i a hi => ?_, fun cy i a => ?_⟩
  · obtain ⟨p, b⟩ := a
    change purify (A.halting.init ()) (i, p) * _ = 0
    refine mul_eq_zero_of_left (purify_apply_eq_zero _ ?_ p) _
    rw [hmat]
    by_cases hf : i.2 = false
    · refine mul_eq_zero_of_left ?_ _
      simp only [Quantum.withAnc, reprogAnc, ancWeight]
      by_cases hc : i.1 ∈ CleanSupp x₀
      · have hv : ¬ ρ.mat (i.1.1.1, i.1.2) (i.1.1.1, i.1.2) ≠ 0 := fun h =>
          hi ⟨hf, hc, hP _ h⟩
        rw [not_not] at hv
        rw [hv, zero_mul]
      · simp only [CleanSupp, Set.mem_setOf_eq] at hc
        rw [if_neg hc, zero_mul, zero_div, mul_zero]
    · refine mul_eq_zero_of_right _ ?_
      rw [Matrix.single_apply, if_neg (fun h => hf h.1.symm)]
  · obtain ⟨p, b⟩ := a
    change purify (A.halting.init ()) (((ancShift cy) i.1, i.2), p) * _ =
      purify (A.halting.init ()) (i, p) * _
    congr 1
    refine apply_perm_eq_of_reduce (σ := (ancShift cy).prodCongr (Equiv.refl Bool)) (i := i)
      (fun j => ?_) p
    rw [reduce_purify, hmat, hmat]
    obtain ⟨⟨⟨v, ax, ay, af⟩, q⟩, f⟩ := i
    simp only [Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply, Quantum.withAnc, reprogAnc,
      ancWeight, ancShift, Equiv.coe_fn_mk]

end ReprogrammedCircuit

/-! ### The pure algorithm of the compiled circuit -/

namespace Alg

variable {X Y O' O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddGroup Y]
  (A : Alg X Y O') (g : Option O' → O)

/-- **The steps of the coherent pure algorithm of a core algorithm** are the steps of the dilation
of its halting completion without the final measurement, relabelled. -/
theorem stepAt_toQueryAlgCoh_mapOut [Nonempty (QueryReg A.V 1 X Y × Bool)] (k : ℕ)
    (v : QState (QueryReg ((A.V × Bool) × A.HaltAnc) 1 X Y)) :
    ((A.toQueryAlgCoh.mapOut g).toOracleAlg ∅).stepAt () k v =
      relabel (haltRelabel A.V A.HaltAnc X Y) ((A.halting.dilateCoh fun _ => ∅).stepAt () k
        (relabel (haltRelabel A.V A.HaltAnc X Y).symm v)) := by
  by_cases hk : k < A.depth + 1
  · rw [OracleAlg.stepAt_of_lt _ hk, OracleAlg.stepAt_of_lt _ hk]
    simp only [QueryAlg.toOracleAlg, QueryAlg.mapOut, OracleAlg.relabel, relabel_symm]
    rfl
  · simp only [OracleAlg.stepAt, hk, dite_false, LinearIsometryEquiv.coe_refl, id]
    ext r
    simp

omit [AddGroup Y] in
/-- The steps of the dilation without the final measurement: the Stinespring unitary of step
`k`. -/
theorem stepAt_dilateCoh [Nonempty (QueryReg A.V 1 X Y × Bool)] {k : ℕ} (hk : k ≤ A.depth)
    (ψ : QState ((QueryReg A.V 1 X Y × Bool) × A.HaltAnc)) :
    (A.halting.dilateCoh fun _ => ∅).stepAt () k ψ = A.halting.dilStep () k ψ := by
  rw [OracleAlg.stepAt_of_lt _ (Nat.lt_succ_of_le hk)]
  rfl

end Alg

section LiftW

variable {V' H X Y : Type}

/-- **A permutation of a circuit's work register and query pair, on the work register of the pure
algorithm** (with the halting flag and the dilation's ancilla beside it). -/
def liftW (π : Equiv.Perm (QueryReg V' 1 X Y)) : Equiv.Perm (QueryReg ((V' × Bool) × H) 1 X Y) where
  toFun r := ((((π (r.1.1.1, r.2)).1, r.1.1.2), r.1.2), (π (r.1.1.1, r.2)).2)
  invFun r := ((((π.symm (r.1.1.1, r.2)).1, r.1.1.2), r.1.2), (π.symm (r.1.1.1, r.2)).2)
  left_inv r := by simp
  right_inv r := by simp

/-- The circuit's work register and query pair read from the work register of the pure
algorithm. -/
def innerOf (r : QueryReg ((V' × Bool) × H) 1 X Y) : QueryReg V' 1 X Y := (r.1.1.1, r.2)

theorem innerOf_liftW (π : Equiv.Perm (QueryReg V' 1 X Y)) (r : QueryReg ((V' × Bool) × H) 1 X Y) :
    innerOf (liftW π r) = π (innerOf r) :=
  rfl

/-- Two lifts agree at a basis state where the permutations agree on its inner part. -/
theorem liftW_congr {π π' : Equiv.Perm (QueryReg V' 1 X Y)} {r : QueryReg ((V' × Bool) × H) 1 X Y}
    (h : π (innerOf r) = π' (innerOf r)) : liftW π r = liftW π' r := by
  change ((((π (innerOf r)).1, r.1.1.2), r.1.2), (π (innerOf r)).2) =
    ((((π' (innerOf r)).1, r.1.1.2), r.1.2), (π' (innerOf r)).2)
  rw [h]

end LiftW

namespace ReprogrammedCircuit

variable {V X Y O' O : Type} [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [AddCommGroup Y] [Nonempty Y]
  (c : ReprogrammedCircuit V X Y) (x₀ : X) (ρ : MState (QueryReg V 1 X Y))
  (out : V × (X × Y × Bool) → O') (g : Option O' → O)

theorem depth_compiledAlg : (compiledAlg c x₀ ρ out).depth = c.queries :=
  queries_toCircuit c

/-- **A step of the pure algorithm of the compiled circuit moves the support of the work
register** (proof-internal), from `segIn` to `segOut`, on running branches, clean from `k` to
`k + 1` (before the last step). -/
theorem stepAt_compiled_supp [Nonempty (QueryReg (V × (X × Y × Bool)) 1 X Y × Bool)]
    {C G : ℕ → Set V} {P Q : Set V} (hv : Valid C G c 0 P Q) {k : ℕ} (hk : k ≤ c.queries)
    {v : QState (QueryReg (((compiledAlg c x₀ ρ out).V × Bool) × (compiledAlg c x₀ ρ out).HaltAnc)
      1 X Y)}
    (hS : Supported {r | r.1.1.1.1 ∈ segIn G P 0 k ∧ r.1.1.2 = false ∧ MixedAlg.Clean k r.1.2} v) :
    Supported {r | r.1.1.1.1 ∈ segOut G Q 0 c.queries k ∧ r.1.1.2 = false ∧
      (k < c.queries → MixedAlg.Clean (k + 1) r.1.2)}
      ((((compiledAlg c x₀ ρ out).toQueryAlgCoh.mapOut g).toOracleAlg ∅).stepAt () k v) := by
  set A := compiledAlg c x₀ ρ out
  set σ := Alg.haltRelabel A.V A.HaltAnc X Y
  set ψ := relabel σ.symm v
  have hψ : ∀ i a, ψ (i, a) = v (σ (i, a)) := fun i a => rfl
  have hclean : MixedAlg.CleanVec k ψ := fun i a ha => by
    rw [hψ]
    exact hS _ fun h => ha h.2.2
  have hS' : ∀ i a, ¬ (i.1.1.1 ∈ segIn G P 0 k ∧ i.2 = false) → ψ (i, a) = 0 := fun i a hi => by
    rw [hψ]
    exact hS _ fun h => hi ⟨h.1, h.2.1⟩
  obtain ⟨hcl, hsupp⟩ := dilStep_compiled_supp c x₀ ρ out hv hk hclean hS'
  have hkd : k ≤ A.depth := by rw [depth_compiledAlg]; exact hk
  rw [Alg.stepAt_toQueryAlgCoh_mapOut, Alg.stepAt_dilateCoh A hkd]
  intro r hr
  by_cases h1 : r.1.1.1.1 ∈ segOut G Q 0 c.queries k ∧ r.1.1.2 = false
  · have h2 : ¬ MixedAlg.Clean (k + 1) r.1.2 := fun h => hr ⟨h1.1, h1.2, fun _ => h⟩
    exact hcl _ _ h2
  · exact hsupp _ _ h1

/-- **A step of the pure algorithm of the compiled circuit keeps the records of earlier queries**
(proof-internal). -/
theorem stepAt_compiled_keeps [Nonempty (QueryReg (V × (X × Y × Bool)) 1 X Y × Bool)]
    {C G : ℕ → Set V} {P Q : Set V} (hv : Valid C G c 0 P Q) {k i : ℕ} (hk : k ≤ c.queries)
    (hi : i < k) (T : Set V) (hT : T = C i ∨ T = (C i)ᶜ)
    {v : QState (QueryReg (((compiledAlg c x₀ ρ out).V × Bool) × (compiledAlg c x₀ ρ out).HaltAnc)
      1 X Y)}
    (hS : Supported {r | r.1.1.1.1 ∈ T ∧ r.1.1.2 = false ∧ MixedAlg.Clean k r.1.2} v) :
    Supported {r | r.1.1.1.1 ∈ T}
      ((((compiledAlg c x₀ ρ out).toQueryAlgCoh.mapOut g).toOracleAlg ∅).stepAt () k v) := by
  set A := compiledAlg c x₀ ρ out
  set σ := Alg.haltRelabel A.V A.HaltAnc X Y
  set ψ := relabel σ.symm v
  have hψ : ∀ i a, ψ (i, a) = v (σ (i, a)) := fun i a => rfl
  have hclean : MixedAlg.CleanVec k ψ := fun i a ha => by
    rw [hψ]
    exact hS _ fun h => ha h.2.2
  have hS' : ∀ i a, ¬ (i.1.1.1 ∈ T ∧ i.2 = false) → ψ (i, a) = 0 := fun i a hi => by
    rw [hψ]
    exact hS _ fun h => hi ⟨h.1, h.2.1⟩
  have hsupp := dilStep_compiled_keeps c x₀ ρ out hv hk hi T hT hclean hS'
  have hkd : k ≤ A.depth := by rw [depth_compiledAlg]; exact hk
  rw [Alg.stepAt_toQueryAlgCoh_mapOut, Alg.stepAt_dilateCoh A hkd]
  intro r hr
  exact hsupp _ _ fun h => hr h.1

/-- **A step of the pure algorithm of the compiled circuit carries the frames** (proof-internal),
before the last step. -/
theorem stepAt_compiled_frame [Nonempty (QueryReg (V × (X × Y × Bool)) 1 X Y × Bool)]
    {C G : ℕ → Set V} {P Q : Set V} (hv : Valid C G c 0 P Q) {k : ℕ} (hk : k < c.queries)
    {v : QState (QueryReg (((compiledAlg c x₀ ρ out).V × Bool) × (compiledAlg c x₀ ρ out).HaltAnc)
      1 X Y)}
    (hS : Supported {r | innerOf r ∈ frameSuppIn x₀ c k ∧ r.1.1.2 = false ∧
      MixedAlg.Clean k r.1.2} v)
    (hinv : ∀ cy r, v (liftW (V' := (compiledAlg c x₀ ρ out).V)
      (H := (compiledAlg c x₀ ρ out).HaltAnc) (c.frameIn k cy) r) = v r) :
    Supported {r | innerOf r ∈ frameSuppAt x₀ c k}
        ((((compiledAlg c x₀ ρ out).toQueryAlgCoh.mapOut g).toOracleAlg ∅).stepAt () k v) ∧
      ∀ cy r, ((((compiledAlg c x₀ ρ out).toQueryAlgCoh.mapOut g).toOracleAlg ∅).stepAt () k v)
        (liftW (V' := (compiledAlg c x₀ ρ out).V) (H := (compiledAlg c x₀ ρ out).HaltAnc)
          (c.frameAt k cy) r) =
        ((((compiledAlg c x₀ ρ out).toQueryAlgCoh.mapOut g).toOracleAlg ∅).stepAt () k v) r := by
  set A := compiledAlg c x₀ ρ out
  set σ := Alg.haltRelabel A.V A.HaltAnc X Y
  set ψ := relabel σ.symm v
  have hψ : ∀ i a, ψ (i, a) = v (σ (i, a)) := fun i a => rfl
  have hclean : MixedAlg.CleanVec k ψ := fun i a ha => by
    rw [hψ]
    exact hS _ fun h => ha h.2.2
  have hS' : ∀ i a, ¬ (i.1 ∈ frameSuppIn x₀ c k ∧ i.2 = false) → ψ (i, a) = 0 := fun i a hi => by
    rw [hψ]
    exact hS _ fun h => hi ⟨h.1, h.2.1⟩
  have hinv' : ∀ cy i a, ψ (((c.frameIn k cy) i.1, i.2), a) = ψ (i, a) := fun cy i a => by
    rw [hψ, hψ]
    exact hinv cy (σ (i, a))
  obtain ⟨hsupp, hinvout⟩ := dilStep_compiled_frame c x₀ ρ out hv hk.le hclean hS' hinv'
  have hkd : k ≤ A.depth := by rw [depth_compiledAlg]; exact hk.le
  rw [Alg.stepAt_toQueryAlgCoh_mapOut, Alg.stepAt_dilateCoh A hkd]
  refine ⟨fun r hr => ?_, fun cy r => ?_⟩
  · exact hsupp _ _ fun h => hr h.1
  · exact hinvout cy (σ.symm r).1 (σ.symm r).2

end ReprogrammedCircuit

namespace ReprogrammedCircuit

variable {V X Y : Type} [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [AddCommGroup Y]

/-- The assignment list of the `k`-th reprogrammed query (`[]` after the last). -/
def assAt : ReprogrammedCircuit V X Y → ℕ → V → List (Assignment X Y)
  | nil, _ => fun _ => []
  | kraus _ c, k => assAt c k
  | rquery a _, 0 => a
  | rquery _ c, k + 1 => assAt c k

theorem frameAt_eq : ∀ (c : ReprogrammedCircuit V X Y) {k : ℕ}, k < c.queries → ∀ cy : Y,
    c.frameAt k cy = frameShift (c.assAt k) cy
  | nil, k, hk, _ => by simp [queries] at hk
  | kraus _ c, k, hk, cy => frameAt_eq c hk cy
  | rquery _ _, 0, _, _ => rfl
  | rquery _ c, k + 1, hk, cy => frameAt_eq c (by simp [queries] at hk; omega) cy

theorem frameSuppAt_eq (x₀ : X) : ∀ (c : ReprogrammedCircuit V X Y) {k : ℕ}, k < c.queries →
    frameSuppAt x₀ c k = frameSupp (c.assAt k) x₀
  | nil, k, hk => by simp [queries] at hk
  | kraus _ c, k, hk => frameSuppAt_eq x₀ c hk
  | rquery _ _, 0, _ => rfl
  | rquery _ c, k + 1, hk => frameSuppAt_eq x₀ c (by simp [queries] at hk; omega)

/-- **The certificate pads the queries off the records**: on `G (k₀ + k)` outside `C (k₀ + k)`
the assignment list of the `k`-th reprogrammed query assigns every input. -/
theorem Valid.padAt {C G : ℕ → Set V} : ∀ {c : ReprogrammedCircuit V X Y} {k₀ : ℕ} {P Q : Set V},
    Valid C G c k₀ P Q → ∀ k < c.queries, ∀ v ∈ G (k₀ + k), v ∉ C (k₀ + k) →
      ∀ x, (lastAssign (c.assAt k v) x).isSome
  | nil, _, _, _, _, k, hk => by simp [queries] at hk
  | kraus _ c, _, _, _, ⟨_, _, _, _, hv⟩, k, hk => Valid.padAt (c := c) hv k hk
  | rquery _ _, k₀, _, _, ⟨_, hpad, _⟩, 0, _ => hpad
  | rquery _ c, k₀, _, _, ⟨_, _, hv⟩, k + 1, hk => by
    intro v hG hC
    have h := Valid.padAt (c := c) hv k (by simp [queries] at hk; omega)
    rw [show k₀ + 1 + k = k₀ + (k + 1) by omega] at h
    exact h v hG hC

end ReprogrammedCircuit

end GordieHowe.Quantum

namespace GordieHowe.QROM

open GordieHowe.Quantum

variable {m : ℕ} {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {B : Type} (e : BitStr I J ≃ B)

/-! ### Simulated queries and permutations of the work register -/

section SimPerm

variable {W : Type} [Fintype W] [DecidableEq W] {t : ℕ}

/-- An operator whose matrix is invariant under a permutation keeps invariance under it. -/
theorem kernelOp_apply_perm {κ : Type} [Fintype κ] {K : κ → κ → ℂ} {π : Equiv.Perm κ}
    (hK : ∀ i j, K (π i) (π j) = K i j) {v : QState κ} (hv : ∀ i, v (π i) = v i) (i : κ) :
    kernelOp K v (π i) = kernelOp K v i := by
  rw [kernelOp_apply, kernelOp_apply, ← Equiv.sum_comp π]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hK, hv]

/-- A permutation of the work register, on the basis of `Sim*`. -/
def workPerm (τ : Equiv.Perm W) : Equiv.Perm (SimRegister W I J m t) :=
  ((τ.prodCongr (Equiv.refl _))).prodCongr (Equiv.refl _)

theorem workPerm_apply (τ : Equiv.Perm W) (b : SimRegister W I J m t) :
    workPerm (I := I) (J := J) (m := m) (t := t) τ b = ((τ b.1.1, b.1.2), b.2) :=
  rfl

/-- **A simulated query keeps invariance under a permutation of the work register**: the
Hadamard transform, `Dec` and `O0` do not read the work register except through equalities. -/
theorem simQuery_apply_workPerm (τ : Equiv.Perm W) {v : QState (SimRegister W I J m t)}
    (hv : ∀ b, v (workPerm τ b) = v b) (b : SimRegister W I J m t) :
    simQuery e W t v (workPerm τ b) = simQuery e W t v b := by
  classical
  have hH : ∀ w : QState (SimRegister W I J m t), (∀ b, w (workPerm τ b) = w b) →
      ∀ b, hadamard W t w (workPerm τ b) = hadamard W t w b := fun w hw =>
    kernelOp_apply_perm (fun i j => by simp [workPerm_apply, τ.injective.eq_iff]) hw
  have hD : ∀ w : QState (SimRegister W I J m t), (∀ b, w (workPerm τ b) = w b) →
      ∀ b, decOp e W t w (workPerm τ b) = decOp e W t w b := fun w hw => by
    rw [decOp_eq]
    exact kernelOp_apply_perm (fun i j => by
      simp only [workPerm_apply, Prod.mk.injEq, τ.injective.eq_iff]
      exact if_congr Prod.ext_iff.symm rfl rfl) hw
  have hP : ∀ w : QState (SimRegister W I J m t), (∀ b, w (workPerm τ b) = w b) →
      ∀ b, phaseOp e W t w (workPerm τ b) = phaseOp e W t w b := fun w hw =>
    kernelOp_apply_perm (fun i j => by
      simp only [workPerm_apply, Prod.mk.injEq, τ.injective.eq_iff]
      refine if_congr ⟨fun h => Prod.ext (Prod.ext h.1.1 h.1.2) h.2, fun h => ?_⟩ rfl rfl
      subst h
      exact ⟨⟨rfl, rfl⟩, rfl⟩) hw
  simp only [simQuery, compressedOracle, ContinuousLinearMap.comp_apply]
  exact hH _ (hD _ (hP _ (hD _ (hH _ hv)))) b

/-- **A simulated query keeps a support that depends only on the work register and the query
input.** -/
theorem supported_simQuery_of {S : Set (SimRegister W I J m t)}
    (hS : ∀ b' b : SimRegister W I J m t, b'.1.1 = b.1.1 → qIn b'.1 = qIn b.1 → (b' ∈ S ↔ b ∈ S))
    {v : QState (SimRegister W I J m t)} (hv : Supported S v) :
    Supported S (simQuery e W t v) := by
  classical
  have hH : ∀ w : QState (SimRegister W I J m t), Supported S w → Supported S (hadamard W t w) :=
    fun w hw => supported_hadamard_of (fun b' b h1 h2 _ => hS b' b h1 h2) hw
  have hD : ∀ w : QState (SimRegister W I J m t), Supported S w → Supported S (decOp e W t w) :=
    fun w hw => by
      rw [decOp_eq]
      refine hw.kernelOp fun b' b hb hb' => ?_
      rw [if_neg]
      intro h
      exact hb' ((hS b' b (by rw [h]) (by rw [h])).2 hb)
  simp only [simQuery, compressedOracle, ContinuousLinearMap.comp_apply]
  exact hH _ (hD _ (supported_phaseOp_of e (hD _ (hH _ hv))))

end SimPerm

/-! ### Steps controlled on the database register -/

section Controlled

variable {W : Type} [Fintype W] [DecidableEq W] {t : ℕ}

omit [DecidableEq W] in
/-- **A step controlled on the database register keeps what its unitary keeps** on each database
slice: a support of the adversary's registers and invariance under a family of permutations of
them. -/
theorem controlled_transport {ι' : Type}
    {U : QState (QueryReg W 1 (Bits m) (BitStr I J)) ≃ₗᵢ[ℂ] QState (QueryReg W 1 (Bits m) (BitStr I J))}
    {S S' : Set (QueryReg W 1 (Bits m) (BitStr I J))}
    {π π' : ι' → Equiv.Perm (QueryReg W 1 (Bits m) (BitStr I J))}
    (hU : ∀ u, Supported S u → (∀ cy r, u (π cy r) = u r) →
      Supported S' (U u) ∧ ∀ cy r, U u (π' cy r) = U u r)
    {v : QState (SimRegister W I J m t)} (hS : Supported {b | b.1 ∈ S} v)
    (hinv : ∀ cy b, v ((π cy) b.1, b.2) = v b) :
    Supported {b | b.1 ∈ S'} (controlled (fun _ => U) v) ∧
      ∀ cy b, controlled (fun _ => U) v ((π' cy) b.1, b.2) = controlled (fun _ => U) v b := by
  have hslice : ∀ s : Slots I J m t, Supported S (WithLp.toLp 2 fun i => v (i, s)) ∧
      ∀ cy r, (WithLp.toLp 2 fun i => v (i, s) : QState (QueryReg W 1 (Bits m) (BitStr I J)))
        (π cy r) = (WithLp.toLp 2 fun i => v (i, s) : QState _) r :=
    fun s => ⟨fun r hr => hS (r, s) hr, fun cy r => hinv cy (r, s)⟩
  refine ⟨fun b hb => ?_, fun cy b => ?_⟩
  · obtain ⟨r, s⟩ := b
    rw [controlled_apply]
    exact (hU _ (hslice s).1 (hslice s).2).1 r hb
  · obtain ⟨r, s⟩ := b
    rw [controlled_apply, controlled_apply]
    exact (hU _ (hslice s).1 (hslice s).2).2 cy r

omit [DecidableEq W] in
/-- A step controlled on the database register keeps a support of the adversary's registers that
its unitary keeps. -/
theorem supported_controlled_of
    {U : QState (QueryReg W 1 (Bits m) (BitStr I J)) ≃ₗᵢ[ℂ] QState (QueryReg W 1 (Bits m) (BitStr I J))}
    {S S' : Set (QueryReg W 1 (Bits m) (BitStr I J))} (hU : ∀ u, Supported S u → Supported S' (U u))
    {v : QState (SimRegister W I J m t)} (hS : Supported {b | b.1 ∈ S} v) :
    Supported {b | b.1 ∈ S'} (controlled (fun _ => U) v) :=
  (controlled_transport (ι' := Unit) (π := fun _ => Equiv.refl _) (π' := fun _ => Equiv.refl _)
    (fun u hu _ => ⟨hU u hu, fun _ _ => rfl⟩) hS fun _ _ => rfl).1

end Controlled


/-! ### The frame of a query in the simulated run -/

section SimFrame

variable {V O' O : Type} [Fintype V] [DecidableEq V]
  (c : ReprogrammedCircuit V (Bits m) (BitStr I J))
  (x₀ : Bits m) (ρ : MState (QueryReg V 1 (Bits m) (BitStr I J)))
  (out : V × (Bits m × BitStr I J × Bool) → O') (g : Option O' → O) {t : ℕ}

/-- A permutation of the circuit's work register and query pair, on the registers of the pure
algorithm of the compiled circuit. -/
abbrev cLift (π : Equiv.Perm (ReprogrammedQueryReg V (Bits m) (BitStr I J))) :
    Equiv.Perm (QueryReg (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).W 1 (Bits m) (BitStr I J)) :=
  liftW (V' := (ReprogrammedCircuit.compiledAlg c x₀ ρ out).V)
    (H := (ReprogrammedCircuit.compiledAlg c x₀ ρ out).HaltAnc) π

/-- On the pure algorithm's work register, the shift of the query answer is `withAns`. -/
theorem cLift_qShift (cy : BitStr I J)
    (r : QueryReg (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).W 1 (Bits m) (BitStr I J)) :
    cLift c x₀ ρ out g (qShift cy) r = withAns r (qAns r + cy) :=
  rfl

theorem cLift_congr {π π' : Equiv.Perm (ReprogrammedQueryReg V (Bits m) (BitStr I J))}
    {r : QueryReg (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).W 1 (Bits m) (BitStr I J)}
    (h : π (innerOf r) = π' (innerOf r)) : cLift c x₀ ρ out g π r = cLift c x₀ ρ out g π' r :=
  liftW_congr h

/-- The ancilla shift as a permutation of the pure algorithm's work register. -/
def ancShiftW (cy : BitStr I J) : Equiv.Perm (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).W :=
  ((Equiv.prodCongr (Equiv.refl V)
    (Equiv.prodCongr (Equiv.refl (Bits m)) (Equiv.prodCongr (Equiv.addRight cy) (Equiv.refl Bool)))).prodCongr
    (Equiv.refl Bool)).prodCongr (Equiv.refl _)

theorem cLift_ancShift (cy : BitStr I J)
    (b : SimRegister (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).W I J m t) :
    (cLift c x₀ ρ out g (ancShift cy) b.1, b.2) = workPerm (ancShiftW c x₀ ρ out g cy) b :=
  rfl

variable (ass : V → List (Assignment (Bits m) (BitStr I J)))

/-- **The frame of a query, on the simulated run**: supported on the frame's support and invariant
under the frame shifts (on the work register and query pair of the circuit, read through the
pure algorithm's registers). -/
structure SimFrame (v : QState (SimRegister (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).W I J m t)) : Prop where
  supp : Supported {b | innerOf b.1 ∈ frameSupp ass x₀} v
  inv : ∀ cy b, v (cLift c x₀ ρ out g (frameShift ass cy) b.1, b.2) = v b

/-- **A simulated query keeps the frame of the query.** On the branches with the reprogramming
flag set, the query register holds the ancilla and the frame shifts its answer, so the part there
does not depend on the answer register and the query fixes it (`simQuery_eq_self_of_ansConst`).
On the others the query input is unassigned and the ancilla is clean; the frame shifts the
ancilla's answer, which the query does not touch. -/
theorem SimFrame.map_simQuery {v : QState (SimRegister (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).W I J m t)} (hv : SimFrame c x₀ ρ out g ass v) :
    SimFrame c x₀ ρ out g ass (simQuery e (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).W t v) := by
  classical
  set Fs : Set (SimRegister (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).W I J m t) := workSet (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).W t {w | w.1.1.2.2.2 = true}
  set U : Set (SimRegister (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).W I J m t) :=
    {b | innerOf b.1 ∈ cleanUnassigned ass x₀}
  -- the flagged part does not depend on the answer register
  have hA : AnsConst (mask Fs v) := by
    intro b u
    by_cases hb : b ∈ Fs
    · rw [mask_apply_of_mem _ hb, mask_apply_of_mem _ (show (withAns b.1 u, b.2) ∈ Fs from hb)]
      by_cases ha : (lastAssign (ass b.1.1.1.1.1) b.1.1.1.1.2.1).isSome
      · have h := hv.inv (u - qAns b.1) b
        rw [cLift_congr c x₀ ρ out g (frameShift_of_swapped ass _ (p := innerOf b.1) hb ha)] at h
        rwa [cLift_qShift, add_sub_cancel] at h
      · have h1 : v b = 0 := hv.supp b fun h => ha (of_mem_frameSupp_of_flag_true ass h hb)
        have h2 : v (withAns b.1 u, b.2) = 0 := hv.supp _ fun h =>
          ha (of_mem_frameSupp_of_flag_true ass h hb)
        rw [h1, h2]
    · rw [mask_apply_of_notMem _ hb, mask_apply_of_notMem _ (show (withAns b.1 u, b.2) ∉ Fs from hb)]
  -- the unflagged part lies on `U`
  have hU : Supported U (mask Fsᶜ v) := by
    intro b hb
    by_cases hf : b ∈ Fs
    · exact mask_apply_of_notMem _ fun h => h hf
    · rw [mask_apply_of_mem _ hf]
      refine hv.supp b fun hs => hb ?_
      have hf' : (innerOf b.1).1.2.2.2 = false := Bool.eq_false_iff.mpr hf
      obtain ⟨h1, h2⟩ := of_mem_frameSupp_of_flag_false ass hs hf'
      exact ⟨hf', h1, h2⟩
  have hUshift : ∀ cy b, b ∈ U → cLift c x₀ ρ out g (frameShift ass cy) b.1 = cLift c x₀ ρ out g (ancShift cy) b.1 :=
    fun cy b hb => cLift_congr c x₀ ρ out g (frameShift_of_unassigned ass cy (p := innerOf b.1) hb.1 hb.2.1)
  have hUmem : ∀ cy b, (workPerm (ancShiftW c x₀ ρ out g cy) b ∈ U ↔ b ∈ U) := fun cy b => Iff.rfl
  -- the unflagged part is invariant under the ancilla shift
  have hUinv : ∀ cy b, mask Fsᶜ v (workPerm (ancShiftW c x₀ ρ out g cy) b) = mask Fsᶜ v b := by
    intro cy b
    by_cases hb : b ∈ U
    · have hf : b ∉ Fs := fun h => by
        have h1 : (innerOf b.1).1.2.2.2 = false := hb.1
        have h2 : (innerOf b.1).1.2.2.2 = true := h
        rw [h1] at h2
        exact Bool.false_ne_true h2
      rw [mask_apply_of_mem _ (show workPerm (ancShiftW c x₀ ρ out g cy) b ∈ Fsᶜ from hf),
        mask_apply_of_mem _ (show b ∈ Fsᶜ from hf), ← cLift_ancShift, ← hUshift cy b hb]
      exact hv.inv cy b
    · rw [hU b hb, hU _ fun h => hb ((hUmem cy b).1 h)]
  set y := simQuery e (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).W t (mask Fsᶜ v)
  have hyU : Supported U y := supported_simQuery_of e (fun b' b h1 h2 => by
    simp only [U, Set.mem_setOf_eq, innerOf, cleanUnassigned, CleanSupp]
    rw [h1, show (b'.1.2 0).1 = (b.1.2 0).1 from h2]) hU
  have hyinv : ∀ cy b, y (workPerm (ancShiftW c x₀ ρ out g cy) b) = y b :=
    fun cy b => simQuery_apply_workPerm e (ancShiftW c x₀ ρ out g cy) (hUinv cy) b
  have hsplit : simQuery e (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).W t v = mask Fs v + y := by
    conv_lhs => rw [← mask_add_mask_compl Fs v]
    rw [map_add, simQuery_eq_self_of_ansConst e hA]
  rw [hsplit]
  refine ⟨fun b hb => ?_, fun cy b => ?_⟩
  · rw [PiLp.add_apply, (supported_mask_of hv.supp) b hb, zero_add]
    exact hyU b fun h => hb (mem_frameSupp_of_unassigned ass h.1 h.2.1 h.2.2)
  · rw [PiLp.add_apply, PiLp.add_apply]
    congr 1
    · have hflag : (cLift c x₀ ρ out g (frameShift ass cy) b.1, b.2) ∈ Fs ↔ b ∈ Fs :=
        Iff.of_eq (congrArg (· = true) (flag_frameShift ass cy (innerOf b.1)))
      by_cases hb : b ∈ Fs
      · rw [mask_apply_of_mem _ (hflag.2 hb), mask_apply_of_mem _ hb]
        exact hv.inv cy b
      · rw [mask_apply_of_notMem _ (fun h => hb (hflag.1 h)), mask_apply_of_notMem _ hb]
    · by_cases hb : b ∈ U
      · have e1 : ((cLift c x₀ ρ out g (frameShift ass cy) b.1, b.2) :
            SimRegister (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).W I J m t) =
            workPerm (ancShiftW c x₀ ρ out g cy) b := by
          rw [hUshift cy b hb]
          exact cLift_ancShift c x₀ ρ out g cy b
        exact (congrArg y e1).trans (hyinv cy b)
      · have hb' : ((cLift c x₀ ρ out g (frameShift ass cy) b.1, b.2) :
            SimRegister (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).W I J m t) ∉ U :=
          fun h => hb (mem_cleanUnassigned_of_frameShift ass cy h)
        exact (hyU _ hb').trans (hyU b hb).symm

/-- **Off the records the query is padded in the simulated run**: on the branches whose work
register is in `G` but outside the record `C`, every input is assigned, the frame shifts the query
answer, and the part there does not depend on the answer register. -/
theorem SimFrame.pad {v : QState (SimRegister (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).W I J m t)} (hv : SimFrame c x₀ ρ out g ass v)
    {Cs Gs : Set V} (hG : Supported {b | b.1.1.1.1.1 ∈ Gs} v)
    (hpad : ∀ w ∈ Gs, w ∉ Cs → ∀ x, (lastAssign (ass w) x).isSome) :
    simQuery e (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).W t (mask (workSet (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).W t {w | w.1.1.1 ∈ Cs})ᶜ v) =
      mask (workSet (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).W t {w | w.1.1.1 ∈ Cs})ᶜ v := by
  refine simQuery_eq_self_of_ansConst e fun b u => ?_
  by_cases hC : b.1.1.1.1.1 ∈ Cs
  · rw [mask_apply_of_notMem _ (show b ∉ (workSet (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).W t {w | w.1.1.1 ∈ Cs})ᶜ from fun h => h hC),
      mask_apply_of_notMem _ (show (withAns b.1 u, b.2) ∉ (workSet (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).W t {w | w.1.1.1 ∈ Cs})ᶜ from
        fun h => h hC)]
  · rw [mask_apply_of_mem _ (show b ∈ (workSet (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).W t {w | w.1.1.1 ∈ Cs})ᶜ from hC),
      mask_apply_of_mem _ (show (withAns b.1 u, b.2) ∈ (workSet (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).W t {w | w.1.1.1 ∈ Cs})ᶜ from hC)]
    by_cases hGb : b.1.1.1.1.1 ∈ Gs
    · have h := hv.inv (u - qAns b.1) b
      rw [cLift_congr c x₀ ρ out g (frameShift_of_padded ass _ (p := innerOf b.1) (hpad _ hGb hC))] at h
      rwa [cLift_qShift, add_sub_cancel] at h
    · exact (hG (withAns b.1 u, b.2) hGb).trans (hG b hGb).symm

end SimFrame


/-! ### The per-branch count of the pure algorithm of a compiled circuit -/

section Assembly

variable {V O' O : Type} [Fintype V] [DecidableEq V]
  (c : ReprogrammedCircuit V (Bits m) (BitStr I J)) (x₀ : Bits m)
  (ρ : MState (QueryReg V 1 (Bits m) (BitStr I J))) (out : V × (Bits m × BitStr I J × Bool) → O')
  (g : Option O' → O)

theorem segOut_self (G : ℕ → Set V) {d k : ℕ} (hk : k ≤ d) :
    ReprogrammedCircuit.segOut G (G d) 0 d k = G k := by
  unfold ReprogrammedCircuit.segOut
  split_ifs with h
  · rw [zero_add]
  · rw [show k = d by omega]

theorem compiled_nonempty :
    Nonempty (QueryReg (ReprogrammedCircuit.compiledAlg c x₀ ρ out).V 1 (Bits m) (BitStr I J) ×
      Bool) :=
  ⟨(Classical.choice (ReprogrammedCircuit.compiledAlg c x₀ ρ out).init.nonempty, false)⟩

/-- The records of the pure algorithm of the compiled circuit: `C i` read on the circuit's work
register. -/
def compiledC (C : ℕ → Set V) : ℕ → Set (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).W :=
  fun i => {w | w.1.1.1 ∈ C i}

/-- The supports of the pure algorithm of the compiled circuit: `G k` on the circuit's work
register, the run not halted, and the dilation's ancilla clean from `k + 1` on before the last
query. -/
def compiledG (G : ℕ → Set V) : ℕ → Set (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).W :=
  haveI := compiled_nonempty c x₀ ρ out
  fun k => {w | w.1.1.1 ∈ G k ∧ w.1.2 = false ∧ (k < c.queries → MixedAlg.Clean (k + 1) w.2)}

/-- The vectors of the simulated run of the pure algorithm of the compiled circuit before query
`k` with `s` database slots: supported in `compiledG k` and in the frame of the query
(`SimFrame`). -/
def compiledInv (G : ℕ → Set V) (s : ℕ) :
    ℕ → Set (QState (SimRegister (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).W I J m s)) :=
  fun k =>
  if k < c.queries then
    {v | Supported (workSet _ _ (compiledG c x₀ ρ out g G k)) v ∧
      SimFrame c x₀ ρ out g (c.assAt k) v}
  else Set.univ

variable {c x₀ ρ out g}

theorem depth_eq : (ReprogrammedCircuit.compiledAlg c x₀ ρ out).depth = c.queries :=
  ReprogrammedCircuit.depth_compiledAlg c x₀ ρ out

theorem compiled_step0_supp {C G : ℕ → Set V} {P : Set V}
    (hv : ReprogrammedCircuit.Valid C G c 0 P (G c.queries))
    {u : QState (QueryReg (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).W 1 (Bits m)
      (BitStr I J))}
    (hu : haveI := compiled_nonempty c x₀ ρ out
      Supported {r | r.1.1.1.1 ∈ P ∧ r.1.1.2 = false ∧ MixedAlg.Clean 0 r.1.2} u) :
    Supported {r | r.1 ∈ compiledG c x₀ ρ out g G 0}
      (((ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).toOracleAlg ∅).stepAt () 0 u) := by
  have := compiled_nonempty c x₀ ρ out
  have h := ReprogrammedCircuit.stepAt_compiled_supp c x₀ ρ out g hv (k := 0) (Nat.zero_le _)
    (v := u) hu
  refine h.mono fun r hr => ⟨?_, hr.2.1, hr.2.2⟩
  have := hr.1
  rwa [segOut_self G (Nat.zero_le _)] at this

/-- **The initial state of the pure algorithm of the compiled circuit**: on the support `P` of `ρ`
on the work register, running, with the clean reprogramming ancilla and the clean dilation
ancilla, and invariant under the ancilla shift. -/
theorem compiled_init_props {P : Set V} (hP : ∀ p, ρ.mat p p ≠ 0 → p.1 ∈ P) :
    haveI := compiled_nonempty c x₀ ρ out
    Supported {r : QueryReg (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).W 1 (Bits m)
        (BitStr I J) | innerOf r ∈ CleanSupp x₀ ∧ r.1.1.2 = false ∧ MixedAlg.Clean 0 r.1.2 ∧
        r.1.1.1.1 ∈ P} (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).init ∧
      ∀ cy r, (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).init
        (cLift c x₀ ρ out g (ancShift cy) r) = (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).init r := by
  have := compiled_nonempty c x₀ ρ out
  obtain ⟨hIS, hII⟩ := ReprogrammedCircuit.dilInit_compiled c x₀ ρ out hP
  have hIC := (ReprogrammedCircuit.compiledAlg c x₀ ρ out).halting.cleanVec_dilInit ()
  refine ⟨fun r hr => ?_, fun cy r => hII cy ((r.1.1.1, r.2), r.1.1.2) r.1.2⟩
  by_cases hc : MixedAlg.Clean 0 r.1.2
  · exact hIS _ _ fun h' => hr ⟨h'.2.1, h'.1, hc, h'.2.2⟩
  · exact hIC _ _ hc

theorem compiled_init {C G : ℕ → Set V} {P : Set V}
    (hv : ReprogrammedCircuit.Valid C G c 0 P (G c.queries)) (hP : ∀ p, ρ.mat p p ≠ 0 → p.1 ∈ P) :
    Supported {r | r.1 ∈ compiledG c x₀ ρ out g G 0}
      (((ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).toOracleAlg ∅).stepAt () 0
        (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).init) :=
  compiled_step0_supp hv ((compiled_init_props (g := g) hP).1.mono
    fun _ h => ⟨h.2.2.2, h.2.1, h.2.2.1⟩)

theorem compiled_stepG {C G : ℕ → Set V} {P : Set V}
    (hv : ReprogrammedCircuit.Valid C G c 0 P (G c.queries)) {k : ℕ} (hk : k < c.queries)
    {u : QState (QueryReg (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).W 1 (Bits m)
      (BitStr I J))} (hu : Supported {r | r.1 ∈ compiledG c x₀ ρ out g G k} u) :
    Supported {r | r.1 ∈ compiledG c x₀ ρ out g G (k + 1)}
      (((ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).toOracleAlg ∅).stepAt () (k + 1) u) := by
  have := compiled_nonempty c x₀ ρ out
  have h := ReprogrammedCircuit.stepAt_compiled_supp c x₀ ρ out g hv (k := k + 1) (by omega)
    (v := u) (fun r hr => hu r fun h' => hr ⟨by
      show r.1.1.1.1 ∈ G (0 + k)
      rw [zero_add]
      exact h'.1, h'.2.1, h'.2.2 hk⟩)
  refine h.mono fun r hr => ⟨?_, hr.2.1, hr.2.2⟩
  have := hr.1
  rwa [segOut_self G (by omega)] at this

theorem compiled_stepKeeps {C G : ℕ → Set V} {P : Set V}
    (hv : ReprogrammedCircuit.Valid C G c 0 P (G c.queries)) {i k : ℕ} (hik : i ≤ k)
    (hk : k < c.queries) (T : Set V) (hT : T = C i ∨ T = (C i)ᶜ)
    {u : QState (QueryReg (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).W 1 (Bits m)
      (BitStr I J))} (hu : Supported {r | r.1.1.1.1 ∈ T ∧ r.1 ∈ compiledG c x₀ ρ out g G k} u) :
    Supported {r | r.1.1.1.1 ∈ T}
      (((ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).toOracleAlg ∅).stepAt () (k + 1) u) := by
  have := compiled_nonempty c x₀ ρ out
  exact ReprogrammedCircuit.stepAt_compiled_keeps c x₀ ρ out g hv (k := k + 1) (i := i) (by omega)
    (by omega) T hT (v := u) (fun r hr => hu r fun h' => hr ⟨h'.1, h'.2.2.1, h'.2.2.2 hk⟩)

theorem compiled_count {G C : ℕ → Set V} {b : ℕ}
    (hcount : ∀ k ≤ c.queries, ∀ w ∈ G k, countBelow C (min (k + 1) c.queries) w ≤ b) :
    ∀ k ≤ (ReprogrammedCircuit.compiledAlg c x₀ ρ out).depth,
      ∀ w ∈ compiledG c x₀ ρ out g G k,
        countBelow (compiledC c x₀ ρ out g C)
          (min (k + 1) (ReprogrammedCircuit.compiledAlg c x₀ ρ out).depth) w ≤ b := by
  intro k hk w hw
  have e : min (k + 1) (ReprogrammedCircuit.compiledAlg c x₀ ρ out).depth =
      min (k + 1) c.queries := by rw [depth_eq]
  rw [e]
  exact hcount k (by rw [← depth_eq (x₀ := x₀) (ρ := ρ) (out := out)]; exact hk) w.1.1.1 hw.1

theorem compiled_inv_dbProj {G : ℕ → Set V} (s k : ℕ) (Pd : Set (DB (Bits m) B))
    (v : QState (SimRegister (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).W I J m s))
    (hv : v ∈ compiledInv c x₀ ρ out g G s k) :
    dbProj e _ _ Pd v ∈ compiledInv c x₀ ρ out g G s k := by
  unfold compiledInv at hv ⊢
  split_ifs at hv ⊢ with hk
  · obtain ⟨hG, hF⟩ := hv
    refine ⟨Supported.dbProj e hG Pd, Supported.dbProj e hF.supp Pd, fun cy b => ?_⟩
    rw [dbProj_eq, mask_apply, mask_apply]
    by_cases hb : InP e _ Pd b.2
    · simp only [Set.indicator, dbSet, Set.mem_setOf_eq, hb, if_true]
      exact hF.inv cy b
    · simp only [Set.indicator, dbSet, Set.mem_setOf_eq, hb, if_false]
  · trivial

theorem compiled_pad {C G : ℕ → Set V} {P Q : Set V} (hv : ReprogrammedCircuit.Valid C G c 0 P Q)
    (s : ℕ) {k : ℕ} (hk : k < (ReprogrammedCircuit.compiledAlg c x₀ ρ out).depth)
    {v : QState (SimRegister (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).W I J m s)}
    (hvI : v ∈ compiledInv c x₀ ρ out g G s k) :
    simQuery e _ _ (mask (workSet _ _ (compiledC c x₀ ρ out g C k))ᶜ v) =
      mask (workSet _ _ (compiledC c x₀ ρ out g C k))ᶜ v := by
  rw [depth_eq] at hk
  unfold compiledInv at hvI
  rw [if_pos hk] at hvI
  obtain ⟨hG, hF⟩ := hvI
  have hG' : Supported {b : SimRegister (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).W I J m
      s | b.1.1.1.1.1 ∈ G k} v :=
    fun b hb => hG b fun h => hb h.1
  refine SimFrame.pad e c x₀ ρ out g (c.assAt k) hF (Cs := C k) (Gs := G k) hG' fun w hw hC => ?_
  have h := hv.padAt k hk w (by rwa [zero_add]) (by rwa [zero_add])
  exact h

theorem compiled_inv_init {C G : ℕ → Set V} {P : Set V}
    (hv : ReprogrammedCircuit.Valid C G c 0 P (G c.queries)) (hP : ∀ p, ρ.mat p p ≠ 0 → p.1 ∈ P)
    (s : ℕ) :
    simStepS (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g) s 0
      (simInitS e (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g) s) ∈
      compiledInv c x₀ ρ out g G s 0 := by
  have := compiled_nonempty c x₀ ρ out
  unfold compiledInv
  split_ifs with h0
  swap
  · trivial
  obtain ⟨hIS, hII⟩ := compiled_init_props (g := g) hP
  set S0 : Set (QueryReg (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).W 1 (Bits m) (BitStr I J)) := {r | innerOf r ∈ CleanSupp x₀ ∧
    r.1.1.2 = false ∧ MixedAlg.Clean 0 r.1.2 ∧ r.1.1.1.1 ∈ P}
  have hsimS : Supported {b : SimRegister (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).W I J m s | b.1 ∈ S0}
      (simInitS e (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g) s) := fun b hb => by
    simp only [simInitS]
    rw [hIS b.1 hb, zero_mul]
  have hsimI : ∀ cy (b : SimRegister (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).W I J m s),
      simInitS e (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g) s (cLift c x₀ ρ out g (ancShift cy) b.1, b.2) =
        simInitS e (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g) s b := fun cy b => by
    simp only [simInitS]
    change (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).init (cLift c x₀ ρ out g (ancShift cy) b.1) * _ = (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).init b.1 * _
    rw [hII cy b.1]
  refine ⟨supported_controlled_of (S := S0) (fun u hu => compiled_step0_supp hv
    (hu.mono fun _ h => ⟨h.2.2.2, h.2.1, h.2.2.1⟩)) hsimS, ?_⟩
  obtain ⟨hF1, hF2⟩ := controlled_transport (ι' := BitStr I J) (S := S0)
    (π := fun cy => cLift c x₀ ρ out g (ancShift cy))
    (S' := {r | innerOf r ∈ frameSupp (c.assAt 0) x₀})
    (π' := fun cy => cLift c x₀ ρ out g (frameShift (c.assAt 0) cy))
    (U := ((ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).toOracleAlg ∅).stepAt () 0) (fun u hu hinv => by
      have h := ReprogrammedCircuit.stepAt_compiled_frame c x₀ ρ out g hv (k := 0) h0 (v := u)
        (hu.mono fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩) hinv
      rw [ReprogrammedCircuit.frameSuppAt_eq x₀ c h0] at h
      refine ⟨h.1, fun cy r => ?_⟩
      have := h.2 cy r
      rwa [ReprogrammedCircuit.frameAt_eq c h0] at this) hsimS hsimI
  exact ⟨hF1, hF2⟩

theorem compiled_inv_step {C G : ℕ → Set V} {P : Set V}
    (hv : ReprogrammedCircuit.Valid C G c 0 P (G c.queries)) (s : ℕ) {k : ℕ}
    (hk : k < (ReprogrammedCircuit.compiledAlg c x₀ ρ out).depth)
    {v : QState (SimRegister (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).W I J m s)}
    (hvI : v ∈ compiledInv c x₀ ρ out g G s k) :
    simStepS (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g) s (k + 1)
      (simQuery e _ _ v) ∈ compiledInv c x₀ ρ out g G s (k + 1) := by
  have := compiled_nonempty c x₀ ρ out
  have hk' : k < c.queries := by rw [← depth_eq (x₀ := x₀) (ρ := ρ) (out := out)]; exact hk
  unfold compiledInv at hvI
  rw [if_pos hk'] at hvI
  obtain ⟨hG, hF⟩ := hvI
  have hG' := supported_simQuery_workSet e hG
  have hF' := hF.map_simQuery e
  unfold compiledInv
  split_ifs with hk1
  swap
  · trivial
  refine ⟨supported_controlled_of (S := {r | r.1 ∈ compiledG c x₀ ρ out g G k})
    (fun u hu => compiled_stepG hv hk' hu) hG', ?_⟩
  set S : Set (QueryReg (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).W 1 (Bits m) (BitStr I J)) :=
    {r | innerOf r ∈ frameSupp (c.assAt k) x₀ ∧ r.1 ∈ compiledG c x₀ ρ out g G k}
  have hS : Supported {b : SimRegister (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).W I J m
      s | b.1 ∈ S}
      (simQuery e (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).W s v) := fun b hb => by
    by_cases h1 : innerOf b.1 ∈ frameSupp (c.assAt k) x₀
    · have h2 : b.1.1 ∉ compiledG c x₀ ρ out g G k := fun h => hb ⟨h1, h⟩
      exact hG' b h2
    · exact hF'.supp b h1
  obtain ⟨hF1, hF2⟩ := controlled_transport (ι' := BitStr I J) (S := S)
    (π := fun cy => cLift c x₀ ρ out g (frameShift (c.assAt k) cy))
    (S' := {r | innerOf r ∈ frameSupp (c.assAt (k + 1)) x₀})
    (π' := fun cy => cLift c x₀ ρ out g (frameShift (c.assAt (k + 1)) cy))
    (U := ((ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).toOracleAlg ∅).stepAt () (k + 1)) (fun u hu hinv => by
      have hinv' : ∀ cy r, u (liftW (V' := (ReprogrammedCircuit.compiledAlg c x₀ ρ out).V)
          (H := (ReprogrammedCircuit.compiledAlg c x₀ ρ out).HaltAnc) (c.frameIn (k + 1) cy) r) =
          u r := fun cy r => by
        change u (cLift c x₀ ρ out g (c.frameAt k cy) r) = u r
        rw [ReprogrammedCircuit.frameAt_eq c hk']
        exact hinv cy r
      have h := ReprogrammedCircuit.stepAt_compiled_frame c x₀ ρ out g hv (k := k + 1) hk1
        (v := u) (fun r hr => hu r fun h' => hr ⟨by
          change innerOf r ∈ ReprogrammedCircuit.frameSuppAt x₀ c k
          rw [ReprogrammedCircuit.frameSuppAt_eq x₀ c hk']
          exact h'.1, h'.2.2.1, h'.2.2.2 hk'⟩) hinv'
      rw [ReprogrammedCircuit.frameSuppAt_eq x₀ c hk1] at h
      refine ⟨h.1, fun cy r => ?_⟩
      have := h.2 cy r
      rwa [ReprogrammedCircuit.frameAt_eq c hk1] at this) hS hF'.inv
  exact ⟨hF1, hF2⟩

variable (c x₀ ρ out g)

/-- **A certificate of a circuit with reprogrammed queries gives a per-branch count of the queries
of its pure algorithm** (`QueryCount`). The records `C`, read on the circuit's work register, are
kept by the dilated steps (`compiled_stepKeeps`); on the supports `G` at most `b` queries are
recorded (`compiled_count`); off the records the queries are padded: the assignment lists assign
every input there (`Valid.padAt`), so the compiled sub-circuit queries the clean ancilla, which the
simulated query fixes (`compiled_pad`, `SimFrame.pad`). The frames of the compiled circuit
(`frameShift`) carry this through the dilation and the simulated queries (`compiled_inv_step`). -/
noncomputable def compiledQueryCount {C G : ℕ → Set V} {P : Set V} {b : ℕ}
    (hv : ReprogrammedCircuit.Valid C G c 0 P (G c.queries))
    (hP : ∀ p, ρ.mat p p ≠ 0 → p.1 ∈ P)
    (hcount : ∀ k ≤ c.queries, ∀ w ∈ G k, countBelow C (min (k + 1) c.queries) w ≤ b) :
    QueryCount e (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g) b where
  C := compiledC c x₀ ρ out g C
  G := compiledG c x₀ ρ out g G
  Inv := compiledInv c x₀ ρ out g G
  init := compiled_init hv hP
  stepG k hk _ hu := compiled_stepG hv (by rwa [depth_eq] at hk) hu
  stepC i k hik hk _ hu := compiled_stepKeeps hv hik (by rwa [depth_eq] at hk) (C i) (Or.inl rfl) hu
  stepCc i k hik hk _ hu := compiled_stepKeeps hv hik (by rwa [depth_eq] at hk) (C i)ᶜ (Or.inr rfl) hu
  count := compiled_count hcount
  inv_init := compiled_inv_init e hv hP
  inv_step s k hk _ hvI := compiled_inv_step e hv s hk hvI
  inv_dbProj s k Pd v hvI := compiled_inv_dbProj e s k Pd v hvI
  pad s k hk _ hvI := compiled_pad e hv s hk hvI

end Assembly

end GordieHowe.QROM
