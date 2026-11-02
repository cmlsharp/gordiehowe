-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.BaseShift
public import GordieHowe.Model.Quantum.Interactive.CircuitTwin

@[expose] public section

/-!
# Local queries carried through the composition's compiled circuit

Tools for relating the compiled circuit of a composition whose adversary's Kraus maps are followed
by additions (`RegAdd`) to the compiled circuit of the adversary without them.

- `OpInv σ K`: the operators of `K` are invariant under the basis permutation `σ`;
  `OpInv.chRel`, `OpInv.comp`, `opInv_ofPerm`, `opInv_measureFn`.
- `liftQ`: a permutation of the registers on the registers with the reprogramming ancilla;
  `OpInv.liftAnc`, `KrausMap.LeftPerm.liftAnc`, `liftAnc_ofPerm_apply`.
- `KindAlg.BaseQ`, `carry`, `carry_congr`: the pending local queries on the composed registers.
- `flagF`, `condSet`, `wxDep_condSet`, `keeps_liftAnc_flagF`, `keeps_reprogSwap_flagF`,
  `keeps_reprogTail`, `twin_concat_of`, `twin_concat_finRange`, `twin_rc_append`: the supports and
  the twin circuits of concatenations, for the walk of the pending additions
  (`KindShape.AddsAt.twin_fullCircBoth`).
-/

open Matrix
open scoped BigOperators Kronecker

namespace GordieHowe.Quantum

open GordieHowe.QROM

/-! ### Kraus maps invariant under a permutation -/

section OpInv

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The operators of `K` are invariant under `σ`**: `K.op r (σ a) (σ b) = K.op r a b`. -/
def OpInv {R : Type} [Fintype R] (σ : Equiv.Perm ι) (K : KrausMap R ι ι) : Prop :=
  ∀ r a b, K.op r (σ a) (σ b) = K.op r a b

variable {R R₁ R₂ : Type} [Fintype R] [Fintype R₁] [Fintype R₂] {σ : Equiv.Perm ι}

/-- **A Kraus map invariant under `σ` commutes with relabelling by `σ`.** -/
theorem OpInv.chRel {K : KrausMap R ι ι} (h : OpInv σ K) (S : Set ι) : ChRel σ σ S K K :=
  fun ρ hρ => KrausMapRelabel.apply_submatrix_of_op K K σ S (fun r a b _ => h r a b) ρ hρ

theorem OpInv.comp {K₂ : KrausMap R₂ ι ι} {K₁ : KrausMap R₁ ι ι} (h₂ : OpInv σ K₂)
    (h₁ : OpInv σ K₁) : OpInv σ (K₂.comp K₁) := fun r a b => by
  show ∑ c, K₂.op r.2 (σ a) c * K₁.op r.1 c (σ b) = ∑ c, K₂.op r.2 a c * K₁.op r.1 c b
  rw [← Equiv.sum_comp σ]
  simp only [h₂ r.2, h₁ r.1]

/-- A basis permutation that commutes with `σ` is invariant under it. -/
theorem opInv_ofPerm {π : Equiv.Perm ι} (h : ∀ a, π (σ a) = σ (π a)) :
    OpInv σ (KrausMap.ofPerm π) := fun r a b => by
  rw [KrausMap.LeftPerm.ofPerm_op_apply, KrausMap.LeftPerm.ofPerm_op_apply, h b]
  simp only [σ.injective.eq_iff]

/-- The measurement of a function that `σ` keeps is invariant under it. -/
theorem opInv_measureFn {M : Type} [Fintype M] [DecidableEq M] {f : ι → M}
    (hf : ∀ a, f (σ a) = f a) : OpInv σ (KrausMap.measureFn f) := fun r a b => by
  simp only [KrausMap.measureFn, Matrix.diagonal_apply, σ.injective.eq_iff, hf]

end OpInv

/-! ### Basis permutations related by carried permutations -/

section OfPerm₂

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Two basis permutations related by carried permutations**: `ofPerm π'` read after `σ` is
`ofPerm π` followed by `σ'` on `S` when `π' ∘ σ = σ' ∘ π` on `S`. -/
theorem chRel_ofPerm₂ {π' π σ' σ : Equiv.Perm ι} {S : Set ι}
    (h : ∀ a ∈ S, π' (σ a) = σ' (π a)) :
    ChRel σ' σ S (KrausMap.ofPerm π') (KrausMap.ofPerm π) := fun ρ hρ => by
  have key : ∀ x, (σ.symm (π'.symm x) ∈ S ∨ π.symm (σ'.symm x) ∈ S) →
      σ.symm (π'.symm x) = π.symm (σ'.symm x) := by
    rintro x (h1 | h1)
    · have e := h _ h1
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at e
      rw [Equiv.eq_symm_apply, Equiv.eq_symm_apply, ← e]
    · have e := h _ h1
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at e
      rw [Equiv.symm_apply_eq, Equiv.symm_apply_eq, e]
  rw [KrausMap.ofPerm_apply, KrausMap.ofPerm_apply]
  ext x y
  simp only [Matrix.submatrix_apply]
  by_cases hl : ρ (σ.symm (π'.symm x)) (σ.symm (π'.symm y)) = 0
  · by_cases hr : ρ (π.symm (σ'.symm x)) (π.symm (σ'.symm y)) = 0
    · rw [hl, hr]
    · obtain ⟨ha, hb⟩ := hρ _ _ hr
      rw [key x (Or.inr ha), key y (Or.inr hb)]
  · obtain ⟨ha, hb⟩ := hρ _ _ hl
    rw [key x (Or.inl ha), key y (Or.inl hb)]

end OfPerm₂

/-! ### Permutations on the registers with the reprogramming ancilla -/

section LiftQ

variable {V X Y : Type} [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y]

/-- **A permutation of `QueryReg V 1 X Y` with the identity on the reprogramming ancilla.** -/
def liftQ (σ : Equiv.Perm (QueryReg V 1 X Y)) : Equiv.Perm (ReprogrammedQueryReg V X Y) :=
  (ancSplit V X Y).symm.permCongr (σ.prodCongr (Equiv.refl _))

theorem liftQ_apply (σ : Equiv.Perm (QueryReg V 1 X Y)) (p : ReprogrammedQueryReg V X Y) :
    liftQ σ p = (ancSplit V X Y).symm (σ (ancSplit V X Y p).1, (ancSplit V X Y p).2) :=
  rfl

variable {R : Type} [Fintype R]

theorem OpInv.liftAnc {σ : Equiv.Perm (QueryReg V 1 X Y)}
    {K : KrausMap R (QueryReg V 1 X Y) (QueryReg V 1 X Y)} (h : OpInv σ K) :
    OpInv (liftQ σ) K.liftAnc := fun r a b => by
  change (K.op r ⊗ₖ (1 : Matrix (X × Y × Bool) (X × Y × Bool) ℂ)) (ancSplit V X Y (liftQ σ a))
      (ancSplit V X Y (liftQ σ b)) =
    (K.op r ⊗ₖ (1 : Matrix (X × Y × Bool) (X × Y × Bool) ℂ)) (ancSplit V X Y a) (ancSplit V X Y b)
  simp only [liftQ_apply, Equiv.apply_symm_apply, Matrix.kroneckerMap_apply, h r]

theorem KrausMap.LeftPerm.liftAnc {σ : Equiv.Perm (QueryReg V 1 X Y)}
    {K' K : KrausMap R (QueryReg V 1 X Y) (QueryReg V 1 X Y)} (h : KrausMap.LeftPerm σ K' K) :
    KrausMap.LeftPerm (liftQ σ) K'.liftAnc K.liftAnc :=
  (h.tensorId (X × Y × Bool)).reindex (ancSplit V X Y).symm

/-- **A basis permutation with the identity on the ancilla** is the basis permutation `liftQ`. -/
theorem liftAnc_ofPerm_apply (π : Equiv.Perm (QueryReg V 1 X Y))
    (ρ : Matrix (ReprogrammedQueryReg V X Y) (ReprogrammedQueryReg V X Y) ℂ) :
    (KrausMap.ofPerm π).liftAnc ρ = (KrausMap.ofPerm (liftQ π)) ρ := by
  have hop : (KrausMap.ofPerm π).liftAnc.op () = (KrausMap.ofPerm (liftQ π)).op () := by
    ext a b
    change ((KrausMap.ofPerm π).op () ⊗ₖ (1 : Matrix (X × Y × Bool) (X × Y × Bool) ℂ))
      (ancSplit V X Y a) (ancSplit V X Y b) = _
    rw [Matrix.kroneckerMap_apply, KrausMap.LeftPerm.ofPerm_op_apply,
      KrausMap.LeftPerm.ofPerm_op_apply, Matrix.one_apply]
    by_cases h1 : (ancSplit V X Y a).1 = π (ancSplit V X Y b).1 <;>
      by_cases h2 : (ancSplit V X Y a).2 = (ancSplit V X Y b).2
    · rw [if_pos h1, if_pos h2, one_mul, if_pos]
      apply (ancSplit V X Y).injective
      rw [liftQ_apply, Equiv.apply_symm_apply]
      exact Prod.ext h1 h2
    · rw [if_neg h2, mul_zero, if_neg]
      intro h
      apply h2
      rw [h, liftQ_apply, Equiv.apply_symm_apply]
    · rw [if_neg h1, zero_mul, if_neg]
      intro h
      apply h1
      rw [h, liftQ_apply, Equiv.apply_symm_apply]
    · rw [if_neg h1, zero_mul, if_neg]
      intro h
      apply h1
      rw [h, liftQ_apply, Equiv.apply_symm_apply]
  simp only [KrausMap.apply, hop]

end LiftQ

/-! ### Compiled circuits with permutations after the queries -/

section Compiled

variable {V X Y : Type} [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [AddGroup Y]

/-- **A support that reads only the work register and the query input.** -/
def WXDep {W : Type} (S : Set (QueryReg W 1 X Y)) : Prop :=
  ∀ p p' : QueryReg W 1 X Y, p.1 = p'.1 → (p.2 0).1 = (p'.2 0).1 → p ∈ S → p' ∈ S

theorem Circuit.withPerms_append {ι : Type} [Fintype ι] [DecidableEq ι] (π : ℕ → Equiv.Perm ι)
    (k : ℕ) (c d : Circuit ι) :
    (c ++ d).withPerms π k = c.withPerms π k ++ d.withPerms π (k + c.queries) := by
  induction c generalizing k with
  | nil => rfl
  | kraus K c ih =>
    change Circuit.kraus K ((c ++ d).withPerms π k) = Circuit.kraus K (c.withPerms π k ++ _)
    rw [ih]
    rfl
  | query c ih =>
    change Circuit.query (.kraus _ ((c ++ d).withPerms π (k + 1))) =
      Circuit.query (.kraus _ (c.withPerms π (k + 1) ++ _))
    rw [ih]
    simp only [Circuit.queries, Nat.add_assoc, Nat.add_comm 1]

variable {QI : Equiv.Perm (ReprogrammedQueryReg V X Y) → Prop}
  {SI : Set (ReprogrammedQueryReg V X Y) → Prop}

/-- **Twin compiled circuits of a concatenation** of circuits with `L` queries each, piece `i`
read from query `k₀ + i * L`, from `σ i`, `S i` to `σ (i + 1)`, `S (i + 1)`. -/
theorem twin_concat_of (π' π : ℕ → Equiv.Perm (ReprogrammedQueryReg V X Y)) {L : ℕ} :
    ∀ (cs' cs : List (ReprogrammedCircuit V X Y)) (k₀ : ℕ)
      (σ : ℕ → Equiv.Perm (ReprogrammedQueryReg V X Y)) (S : ℕ → Set (ReprogrammedQueryReg V X Y)),
      cs'.length = cs.length → (∀ c ∈ cs', c.queries = L) → (∀ c ∈ cs, c.queries = L) →
      (∀ i (hi : i < cs.length) (hi' : i < cs'.length),
        Circuit.Twin QI SI (σ (i + 1)) (S (i + 1)) (cs'[i].toCircuit.withPerms π' (k₀ + i * L))
          (cs[i].toCircuit.withPerms π (k₀ + i * L)) (σ i) (S i)) →
      Circuit.Twin QI SI (σ cs.length) (S cs.length)
        ((ReprogrammedCircuit.concat cs').toCircuit.withPerms π' k₀)
        ((ReprogrammedCircuit.concat cs).toCircuit.withPerms π k₀) (σ 0) (S 0)
  | [], [], _, _, _, _, _, _, _ => .nil rfl rfl
  | [], _ :: _, _, _, _, hl, _, _, _ => absurd hl (by simp)
  | _ :: _, [], _, _, _, hl, _, _, _ => absurd hl (by simp)
  | c' :: cs', c :: cs, k₀, σ, S, hl, hq', hq, h => by
    have hc' : c'.queries = L := hq' c' (List.mem_cons_self ..)
    have hc : c.queries = L := hq c (List.mem_cons_self ..)
    change Circuit.Twin QI SI (σ (cs.length + 1)) (S (cs.length + 1))
      ((c' ++ ReprogrammedCircuit.concat cs').toCircuit.withPerms π' k₀)
      ((c ++ ReprogrammedCircuit.concat cs).toCircuit.withPerms π k₀) (σ 0) (S 0)
    rw [ReprogrammedCircuit.toCircuit_append, ReprogrammedCircuit.toCircuit_append,
      Circuit.withPerms_append, Circuit.withPerms_append, ReprogrammedCircuit.queries_toCircuit,
      ReprogrammedCircuit.queries_toCircuit, hc, hc']
    have h0 := h 0 (by simp) (by simp)
    simp only [zero_mul, Nat.add_zero, Nat.zero_add, List.getElem_cons_zero] at h0
    refine Circuit.Twin.append h0 ?_
    exact twin_concat_of π' π cs' cs (k₀ + L) (fun i => σ (i + 1)) (fun i => S (i + 1))
      (by simpa using hl) (fun d hd => hq' d (List.mem_cons_of_mem _ hd))
      (fun d hd => hq d (List.mem_cons_of_mem _ hd)) fun i hi hi' => by
        have h' := h (i + 1) (by simp; omega) (by simp; omega)
        simp only [List.getElem_cons_succ] at h'
        rw [show k₀ + L + i * L = k₀ + (i + 1) * L by ring]
        exact h'

/-- `twin_concat_of` for the circuits of functions on `Fin n`. -/
theorem twin_concat_finRange (π' π : ℕ → Equiv.Perm (ReprogrammedQueryReg V X Y)) {n L : ℕ}
    (k₀ : ℕ) (f' f : Fin n → ReprogrammedCircuit V X Y) (hq' : ∀ i, (f' i).queries = L)
    (hq : ∀ i, (f i).queries = L) (σ : ℕ → Equiv.Perm (ReprogrammedQueryReg V X Y))
    (S : ℕ → Set (ReprogrammedQueryReg V X Y))
    (h : ∀ i : Fin n, Circuit.Twin QI SI (σ (i + 1)) (S (i + 1))
      ((f' i).toCircuit.withPerms π' (k₀ + i * L)) ((f i).toCircuit.withPerms π (k₀ + i * L))
      (σ i) (S i)) :
    Circuit.Twin QI SI (σ n) (S n)
      ((ReprogrammedCircuit.concat ((List.finRange n).map f')).toCircuit.withPerms π' k₀)
      ((ReprogrammedCircuit.concat ((List.finRange n).map f)).toCircuit.withPerms π k₀)
      (σ 0) (S 0) := by
  have := twin_concat_of (QI := QI) (SI := SI) π' π (L := L) ((List.finRange n).map f')
    ((List.finRange n).map f) k₀ σ S (by simp)
    (fun c hc => by obtain ⟨i, -, rfl⟩ := List.mem_map.1 hc; exact hq' i)
    (fun c hc => by obtain ⟨i, -, rfl⟩ := List.mem_map.1 hc; exact hq i)
    fun i hi hi' => by
      simp only [List.getElem_map, List.getElem_finRange]
      exact h ⟨i, by simpa using hi⟩
  simpa using this

end Compiled

/-! ### The base additions on the composed registers -/

/-- **Local queries of a kind algorithm on a part of its workspace**: a part `Lw` of the workspace
of `Y₁`-values, one per query pair, and the branches `on k` on which the adversary's Kraus map `k`
is followed by the local query; neither the branches nor the kind read the part. -/
structure KindShape.BaseQ {X Y Req Resp : Type} [Fintype X] [DecidableEq X] [Fintype Y]
    [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
    (ksT : KindShape X Y Req Resp) (kind : ksT.W → Bool) (Y₁ : Type) where
  /-- The part of the workspace. -/
  Lw : RegLens ksT.W (Fin ksT.width → Y₁)
  /-- The branches of the local query after Kraus map `k`. -/
  on : StepIdx ksT.slots ksT.post → ksT.W → Bool
  on_set : ∀ k w v, on k (Lw.set w v) = on k w
  kind_set : ∀ w v, kind (Lw.set w v) = kind w

/-- **Local queries of a kind algorithm on a part of its workspace**: those of its shape at its kind
(`KindShape.BaseQ`). -/
abbrev KindAlg.BaseQ {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y]
    [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
    {ksT : KindShape X Y Req Resp} (T : KindAlg ksT O) (Y₁ : Type) : Type :=
  ksT.BaseQ T.kind Y₁

/-- Where the input of a query pair is read on the composed registers: the adversary's pair, the
query register, or the query register or the reprogramming ancilla's input as the flag says. -/
inductive XPos
  | adv
  | qry
  | til
  deriving DecidableEq

section Carry

variable {X Y Y₁ Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [AddGroup Y₁]
  {ksT : KindShape X Y Req Resp} {T : KindAlg ksT O} {kind : ksT.W → Bool}
  {C : Challenger X Y Req Resp} (D : ksT.BaseQ kind Y₁) (ω : X → Y₁)

/-- The read of the input of pair `i`, at the query input `x` and the work register with the
ancilla `w`. -/
def XPos.read (C : Challenger X Y Req Resp) : XPos → Fin ksT.width → X →
    ksT.CW C × (X × Y × Bool) → X
  | .adv, i, _, w => (w.1.adv.2 i).1
  | .qry, _, x, _ => x
  | .til, _, x, w => if w.2.2.2 then w.2.1 else x

/-- The part on the composed work register with the ancilla. -/
def KindShape.BaseQ.wLens : RegLens (ksT.CW C × (X × Y × Bool)) (Fin ksT.width → Y₁) where
  get w := D.Lw.get w.1.adv.1.1
  set w v := (⟨((D.Lw.set w.1.adv.1.1 v, w.1.adv.1.2), w.1.adv.2), w.1.chal⟩, w.2)
  get_set _ _ := by simp
  set_get _ := by simp
  set_set _ _ _ := by simp

/-- **The pending local queries after Kraus map `k`**, at the query input `x`: on the branches of
`on k`, `ω` of pair `i`'s input (read at `pos i`) added to coordinate `i` for the pending `i`. -/
def KindShape.BaseQ.carryW (k : StepIdx ksT.slots ksT.post) (pend : Fin ksT.width → Bool)
    (pos : Fin ksT.width → XPos) (x : X) : RegAdd (ksT.CW C × (X × Y × Bool)) (Fin ksT.width → Y₁) where
  toRegLens := D.wLens
  f w i := if pend i && D.on k w.1.adv.1.1 then ω ((pos i).read C i x w) else 0
  f_set w v := by
    funext i
    cases h : pos i <;> simp [KindShape.BaseQ.wLens, XPos.read, D.on_set]; rfl

/-- **The pending local queries as a permutation of the composed registers with the ancilla**,
reading the query input. -/
def KindShape.BaseQ.carry (k : StepIdx ksT.slots ksT.post) (pend : Fin ksT.width → Bool)
    (pos : Fin ksT.width → XPos) : Equiv.Perm (ReprogrammedQueryReg (ksT.CW C) X Y) where
  toFun p := ((D.carryW ω k pend pos (p.2 0).1).perm p.1, p.2)
  invFun p := ((D.carryW ω k pend pos (p.2 0).1).perm.symm p.1, p.2)
  left_inv p := by simp
  right_inv p := by simp

theorem KindShape.BaseQ.carry_apply (k : StepIdx ksT.slots ksT.post) (pend : Fin ksT.width → Bool)
    (pos : Fin ksT.width → XPos) (p : ReprogrammedQueryReg (ksT.CW C) X Y) :
    D.carry ω k pend pos p = ((D.carryW ω k pend pos (p.2 0).1).perm p.1, p.2) :=
  rfl

/-- Pending queries with the same reads on the pending pairs are equal. -/
theorem KindShape.BaseQ.carry_congr (k : StepIdx ksT.slots ksT.post) (pend : Fin ksT.width → Bool)
    {pos pos' : Fin ksT.width → XPos} (h : ∀ i, pend i = true → pos i = pos' i) :
    D.carry (C := C) ω k pend pos = D.carry ω k pend pos' := by
  refine Equiv.ext fun p => Prod.ext ?_ rfl
  show D.wLens.set p.1 (D.wLens.get p.1 + (D.carryW (C := C) ω k pend pos (p.2 0).1).f p.1) =
    D.wLens.set p.1 (D.wLens.get p.1 + (D.carryW (C := C) ω k pend pos' (p.2 0).1).f p.1)
  congr 2
  funext i
  simp only [carryW]
  by_cases hp : pend i = true
  · rw [h i hp]
  · simp [hp]

end Carry

/-! ### The gates of the composition and the pending local queries -/

/-- **A kind algorithm with its Kraus maps replaced** by `st`. -/
abbrev KindAlg.withStep {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y]
    [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
    {ksT : KindShape X Y Req Resp} (T : KindAlg ksT O)
    (st : StepIdx ksT.slots ksT.post → KrausMap ksT.R (DReg ksT.W ksT.width X Y Req Resp)
      (DReg ksT.W ksT.width X Y Req Resp)) : KindAlg ksT O :=
  { T with step := st }

section Gates

variable {X Y Y₁ Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [AddGroup Y₁]
  {ksT : KindShape X Y Req Resp} {T : KindAlg ksT O} {kind : ksT.W → Bool}
  {C : Challenger X Y Req Resp} (D : ksT.BaseQ kind Y₁) (ω : X → Y₁)

/-- **Channel relations depend on the maps only through their channels.** -/
theorem chRel_congr {ι : Type} [Fintype ι] [DecidableEq ι] {R₁ R₂ R₁' R₂' : Type} [Fintype R₁]
    [Fintype R₂] [Fintype R₁'] [Fintype R₂'] {σ' σ : Equiv.Perm ι} {S : Set ι}
    {K₁' : KrausMap R₁' ι ι} {K₁ : KrausMap R₁ ι ι} {K₂' : KrausMap R₂' ι ι}
    {K₂ : KrausMap R₂ ι ι} (h' : ∀ ρ, K₁' ρ = K₂' ρ) (h : ∀ ρ, K₁ ρ = K₂ ρ)
    (hr : ChRel σ' σ S K₂' K₂) : ChRel σ' σ S K₁' K₁ := fun ρ hρ => by
  rw [h', h, hr ρ hρ]

/-- **The set of the reprogramming flag down.** -/
def flagF (V X Y : Type) : Set (ReprogrammedQueryReg V X Y) :=
  {p | p.1.2.2.2 = false}

/-- **The supports between the two exchanges of a reprogrammed query**: the flag is up exactly
when the reprogramming condition holds. -/
def condSet {V : Type} (a : V → List (Assignment X Y)) : Set (ReprogrammedQueryReg V X Y) :=
  {p | p.1.2.2.2 = true ↔ reprogCond a p}

/-- The supports between the exchanges read only the work register and the query input. -/
theorem wxDep_condSet {V : Type} [AddGroup Y] (a : V → List (Assignment X Y)) :
    WXDep (condSet a) := fun p p' h1 h2 hp => by
  simp only [condSet, reprogCond, Set.mem_setOf_eq] at hp ⊢
  rw [← h1, ← h2]
  exact hp

/-- **A Kraus map with the identity on the ancilla keeps the flag down.** -/
theorem keeps_liftAnc_flagF {V : Type} [Fintype V] [DecidableEq V] {R : Type} [Fintype R]
    (K : KrausMap R (QueryReg V 1 X Y) (QueryReg V 1 X Y)) :
    Keeps (flagF V X Y) (flagF V X Y) K.liftAnc := fun ρ hρ a b hab => by
  have hop : ∀ r (c d : ReprogrammedQueryReg V X Y), K.liftAnc.op r c d ≠ 0 → c.1.2 = d.1.2 :=
    fun r c d h => by
      change (K.op r ⊗ₖ (1 : Matrix (X × Y × Bool) (X × Y × Bool) ℂ)) (ancSplit V X Y c)
        (ancSplit V X Y d) ≠ 0 at h
      rw [Matrix.kroneckerMap_apply, Matrix.one_apply] at h
      by_contra hne
      exact h (by simp [ancSplit, hne])
  simp only [KrausMap.apply, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply] at hab
  obtain ⟨r, -, hr⟩ := Finset.exists_ne_zero_of_sum_ne_zero hab
  obtain ⟨c, -, hc⟩ := Finset.exists_ne_zero_of_sum_ne_zero hr
  rw [Finset.sum_mul] at hc
  obtain ⟨d, -, hd⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
  obtain ⟨hdS, hcS⟩ := hρ d c (right_ne_zero_of_mul (left_ne_zero_of_mul hd))
  have e1 := hop r a d (left_ne_zero_of_mul (left_ne_zero_of_mul hd))
  have e2 := hop r b c (fun h0 => right_ne_zero_of_mul hd (by rw [h0, star_zero]))
  simp only [flagF, Set.mem_setOf_eq] at hdS hcS ⊢
  exact ⟨by rw [e1]; exact hdS, by rw [e2]; exact hcS⟩

/-- **The first exchange carries the flag down to the supports between the exchanges.** -/
theorem keeps_reprogSwap_flagF {V : Type} [Fintype V] [DecidableEq V]
    (a : V → List (Assignment X Y)) :
    Keeps (flagF V X Y) (condSet a) (KrausMap.ofPerm (reprogSwap a)) :=
  keeps_ofPerm_of fun p hp => by
    obtain ⟨⟨w, ax, ay, fl⟩, qp⟩ := p
    simp only [flagF, Set.mem_setOf_eq] at hp
    subst hp
    simp only [condSet, Set.mem_setOf_eq, reprogSwap_apply]
    by_cases h : reprogCond a ((w, ax, ay, false), qp)
    · rw [if_pos h, reprogCond_swapFlip]
      simp [swapFlip, h]
    · rw [if_neg h]
      simp [h]

/-- **The second exchange and the addition carry the supports between the exchanges to the flag
down.** -/
theorem keeps_reprogTail {V : Type} [Fintype V] [DecidableEq V] [AddGroup Y]
    (a : V → List (Assignment X Y)) :
    Keeps (condSet a) (flagF V X Y)
      ((KrausMap.ofPerm (reprogAdd a)).comp (KrausMap.ofPerm (reprogSwap a))) := by
  refine Keeps.comp (S' := flagF V X Y) (keeps_ofPerm_of fun p hp => ?_)
    (keeps_ofPerm_of fun p hp => ?_)
  · simpa [flagF, reprogAdd] using hp
  · obtain ⟨⟨w, ax, ay, fl⟩, qp⟩ := p
    simp only [condSet, Set.mem_setOf_eq] at hp
    simp only [flagF, Set.mem_setOf_eq, reprogSwap_apply]
    by_cases h : reprogCond a ((w, ax, ay, fl), qp)
    · rw [if_pos h]
      have hf := hp.2 h
      subst hf
      rfl
    · rw [if_neg h]
      cases fl
      · rfl
      · exact absurd (hp.1 rfl) h

/-- **Twin compiled circuits of two concatenated circuits**, the second read after the first
one's queries. -/
theorem twin_rc_append {V : Type} [Fintype V] [DecidableEq V] [AddGroup Y]
    {QI : Equiv.Perm (ReprogrammedQueryReg V X Y) → Prop}
    {SI : Set (ReprogrammedQueryReg V X Y) → Prop}
    {π' π : ℕ → Equiv.Perm (ReprogrammedQueryReg V X Y)} {c₁' c₁ c₂' c₂ : ReprogrammedCircuit V X Y}
    {k : ℕ} {σ σm σe : Equiv.Perm (ReprogrammedQueryReg V X Y)}
    {S Sm Se : Set (ReprogrammedQueryReg V X Y)}
    (h₁ : Circuit.Twin QI SI σm Sm (c₁'.toCircuit.withPerms π' k) (c₁.toCircuit.withPerms π k) σ S)
    (h₂ : Circuit.Twin QI SI σe Se (c₂'.toCircuit.withPerms π' (k + c₁'.queries))
      (c₂.toCircuit.withPerms π (k + c₁.queries)) σm Sm) :
    Circuit.Twin QI SI σe Se ((c₁' ++ c₂').toCircuit.withPerms π' k)
      ((c₁ ++ c₂).toCircuit.withPerms π k) σ S := by
  rw [ReprogrammedCircuit.toCircuit_append, ReprogrammedCircuit.toCircuit_append,
    Circuit.withPerms_append, Circuit.withPerms_append, ReprogrammedCircuit.queries_toCircuit,
    ReprogrammedCircuit.queries_toCircuit]
  exact h₁.append h₂

theorem KindAlg.chalQueries_eq_nil [Nonempty X] [AddGroup Y] (hq : C.q = 0) (j : Fin ksT.slots) :
    T.chalQueries C j = .nil := by
  have hl : (List.finRange C.q).map (fun i => (ReprogrammedCircuit.kraus
      (KrausMap.ofPerm (T.prepChal C j i)) (.rquery (fun v => T.chalAss C j i v.chal)
        (.kraus (KrausMap.ofPerm (T.garSwap C j i)) .nil)) : ReprogrammedCircuit (ksT.CW C) X Y)) =
      [] := List.eq_nil_of_length_eq_zero (by simp [hq])
  unfold KindAlg.chalQueries
  rw [hl]
  rfl

theorem queries_concat_finRange' {V : Type} [Fintype V] [DecidableEq V] {n L : ℕ}
    {f : Fin n → ReprogrammedCircuit V X Y} (hq : ∀ i, (f i).queries = L) :
    (ReprogrammedCircuit.concat ((List.finRange n).map f)).queries = n * L := by
  rw [ReprogrammedCircuit.queries_concat, List.map_map]
  have h : (List.finRange n).map ((fun c => ReprogrammedCircuit.queries c) ∘ f) =
      (List.finRange n).map fun _ => L := List.map_congr_left fun i _ => hq i
  rw [h]
  simp

end Gates

end GordieHowe.Quantum
