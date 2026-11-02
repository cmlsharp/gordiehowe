-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.BlockRel
public import GordieHowe.Model.Quantum.Interactive.TPRun
public import GordieHowe.Model.Quantum.Interactive.ReqBridgeCirc

@[expose] public section

/-!
# The block hypotheses through the trace-preserving form

For a trace-preserving adversary `A` and other trace-preserving Kraus maps `st'`, the block
hypotheses (`GordieHowe/Model/Quantum/Interactive/BlockRel.lean`) of `A` and `st'` give those of
the trace-preserving forms (`AdaptiveIAlg.toTPKindAlg`), whose steps are the steps of the aborting
completion (`AdaptiveIAlg.abortAlg`), with the label, the sets and the permutations read on `A`'s
part of the workspace (the query counter kept).

- `AdaptiveIAlg.abortStep`, `AdaptiveIAlg.abortAlg_withStep`: the Kraus maps `st'` read through the
  aborting completion.
- `AdaptiveIAlg.cntSet`, `AdaptiveIAlg.prevSeq_cntSet`, `AdaptiveIAlg.prevSeq_cntOne`: a set of
  `A`'s workspace, request and response read past the counter, and the sequences of sets and of
  permutations (`AdaptiveIAlg.cntOne`) with the counter kept.
- `AdaptiveIAlg.tpOp_inr_inr_eq_zero`, `AdaptiveIAlg.abortStep_op`,
  `AdaptiveIAlg.abortAlg_init_mat`: the entries of the aborting
  completions' steps and initial state.
- `AdaptiveIAlg.tpShift_symm_fst`, `AdaptiveIAlg.endSwap_symm_fst`, `AdaptiveIAlg.tpShift_symm_ws`,
  `AdaptiveIAlg.endSwap_symm_ws`: the counter's maps keep the rest of the registers.
- `AdaptiveIAlg.tpOp_ne_zero`, `AdaptiveIAlg.rowGram_tpOp`: a nonzero entry of the
  trace-preserving form is one of the adversary's Kraus map; the overlaps into a block are those of
  the Kraus map when the counters agree, else zero.
- `AdaptiveIAlg.BlockRel.toTP`, `AdaptiveIAlg.BlockNone.toTP`: the block hypotheses of the
  aborting completions of `A` and `A.withStep st'`.
-/

open Matrix
open scoped BigOperators

namespace GordieHowe.Quantum

open GordieHowe.QROM KrausRel

namespace AdaptiveIAlg

variable {X Y Req Resp O L : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]

variable {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O)
  (st' : StepIdx A.slots A.post → KrausMap A.R (DReg A.W A.width X Y Req Resp)
    (DReg A.W A.width X Y Req Resp))

/-! ### The aborting completion with other Kraus maps -/

/-- **The Kraus maps `st'` read through the aborting completion**: the steps of the
trace-preserving form of `A.withStep st'`. -/
noncomputable def abortStep : StepIdx A.abortAlg.slots A.abortAlg.post →
    KrausMap A.abortAlg.R (DReg A.abortAlg.W A.abortAlg.width X Y Req Resp)
      (DReg A.abortAlg.W A.abortAlg.width X Y Req Resp) :=
  fun k => (A.withStep st').toTPKindAlg.step k

/-- **The aborting completion of `A.withStep st'`** is that of `A` with the Kraus maps
`abortStep`. -/
theorem abortAlg_withStep : (A.withStep st').abortAlg = A.abortAlg.withStep (A.abortStep st') :=
  rfl

/-! ### Sets with the counter kept -/

/-- **A set of `A`'s workspace, request and response, read past the counter.** -/
def cntSet (S : Set (A.W × Req × Option Resp)) :
    Set ((A.W × Fin (A.budget + 2)) × Req × Option Resp) :=
  {x | (x.1.1, x.2) ∈ S}

theorem prevSeq_cntSet (G : ℕ → Set (A.W × Req × Option Resp))
    (G₀ : Set (A.W × Req × Option Resp)) (n : ℕ) :
    prevSeq (fun n => A.cntSet (G n)) (A.cntSet G₀) n = A.cntSet (prevSeq G G₀ n) := by
  simp only [prevSeq]
  split_ifs <;> rfl

theorem prevSeq_cntOne (σ : ℕ → Equiv.Perm (A.W × Req × Option Resp))
    (σ₀ : Equiv.Perm (A.W × Req × Option Resp)) (n : ℕ) :
    prevSeq (fun n => A.cntOne (σ n)) (A.cntOne σ₀) n = A.cntOne (prevSeq σ σ₀ n) := by
  simp only [prevSeq]
  split_ifs <;> rfl

/-! ### The entries of the trace-preserving form -/

theorem tpOp_inr_inr_eq_zero (hA : A.TracePreserving) (k : StepIdx A.slots A.post)
    (c : Fin (A.budget + 2)) : A.tpOp false k (.inr (.inr c)) = 0 := by
  simp only [tpOp_false, tpRaw_inl, tpRaw_inr_inl, tpRaw_inr_inr,
      TracePreserving.haltOp_eq_zero hA k, Matrix.zero_kronecker]
  rfl

/-- **The Kraus maps `abortStep st'` are the operators of the trace-preserving form of
`A.withStep st'`.** -/
theorem abortStep_op (k : StepIdx A.abortAlg.slots A.abortAlg.post) (r : A.abortAlg.R)
    (y x : A.CReg) : (A.abortStep st' k).op r y x = (A.withStep st').tpOp false k r y x := by
  show (((A.withStep st').toTPKindAlg).step k).op r y x = _
  rw [toTPKindAlg_step_op]

/-- The entries of the initial state of the aborting completion. -/
theorem abortAlg_init_mat (a b : DReg A.abortAlg.W A.abortAlg.width X Y Req Resp) :
    A.abortAlg.init.mat a b = A.init.mat (A.cntSplit a).1 (A.cntSplit b).1 *
      Matrix.single (0 : Fin (A.budget + 2)) 0 (1 : ℂ) (A.cntSplit a).2 (A.cntSplit b).2 :=
  rfl

theorem tpShift_symm_fst (y : A.CReg) : (A.cntSplit (A.tpShift.symm y)).1 = (A.cntSplit y).1 := by
  obtain ⟨⟨⟨w, c⟩, q, a⟩, p⟩ := y
  rfl

theorem endSwap_symm_fst (y : A.CReg) : (A.cntSplit (A.endSwap.symm y)).1 = (A.cntSplit y).1 := by
  obtain ⟨⟨⟨w, c⟩, q, a⟩, p⟩ := y
  rfl

theorem tpShift_symm_ws (z : A.CReg) : (A.tpShift.symm z).workspace.1 = z.workspace.1 := by
  obtain ⟨⟨⟨w, c⟩, q, a⟩, p⟩ := z
  rfl

theorem endSwap_symm_ws (z : A.CReg) : (A.endSwap.symm z).workspace.1 = z.workspace.1 := by
  obtain ⟨⟨⟨w, c⟩, q, a⟩, p⟩ := z
  rfl

/-- **A nonzero entry of the trace-preserving form** of a trace-preserving adversary is one of its
Kraus map at a row with the same workspace, request and response. -/
theorem tpOp_ne_zero (hA : A.TracePreserving) {k : StepIdx A.slots A.post}
    {i : A.R ⊕ (A.R ⊕ Fin (A.budget + 2))} {y x : A.CReg} (h : A.tpOp false k i y x ≠ 0) :
    ∃ r, (A.step k).op r (A.cntSplit y).1 (A.cntSplit x).1 ≠ 0 := by
  rcases i with r | r | c
  · rw [tpOp_inl_entry] at h
    by_cases hk : (k : ℕ) < A.slots
    · simp only [hk, ↓reduceIte] at h
      have h' := right_ne_zero_of_mul h
      rw [cntKraus_op_apply, tpShift_symm_fst] at h'
      exact ⟨r, left_ne_zero_of_mul h'⟩
    · simp only [hk, ↓reduceIte, cntKraus_op_apply] at h
      exact ⟨r, left_ne_zero_of_mul h⟩
  · rw [tpOp_inr_inl_entry] at h
    by_cases hk : (k : ℕ) < A.slots
    · simp only [hk, ↓reduceIte] at h
      have h' := right_ne_zero_of_mul h
      rw [cntKraus_op_apply, endSwap_symm_fst] at h'
      exact ⟨r, left_ne_zero_of_mul h'⟩
    · simp only [hk, ↓reduceIte] at h
      exact absurd rfl h
  · rw [A.tpOp_inr_inr_eq_zero hA k c] at h
    exact absurd rfl h

/-- **The overlaps into a block of the trace-preserving form** of a trace-preserving adversary:
those of its Kraus map when the counters agree, else zero. -/
theorem rowGram_tpOp [DecidableEq L] (ℓ : A.W → Option L) (hA : A.TracePreserving)
    (k : StepIdx A.slots A.post) (T : KrausMap (A.R ⊕ (A.R ⊕ Fin (A.budget + 2))) A.CReg A.CReg)
    (hT : ∀ i y x, T.op i y x = A.tpOp false k i y x) (r : L) (c d : A.CReg) :
    rowGram (fun p : A.CReg => ℓ p.workspace.1) r T c d =
      (1 : Matrix (Fin (A.budget + 2)) (Fin (A.budget + 2)) ℂ) c.workspace.2 d.workspace.2 *
        rowGram (fun p : DReg A.W A.width X Y Req Resp => ℓ p.workspace) r (A.step k)
          (A.cntSplit c).1 (A.cntSplit d).1 := by
  classical
  -- the overlaps of the Kraus map with the counter
  have hc : ∀ r' : A.R, (∑ z : A.CReg, if ℓ z.workspace.1 = some r then
      (A.cntKraus k).op r' z c * star ((A.cntKraus k).op r' z d) else 0) =
      (1 : Matrix (Fin (A.budget + 2)) (Fin (A.budget + 2)) ℂ) c.workspace.2 d.workspace.2 *
        ∑ u : DReg A.W A.width X Y Req Resp, if ℓ u.workspace = some r then
          (A.step k).op r' u (A.cntSplit c).1 * star ((A.step k).op r' u (A.cntSplit d).1)
        else 0 := fun r' => by
    rw [← Equiv.sum_comp A.cntSplit.symm, Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp only [cntKraus_op_apply, Equiv.apply_symm_apply]
    change (∑ t : Fin (A.budget + 2), if ℓ u.workspace = some r then
      ((A.step k).op r' u (A.cntSplit c).1 * (1 : Matrix _ _ ℂ) t c.workspace.2) *
        star ((A.step k).op r' u (A.cntSplit d).1 * (1 : Matrix _ _ ℂ) t d.workspace.2)
      else 0) = _
    split_ifs
    · simp only [star_mul', Matrix.one_apply]
      by_cases hcd : c.workspace.2 = d.workspace.2
      · rw [Finset.sum_eq_single d.workspace.2 (fun t _ ht => by simp [ht]) (by simp)]
        simp [hcd]
      · rw [Finset.sum_eq_zero fun t _ => ?_]
        · simp [hcd]
        · by_cases h1 : t = c.workspace.2
          · subst h1
            simp [hcd]
          · simp [h1]
    · simp
  -- the two operators of a slot's step split those of the Kraus map with the counter
  have hpair : ∀ r', (∑ a : A.CReg, if ℓ a.workspace.1 = some r then
        A.tpOp false k (.inl r') a c * star (A.tpOp false k (.inl r') a d) else 0) +
      (∑ a : A.CReg, if ℓ a.workspace.1 = some r then
        A.tpOp false k (.inr (.inl r')) a c * star (A.tpOp false k (.inr (.inl r')) a d) else 0) =
      ∑ z : A.CReg, if ℓ z.workspace.1 = some r then
        (A.cntKraus k).op r' z c * star ((A.cntKraus k).op r' z d) else 0 := by
    intro r'
    simp only [tpOp_inl_entry, tpOp_inr_inl_entry]
    by_cases hk : (k : ℕ) < A.slots
    · simp only [hk, ↓reduceIte]
      rw [← Equiv.sum_comp A.tpShift, ← Equiv.sum_comp A.endSwap
        (fun a => if ℓ a.workspace.1 = some r then
          ((if !A.inBudget (A.endSwap.symm a) then (1 : ℂ) else 0) *
            (A.cntKraus k).op r' (A.endSwap.symm a) c) *
          star ((if !A.inBudget (A.endSwap.symm a) then (1 : ℂ) else 0) *
            (A.cntKraus k).op r' (A.endSwap.symm a) d) else 0),
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun z _ => ?_
      have e1 : (A.tpShift z).workspace.1 = z.workspace.1 := by
        rw [← tpShift_symm_ws A (A.tpShift z), Equiv.symm_apply_apply]
      have e2 : (A.endSwap z).workspace.1 = z.workspace.1 := by
        rw [← endSwap_symm_ws A (A.endSwap z), Equiv.symm_apply_apply]
      simp only [Equiv.symm_apply_apply, e1, e2]
      cases hb : A.inBudget z <;> simp
    · simp [hk]
  unfold rowGram
  simp only [hT, Finset.sum_filter]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [A.tpOp_inr_inr_eq_zero hA k, Matrix.zero_apply, zero_mul, ite_self,
    Finset.sum_const_zero, add_zero]
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r' _ => ?_
  rw [← hc r', ← hpair r']

/-! ### The block hypotheses of the aborting completions -/

variable {A st'}

/-- **The block hypotheses through the aborting completion**: those of `A` and `st'`, for
trace-preserving `A` and `A.withStep st'`, give those of their aborting completions, with the
label, the sets and the permutations read on `A`'s part of the workspace. -/
theorem BlockRel.toTP {ℓ : A.W → Option L} {G G' : ℕ → Set (A.W × Req × Option Resp)}
    {G₀ G₀' : Set (A.W × Req × Option Resp)} {σ : ℕ → Equiv.Perm (A.W × Req × Option Resp)}
    {σ₀ : Equiv.Perm (A.W × Req × Option Resp)} {r : L} (hA : A.TracePreserving)
    (hA' : (A.withStep st').TracePreserving) (h : A.BlockRel st' ℓ G G' G₀ G₀' σ σ₀ r) :
    A.abortAlg.BlockRel (A.abortStep st') (fun w => ℓ w.1) (fun n => A.cntSet (G n))
      (fun n => A.cntSet (G' n)) (A.cntSet G₀) (A.cntSet G₀') (fun n => A.cntOne (σ n))
      (A.cntOne σ₀) r where
  label_eq n x := h.label_eq n (x.1.1, x.2)
  label_eq₀ x := h.label_eq₀ (x.1.1, x.2)
  kind_eq n x := by
    show (A.kind (σ n (x.1.1, x.2)).1 || decide (x.1.2 = A.ended)) =
      (A.kind x.1.1 || decide (x.1.2 = A.ended))
    rw [h.kind_eq n (x.1.1, x.2)]
  set_eq n x hx := h.set_eq n (x.1.1, x.2) hx
  set_eq₀ x hx := h.set_eq₀ (x.1.1, x.2) hx
  keepsSet k i a b hb hne := by
    erw [prevSeq_cntSet] at hb
    rw [abortAlg_step_op] at hne
    obtain ⟨r', hr⟩ := A.tpOp_ne_zero hA (k := k) (i := i) (y := a) (x := b) hne
    exact h.keepsSet k r' _ _ hb hr
  keepsSet' k i a b hb hne := by
    erw [prevSeq_cntSet] at hb
    rw [abortStep_op] at hne
    obtain ⟨r', hr⟩ := (A.withStep st').tpOp_ne_zero hA' (k := k) (i := i) (y := a) (x := b) hne
    exact h.keepsSet' k r' _ _ hb hr
  keeps k i r' a b hbG hb hne := by
    erw [prevSeq_cntSet] at hbG
    rw [abortAlg_step_op] at hne
    obtain ⟨r'', hr⟩ := A.tpOp_ne_zero hA (k := k) (i := i) (y := a) (x := b) hne
    exact h.keeps k r'' r' _ _ hbG hb hr
  keeps' k i r' a b hbG hb hne := by
    erw [prevSeq_cntSet] at hbG
    rw [abortStep_op] at hne
    obtain ⟨r'', hr⟩ := (A.withStep st').tpOp_ne_zero hA' (k := k) (i := i) (y := a) (x := b) hne
    exact h.keeps' k r'' r' _ _ hbG hb hr
  hop k i a b ha hb := by
    have hb2 := hb.2
    erw [prevSeq_cntSet] at hb2
    have hb' : (A.cntSplit b).1 ∈ {d : DReg A.W A.width X Y Req Resp |
        InBlock ℓ r d.workspace ∧ d.1 ∈ prevSeq G G₀ k} := ⟨hb.1, hb2⟩
    erw [prevSeq_cntOne]
    rw [abortStep_op, abortAlg_step_op]
    exact tpOp_withStep_cntOne st' (hA.haltOp_eq_zero k) (hA'.haltOp_eq_zero k) (h.kind_eq k)
      (h.hop k) i a b ha hb'
  init_supp a b hab := by
    rw [abortAlg_init_mat] at hab
    exact h.init_supp _ _ (left_ne_zero_of_mul hab)
  init_supp' a b hab := by
    rw [abortAlg_init_mat] at hab
    exact h.init_supp' _ _ (left_ne_zero_of_mul hab)
  init_eq a b haG hbG ha hb := by
    rw [abortAlg_init_mat, abortAlg_init_mat]
    exact congrArg (· * _) (h.init_eq (A.cntSplit a).1 (A.cntSplit b).1 haG hbG ha hb)

/-- **The `none`-block hypotheses through the aborting completion**, for trace-preserving `A` and
`A.withStep st'`. -/
theorem BlockNone.toTP [DecidableEq L] {ℓ : A.W → Option L}
    {G G' : ℕ → Set (A.W × Req × Option Resp)} {G₀ G₀' : Set (A.W × Req × Option Resp)}
    (hA : A.TracePreserving) (hA' : (A.withStep st').TracePreserving)
    (h : A.BlockNone st' ℓ G G' G₀ G₀') :
    A.abortAlg.BlockNone (A.abortStep st') (fun w => ℓ w.1) (fun n => A.cntSet (G n))
      (fun n => A.cntSet (G' n)) (A.cntSet G₀) (A.cntSet G₀') where
  none_eq n x hx := h.none_eq n (x.1.1, x.2) hx
  none_eq₀ x hx := h.none_eq₀ (x.1.1, x.2) hx
  keepsSet k i a b hb hne := by
    erw [prevSeq_cntSet] at hb
    rw [abortAlg_step_op] at hne
    obtain ⟨r', hr⟩ := A.tpOp_ne_zero hA (k := k) (i := i) (y := a) (x := b) hne
    exact h.keepsSet k r' _ _ hb hr
  keepsSet' k i a b hb hne := by
    erw [prevSeq_cntSet] at hb
    rw [abortStep_op] at hne
    obtain ⟨r', hr⟩ := (A.withStep st').tpOp_ne_zero hA' (k := k) (i := i) (y := a) (x := b) hne
    exact h.keepsSet' k r' _ _ hb hr
  keeps k i r' a b hbG hb hne := by
    erw [prevSeq_cntSet] at hbG
    rw [abortAlg_step_op] at hne
    obtain ⟨r'', hr⟩ := A.tpOp_ne_zero hA (k := k) (i := i) (y := a) (x := b) hne
    exact h.keeps k r'' r' _ _ hbG hb hr
  keeps' k i r' a b hbG hb hne := by
    erw [prevSeq_cntSet] at hbG
    rw [abortStep_op] at hne
    obtain ⟨r'', hr⟩ := (A.withStep st').tpOp_ne_zero hA' (k := k) (i := i) (y := a) (x := b) hne
    exact h.keeps' k r'' r' _ _ hbG hb hr
  row_none_eq k i a b haG hbG ha hb := by
    erw [prevSeq_cntSet] at hbG
    have hrel : OpRelOn₂ (tripPerm (Equiv.refl _)) (tripPerm (Equiv.refl _))
        {d : DReg A.W A.width X Y Req Resp | d.1 ∈ G k ∧ ℓ d.workspace = none}
        {d : DReg A.W A.width X Y Req Resp | d.1 ∈ prevSeq G G₀ k ∧ ℓ d.workspace = none}
        (A.step k) (st' k) :=
      fun i' a' b' ha' hb' => h.row_none_eq k i' a' b' ha'.1 hb'.1 ha'.2 hb'.2
    rw [abortStep_op, abortAlg_step_op]
    exact tpOp_withStep_cntOne st' (hA.haltOp_eq_zero k) (hA'.haltOp_eq_zero k) (fun _ => rfl)
      hrel i a b ⟨haG, ha⟩ ⟨hbG, hb⟩
  gram_eq k r c d hcG hdG hc hd := by
    erw [prevSeq_cntSet] at hcG hdG
    refine ((A.withStep st').rowGram_tpOp ℓ hA' k (A.abortStep st' k)
      (abortStep_op A st' k) r c d).trans
        (Eq.trans ?_ (A.rowGram_tpOp ℓ hA k (A.abortAlg.step k) (abortAlg_step_op A k) r c d).symm)
    exact congrArg (_ * ·) (h.gram_eq k r _ _ hcG hdG hc hd)
  init_supp a b hab := by
    rw [abortAlg_init_mat] at hab
    exact h.init_supp _ _ (left_ne_zero_of_mul hab)
  init_supp' a b hab := by
    rw [abortAlg_init_mat] at hab
    exact h.init_supp' _ _ (left_ne_zero_of_mul hab)

end AdaptiveIAlg

end GordieHowe.Quantum
