-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.RingSwitching.PackingRoute
public import GordieHowe.ProofSystem.FieldProof.ClaimSupport

@[expose] public section

/-!
# What the claims of a routed stage read

A routed stage (`MaskedReduction.routedStage`) needs its passing claims to read no coordinate of the
stage's child (`MaskedReduction.PassingAvoid`). This file tracks what each claim reads
(`AffineForm.ReadsOnly`) through a routed stage, so that a tree of routed stages can choose its
touching claims from what they read:

* **the claims of a masked reduction read only `T`** (`MaskedReduction.ReadsOnly`): claim `c` reads
  only the coordinates of `T c`, at every public input and transcript;
* **avoidance from supports** (`MaskedReduction.passingAvoid_of_readsOnly`): a passing claim whose
  support holds no child coordinate avoids the child;
* **the supports after a routed stage** (`MaskedReduction.ReadsOnly.routedStage`, at
  `StageRouting.outSupport`): the remainder row reads the touching claims' coordinates off the
  child and the cells, each measurement row the stage's words and the cells, each passing claim
  its own coordinates off the child.
-/

namespace GordieHowe

open IOP IOP.ProtocolSpec PackingStage RelativePacking AffineForm
open GKR.Schedule (one oneValue)
open scoped NNReal

variable {F ι : Type} [Field F] {ng d : ℕ} {Y : Type} [DecidableEq Y]

/-! ### Coefficients on the child's coordinates -/

/-- The coefficient on a child coordinate is the form's coefficient there. -/
theorem childCoeff_eq_coeff (c : AffineForm F (Y ⊕ PackedCoord ng d)) (g : Fin ng) (j : Fin d) :
    childCoeff c g j = c.coeff (.inr ⟨g, j⟩) := by
  rw [childCoeff, coeff_eq_sum_terms]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  rcases t with ⟨a, y | q⟩
  · simp
  · simp only [Sum.elim_inr, Sum.inr.injEq]

/-- The part off the child's coordinates has the form's coefficients on `Y`. -/
theorem coeff_restPart (c : AffineForm F (Y ⊕ PackedCoord ng d)) (y : Y) :
    (restPart c).coeff y = c.coeff (.inl y) := by
  rw [coeff_eq_sum_terms, coeff_eq_sum_terms, restPart, filterMapTerms]
  dsimp only
  induction c.terms with
  | nil => simp
  | cons t l ih =>
    rcases t with ⟨a, y' | q⟩
    · simp only [List.filterMap_cons, Sum.elim_inl, List.map_cons, List.sum_cons, ih,
        Sum.inl.injEq]
    · simp only [List.filterMap_cons, Sum.elim_inr, List.map_cons, List.sum_cons, ih,
        reduceCtorEq, ite_false, zero_add]

/-- **A claim whose support holds no child coordinate avoids the child.** -/
theorem avoids_of_readsOnly {T : Y ⊕ PackedCoord ng d → Prop}
    {c : AffineForm F (Y ⊕ PackedCoord ng d)} (h : c.ReadsOnly T) (hT : ∀ q, ¬ T (.inr q)) :
    Avoids c := fun g j => by
  rw [childCoeff_eq_coeff]
  exact h.coeff_eq_zero (hT _)

namespace AffineForm.ReadsOnly

/-- **The part off the child reads what the claim reads off the child.** -/
theorem restPart {T : Y ⊕ PackedCoord ng d → Prop}
    {c : AffineForm F (Y ⊕ PackedCoord ng d)} (h : c.ReadsOnly T) :
    (GordieHowe.restPart c).ReadsOnly fun y => T (.inl y) := fun y hy => by
  rw [coeff_restPart] at hy
  exact h _ hy

/-- **A combination reads what its claims read.** -/
theorem combination {Z : Type} [DecidableEq Z] {nc : ℕ} {T : Z → Prop} (ρ : Fin nc → F)
    {cl : Fin nc → AffineForm F Z} (h : ∀ i, (cl i).ReadsOnly T) :
    (GordieHowe.combination ρ cl).ReadsOnly T :=
  AffineForm.ReadsOnly.sumFin fun i => (h i).smul (ρ i)

end AffineForm.ReadsOnly

/-! ### The supports of a masked reduction's claims -/

namespace FieldProof.MaskedReduction

variable [Fintype ι] {Pub Wit Z : Type} [DecidableEq Z] {cells : Wit → ι → F} {nc : ℕ}

variable {nt np : ℕ}

/-- **A passing claim whose support holds no child coordinate avoids the child**, so the routing
obligation of a routed stage holds. -/
theorem passingAvoid_of_readsOnly {M : MaskedReduction F ι Pub Wit cells (Y ⊕ PackedCoord ng d) nc}
    {T : Fin nc → Y ⊕ PackedCoord ng d → Prop} (h : M.ReadsOnly T) (R : StageRouting nc nt np)
    (hT : ∀ i q, ¬ T (R.split.symm (.inr i)) (.inr q)) : M.PassingAvoid R :=
  fun p tr i => avoids_of_readsOnly (h p tr _) (hT i)

end FieldProof.MaskedReduction

/-! ### The supports after a routed stage -/

namespace StageRouting

variable {nc nt np : ℕ}

/-- **What the claims after a routed stage read**, from what the claims before it read (`T`), the
stage's words `word` and the cells' coordinates `cell`: the remainder row the touching claims'
coordinates off the child and the cells, each measurement row the words and the cells, each
passing claim its coordinates off the child. -/
def outSupport (R : StageRouting nc nt np) (T : Fin nc → Y ⊕ PackedCoord ng d → Prop)
    (word : Fin ng → Y) {ι : Type} (cell : ι → Y) : Fin (d + 1 + np) → Y → Prop :=
  Fin.append
    (Fin.cases (fun y => (∃ i, T (R.split.symm (.inl i)) (.inl y)) ∨ ∃ c, cell c = y)
      fun _ y => (∃ g, word g = y) ∨ ∃ c, cell c = y)
    fun i y => T (R.split.symm (.inr i)) (.inl y)

/-- **A stage's routing with its counts**: `nt` touching and `np` passing claims. -/
structure Routing (nc : ℕ) where
  /-- The number of touching claims. -/
  nt : ℕ
  /-- The number of passing claims. -/
  np : ℕ
  /-- The routing. -/
  route : StageRouting nc nt np

/-- **The split of the claims by a test**: the claims the test accepts, in increasing order, then
the others (`Finset.orderIsoOfFin`). -/
def splitBy {nc : ℕ} (t : Fin nc → Bool) :
    Fin nc ≃ Fin (Finset.univ.filter fun c => t c = true).card ⊕
      Fin (Finset.univ.filter fun c => ¬ t c = true).card :=
  (Equiv.sumCompl fun c => t c = true).symm.trans
    (Equiv.sumCongr
      ((Equiv.subtypeEquivRight fun c => by simp).trans
        ((Finset.univ.filter fun c => t c = true).orderIsoOfFin rfl).toEquiv.symm)
      ((Equiv.subtypeEquivRight fun c => by simp).trans
        ((Finset.univ.filter fun c => ¬ t c = true).orderIsoOfFin rfl).toEquiv.symm))

theorem splitBy_symm_inl {nc : ℕ} (t : Fin nc → Bool) (i) : t ((splitBy t).symm (.inl i)) = true := by
  have := ((Finset.univ.filter fun c => t c = true).orderIsoOfFin rfl i).2
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
  simpa [splitBy] using this

theorem splitBy_symm_inr {nc : ℕ} (t : Fin nc → Bool) (i) : t ((splitBy t).symm (.inr i)) = false := by
  have := ((Finset.univ.filter fun c => ¬ t c = true).orderIsoOfFin rfl i).2
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_true] at this
  simpa [splitBy] using this

/-- **The routing of a split** of the claims into touching and passing ones: no touching claim,
one, or two or more. -/
def Routing.ofSplit {nc : ℕ} : {nt np : ℕ} → (Fin nc ≃ Fin nt ⊕ Fin np) → Routing nc
  | 0, np, s => ⟨0, np, .none (s.trans (Equiv.emptySum (Fin 0) _))⟩
  | 1, np, s => ⟨1, np, .single s⟩
  | n + 2, np, s => ⟨n + 2, np, .combine s (by omega)⟩

/-- **The touching claims of a split's routing are the split's.** -/
theorem Routing.ofSplit_inl {nc : ℕ} {P : Fin nc → Prop} :
    {nt np : ℕ} → (s : Fin nc ≃ Fin nt ⊕ Fin np) → (∀ i, P (s.symm (.inl i))) →
      ∀ i, P ((Routing.ofSplit s).route.split.symm (.inl i))
  | 0, _, _, _, i => i.elim0
  | 1, _, _, h, i => h i
  | _ + 2, _, _, h, i => h i

/-- **The passing claims of a split's routing are the split's.** -/
theorem Routing.ofSplit_inr {nc : ℕ} {P : Fin nc → Prop} :
    {nt np : ℕ} → (s : Fin nc ≃ Fin nt ⊕ Fin np) → (∀ i, P (s.symm (.inr i))) →
      ∀ i, P ((Routing.ofSplit s).route.split.symm (.inr i))
  | 0, np, s, h, i => by
    change P (((s.trans (Equiv.emptySum (Fin 0) (Fin np))).trans
      (Equiv.emptySum (Fin 0) (Fin np)).symm).symm (.inr (i : Fin np)))
    rw [show (s.trans (Equiv.emptySum (Fin 0) (Fin np))).trans
        (Equiv.emptySum (Fin 0) (Fin np)).symm = s from
      Equiv.ext fun x => (Equiv.emptySum (Fin 0) (Fin np)).symm_apply_apply _]
    exact h i
  | 1, _, _, h, i => h i
  | _ + 2, _, _, h, i => h i

/-- **A split's routing keeps the split's passing claims.** -/
theorem Routing.ofSplit_np {nc : ℕ} : {nt np : ℕ} → (s : Fin nc ≃ Fin nt ⊕ Fin np) →
    (Routing.ofSplit s).np = np
  | 0, _, _ => rfl
  | 1, _, _ => rfl
  | _ + 2, _, _ => rfl

/-- **A split's routing combines at most once.** -/
theorem Routing.combinations_ofSplit_le {nc : ℕ} :
    {nt np : ℕ} → (s : Fin nc ≃ Fin nt ⊕ Fin np) → (Routing.ofSplit s).route.combinations ≤ 1
  | 0, _, _ => Nat.zero_le 1
  | 1, _, _ => Nat.zero_le 1
  | _ + 2, _, _ => le_rfl

/-- **The routing of a test** (`TreeRows::stage`, the rows reading the region): the claims the
test accepts touch, the others pass; no combination when at most one touches. -/
def Routing.ofTouch {nc : ℕ} (t : Fin nc → Bool) : Routing nc := Routing.ofSplit (splitBy t)

/-- **The touching claims of a test's routing are the claims it accepts.** -/
theorem Routing.ofTouch_inl {nc : ℕ} (t : Fin nc → Bool) :
    ∀ i, t ((Routing.ofTouch t).route.split.symm (.inl i)) = true :=
  Routing.ofSplit_inl (P := fun c => t c = true) _ (splitBy_symm_inl t)

/-- **The passing claims of a test's routing are the claims it rejects.** -/
theorem Routing.ofTouch_inr {nc : ℕ} (t : Fin nc → Bool) :
    ∀ i, t ((Routing.ofTouch t).route.split.symm (.inr i)) = false :=
  Routing.ofSplit_inr (P := fun c => t c = false) _ (splitBy_symm_inr t)

/-- **The passing claims of a test's routing are the claims it rejects.** -/
theorem Routing.ofTouch_np {nc : ℕ} (t : Fin nc → Bool) :
    (Routing.ofTouch t).np = (Finset.univ.filter fun c => ¬ t c = true).card :=
  Routing.ofSplit_np _

/-- **A test's routing combines at most once.** -/
theorem Routing.combinations_ofTouch_le {nc : ℕ} (t : Fin nc → Bool) :
    (Routing.ofTouch t).route.combinations ≤ 1 :=
  Routing.combinations_ofSplit_le _

end StageRouting

namespace FieldProof.MaskedReduction

variable [Fintype ι] [DecidableEq ι] {Pub Wit : Type} {cells : Wit → ι → F} {nc nt np : ℕ}
  {p m e : ℕ} [ExpChar F p]

/-- **The stage's rows read the words, what the claim reads off the child, and the cells.** -/
theorem readsOnly_rows (S : Stage F ι p m d e ng Y) (cell : ι → Y)
    {c : AffineForm F (Y ⊕ PackedCoord ng d)} {T : Y ⊕ PackedCoord ng d → Prop}
    (hc : c.ReadsOnly T) (M : Fin d → F) :
    (S.rows cell c M 0).ReadsOnly (fun y => T (.inl y) ∨ ∃ i, cell i = y) ∧
      ∀ k : Fin d, (S.rows cell c M k.succ).ReadsOnly (fun y => (∃ g, S.word g = y) ∨ ∃ i, cell i = y) := by
  have hcell : ∀ a : AffineForm F ι, (a.rename cell).ReadsOnly
      (fun y => ∃ i, cell i = y) := fun a =>
    AffineForm.ReadsOnly.rename (S := fun _ => True) (AffineForm.ReadsOnly.of_forall fun _ => trivial)
      fun i _ => ⟨i, rfl⟩
  refine ⟨?_, fun k => ?_⟩
  · change (S.remainderRow cell c M).ReadsOnly _
    refine ((hc.restPart.mono fun y h => Or.inl h).sub ?_).add (AffineForm.ReadsOnly.ofConst _)
    exact AffineForm.ReadsOnly.sumFin fun k => (hcell _).mono fun y h => Or.inr h
  · change (S.measureRow cell c M k).ReadsOnly _
    refine (AffineForm.ReadsOnly.add ?_ ((hcell _).mono fun y h => Or.inr h)).sub
      (AffineForm.ReadsOnly.ofConst _)
    exact AffineForm.ReadsOnly.sumFin fun g =>
      (AffineForm.ReadsOnly.var (S := fun y => (∃ g, S.word g = y) ∨ ∃ i, cell i = y)
        (Or.inl ⟨g, rfl⟩)).smul _

omit [DecidableEq ι] in
/-- **The reordered claims read what they read.** -/
theorem ReadsOnly.reorder {Z : Type} [DecidableEq Z] {nc' : ℕ}
    {M : MaskedReduction F ι Pub Wit cells Z nc} {T : Fin nc → Z → Prop} (h : M.ReadsOnly T)
    (σ : Fin nc ≃ Fin nc') : (M.reorder σ).ReadsOnly fun c => T (σ.symm c) :=
  fun pb tr c => h pb tr (σ.symm c)

omit [DecidableEq ι] in
/-- **The zero claim reads nothing**; the other claims read what they read. -/
theorem ReadsOnly.prependZero {Z : Type} [DecidableEq Z]
    {M : MaskedReduction F ι Pub Wit cells Z np} {T : Fin np → Z → Prop} (h : M.ReadsOnly T) :
    M.prependZero.ReadsOnly (Fin.append (fun _ _ => False) T) := by
  intro pb tr c
  refine Fin.addCases (fun c => ?_) (fun i => ?_) c
  · change (Fin.append (fun _ => (0 : AffineForm F Z)) (M.claims pb tr) (Fin.castAdd np c)).ReadsOnly
      (Fin.append (fun _ _ => False) T (Fin.castAdd np c))
    rw [Fin.append_left, Fin.append_left]
    exact AffineForm.ReadsOnly.zero
  · change (Fin.append (fun _ => (0 : AffineForm F Z)) (M.claims pb tr) (Fin.natAdd 1 i)).ReadsOnly
      (Fin.append (fun _ _ => False) T (Fin.natAdd 1 i))
    rw [Fin.append_right, Fin.append_right]
    exact h pb tr i

variable [Fintype F] [DecidableEq F]

omit [DecidableEq ι] in
/-- **The combination reads what the first claims read**; the other claims read what they read. -/
theorem ReadsOnly.combineFirst {Z : Type} [DecidableEq Z]
    {M : MaskedReduction F ι Pub Wit cells Z (nt + np)} {T : Fin (nt + np) → Z → Prop}
    (h : M.ReadsOnly T) :
    M.combineFirst.ReadsOnly
      (Fin.append (fun _ z => ∃ i, T (Fin.castAdd np i) z) fun i => T (Fin.natAdd nt i)) := by
  intro pb tr c
  have hcl : M.combineFirst.claims pb tr = Fin.append
      (fun _ => GordieHowe.combination (oneValue tr.right)
        fun i => M.claims pb tr.left (Fin.castAdd np i))
      fun i => M.claims pb tr.left (Fin.natAdd nt i) := rfl
  rw [hcl]
  refine Fin.addCases (fun c => ?_) (fun i => ?_) c
  · rw [Fin.append_left, Fin.append_left]
    exact AffineForm.ReadsOnly.combination _ fun i =>
      (h pb tr.left (Fin.castAdd np i)).mono fun z hz => ⟨i, hz⟩
  · rw [Fin.append_right, Fin.append_right]
    exact h pb tr.left (Fin.natAdd nt i)

/-- **The supports after the measurement on the first claim**: the stage's rows read as
`readsOnly_rows` says for the first claim, each passing claim its coordinates off the child. -/
theorem ReadsOnly.measureHead {M : MaskedReduction F ι Pub Wit cells (Y ⊕ PackedCoord ng d) (1 + np)}
    {T : Fin (1 + np) → Y ⊕ PackedCoord ng d → Prop} (h : M.ReadsOnly T)
    (S : Stage F ι p m d e ng Y) (L : Level F ι Y) :
    (M.measureHead S L).ReadsOnly
      (Fin.append (Fin.cases (fun y => T (Fin.castAdd np 0) (.inl y) ∨ ∃ i, L.cell i = y)
          fun _ y => (∃ g, S.word g = y) ∨ ∃ i, L.cell i = y)
        fun i y => T (Fin.natAdd 1 i) (.inl y)) := by
  intro pb tr c
  have hcl : (M.measureHead S L).claims pb tr =
      Fin.append (S.rows L.cell (M.claims pb tr.left (Fin.castAdd np 0)) (oneValue tr.right))
        fun i => GordieHowe.restPart (M.claims pb tr.left (Fin.natAdd 1 i)) := rfl
  rw [hcl]
  refine Fin.addCases (fun c => ?_) (fun i => ?_) c
  · rw [Fin.append_left, Fin.append_left]
    have hr := readsOnly_rows S L.cell (h pb tr.left (Fin.castAdd np 0)) (oneValue tr.right)
    refine Fin.cases ?_ (fun k => ?_) c
    · exact hr.1
    · simpa only [Fin.cases_succ] using hr.2 k
  · rw [Fin.append_right, Fin.append_right]
    exact (h pb tr.left (Fin.natAdd 1 i)).restPart

omit [DecidableEq ι] in
/-- **The touching claims' combination reads what the touching claims read**; the claims after it
read what the passing claims read. -/
theorem ReadsOnly.touch {Z : Type} [DecidableEq Z] {M : MaskedReduction F ι Pub Wit cells Z nc}
    {T : Fin nc → Z → Prop} (h : M.ReadsOnly T) (R : StageRouting nc nt np) :
    (M.touch R).ReadsOnly (Fin.append (fun _ z => ∃ i, T (R.split.symm (.inl i)) z)
      fun i => T (R.split.symm (.inr i))) := by
  cases R with
  | none s =>
    refine (h.reorder s).prependZero.mono fun c z hz => ?_
    refine Fin.addCases (fun c hz => ?_) (fun i hz => ?_) c hz
    · rw [Fin.append_left] at hz
      exact hz.elim
    · rw [Fin.append_right] at hz
      rw [Fin.append_right]
      simpa only [StageRouting.split, Equiv.symm_trans_apply, Equiv.symm_symm,
        Equiv.emptySum_apply_inr] using hz
  | single s =>
    refine (h.reorder (StageRouting.single s).order).mono fun c z hz => ?_
    refine Fin.addCases (fun c hz => ?_) (fun i hz => ?_) c hz
    · rw [Fin.append_left]
      refine ⟨0, ?_⟩
      have hc : c = 0 := Subsingleton.elim _ _
      subst hc
      simpa [StageRouting.order, StageRouting.split] using hz
    · rw [Fin.append_right]
      rwa [StageRouting.order_symm_natAdd] at hz
  | combine s h2 =>
    refine ((h.reorder (StageRouting.combine s h2).order).combineFirst).mono fun c z hz => ?_
    refine Fin.addCases (fun c hz => ?_) (fun i hz => ?_) c hz
    · rw [Fin.append_left] at hz ⊢
      obtain ⟨i, hi⟩ := hz
      exact ⟨i, by simpa [StageRouting.order, StageRouting.split] using hi⟩
    · rw [Fin.append_right] at hz ⊢
      rwa [StageRouting.order_symm_natAdd] at hz

/-- **The supports after a routed stage** (`StageRouting.outSupport`). -/
theorem ReadsOnly.routedStage {M : MaskedReduction F ι Pub Wit cells (Y ⊕ PackedCoord ng d) nc}
    {T : Fin nc → Y ⊕ PackedCoord ng d → Prop} (h : M.ReadsOnly T) (R : StageRouting nc nt np)
    (S : Stage F ι p m d e ng Y) (L : Level F ι Y) :
    (M.routedStage R S L).ReadsOnly (R.outSupport T S.word L.cell) := by
  refine ((h.touch R).measureHead S L).mono fun c y hy => ?_
  refine Fin.addCases (fun c hy => ?_) (fun i hy => ?_) c hy
  · rw [Fin.append_left] at hy
    rw [StageRouting.outSupport, Fin.append_left]
    refine Fin.cases (fun hy => ?_) (fun k hy => ?_) c hy
    · simp only [Fin.cases_zero, Fin.append_left] at hy ⊢
      exact hy
    · simpa only [Fin.cases_succ] using hy
  · rw [Fin.append_right] at hy
    rw [StageRouting.outSupport, Fin.append_right]
    simpa only [Fin.append_right] using hy

end FieldProof.MaskedReduction

end GordieHowe
