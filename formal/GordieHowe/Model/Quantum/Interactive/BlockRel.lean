-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.SplitRestrict
public import GordieHowe.Model.Quantum.Interactive.ConstReg
public import GordieHowe.Model.QROM.ExpandCohBlock

@[expose] public section

/-!
# Adversaries with other Kraus maps on one block of a label

The hypotheses of the block lemmas (`GordieHowe/Model/QROM/ExpandCohBlock.lean`) for an adversary
with run-time kinds `A` and the same adversary with the Kraus maps `st'` (`AdaptiveIAlg.withStep`),
for a label `ℓ` of the workspace that the Kraus maps keep once set:

- `AdaptiveIAlg.tripPerm σ`: a permutation of the workspace, the request register and the response
  register, on the adversary's registers.
- `AdaptiveIAlg.BlockRel A st' ℓ G G' G₀ G₀' σ σ₀ r`: the two families move through their sets
  `G k` and `G' k` of well-formed registers and keep the blocks of `ℓ` there, and agree on the rows
  in `G k` and the columns in the set before whose label is `none` or `some r`, read along
  `tripPerm (σ k)` on the rows and the previous permutation on the columns (`QROM.OpRelOn₂`); the
  initial state is supported on `G₀` and `G₀'` and invariant along `σ₀` there; the permutations
  keep the label and the kinds and map the block of `G k` onto that of `G' k`.
- `AdaptiveIAlg.BlockNone A st' ℓ G G' G₀ G₀'`: the two families move through their sets, which
  have the same states of label `none`, and keep the blocks of `ℓ` there, agree on the rows in
  `G k` with label `none` from the columns in the set before with label `none`, and their rows of
  every block have the same overlaps from the columns with label `none` (`QROM.rowGram`).
- `AdaptiveIAlg.BlockRel.restrictAt`, `AdaptiveIAlg.BlockNone.restrictAt`,
  `AdaptiveIAlg.restrictAt_withStep`, `AdaptiveIAlg.restrictStep`, `AdaptiveIAlg.restrictTrip`,
  `AdaptiveIAlg.restrictSet`, `AdaptiveIAlg.prevSeq_restrictSet`, `AdaptiveIAlg.splitReg_tripPerm`,
  `AdaptiveIAlg.basePerm_symm_tripPerm`: the hypotheses at a fixed base part of a split oracle.
-/

open Matrix
open scoped BigOperators

namespace GordieHowe.Quantum

open GordieHowe.QROM KrausRel

namespace AdaptiveIAlg

variable {X Y Req Resp O L : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]

/-- **A permutation of the workspace, the request register and the response register** on the
adversary's registers; the query pairs are kept. -/
def tripPerm {W : Type} {n : ℕ} (σ : Equiv.Perm (W × Req × Option Resp)) :
    Equiv.Perm (DReg W n X Y Req Resp) :=
  σ.prodCongr (Equiv.refl _)

variable {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O)
  (st' : StepIdx A.slots A.post → KrausMap A.R (DReg A.W A.width X Y Req Resp)
    (DReg A.W A.width X Y Req Resp))

/-- **The adversary and the adversary with the Kraus maps `st'` on one block** of the label `ℓ`
of the workspace, along sets `G n` (for `A`) and `G' n` (for `st'`) and permutations `σ n` of the
workspace, the request and the response registers after step `n` (`G₀`, `G₀'`, `σ₀` of the initial
state): each family moves from its set before its step into its set after and keeps the blocks of
`ℓ` on its columns; on the rows in `G k` and the columns in the set before whose label is `none`
or `some r` they agree, read along `σ k` on the rows and the previous permutation on the columns;
the initial state is supported on `G₀` and `G₀'` and invariant along `σ₀` on its block; the
permutations keep the label and the kinds and map the block of `G n` onto that of `G' n`. -/
structure BlockRel (ℓ : A.W → Option L) (G G' : ℕ → Set (A.W × Req × Option Resp))
    (G₀ G₀' : Set (A.W × Req × Option Resp)) (σ : ℕ → Equiv.Perm (A.W × Req × Option Resp))
    (σ₀ : Equiv.Perm (A.W × Req × Option Resp)) (r : L) : Prop where
  /-- The permutations keep the label. -/
  label_eq : ∀ n x, ℓ (σ n x).1 = ℓ x.1
  /-- The initial permutation keeps the label. -/
  label_eq₀ : ∀ x, ℓ (σ₀ x).1 = ℓ x.1
  /-- The permutations keep the kinds. -/
  kind_eq : ∀ n x, A.kind (σ n x).1 = A.kind x.1
  /-- The permutations map the block of the sets of `A` onto that of the sets of `st'`. -/
  set_eq : ∀ n x, InBlock ℓ r x.1 → (σ n x ∈ G' n ↔ x ∈ G n)
  /-- The initial permutation maps the blocks of the initial sets onto each other. -/
  set_eq₀ : ∀ x, InBlock ℓ r x.1 → (σ₀ x ∈ G₀' ↔ x ∈ G₀)
  /-- `A`'s Kraus maps move through the sets. -/
  keepsSet : ∀ (k : StepIdx A.slots A.post) i, KeepsSet
    {d : DReg A.W A.width X Y Req Resp | d.1 ∈ prevSeq G G₀ k}
    {d : DReg A.W A.width X Y Req Resp | d.1 ∈ G k} ((A.step k).op i)
  /-- The other Kraus maps move through their sets. -/
  keepsSet' : ∀ (k : StepIdx A.slots A.post) i, KeepsSet
    {d : DReg A.W A.width X Y Req Resp | d.1 ∈ prevSeq G' G₀' k}
    {d : DReg A.W A.width X Y Req Resp | d.1 ∈ G' k} ((st' k).op i)
  /-- `A`'s Kraus maps keep the blocks on the columns of the set before their step. -/
  keeps : ∀ (k : StepIdx A.slots A.post) i, KeepsBlocksOn
    {d : DReg A.W A.width X Y Req Resp | d.1 ∈ prevSeq G G₀ k}
    (fun d : DReg A.W A.width X Y Req Resp => ℓ d.workspace) ((A.step k).op i)
  /-- The other Kraus maps keep the blocks on the columns of their set before their step. -/
  keeps' : ∀ (k : StepIdx A.slots A.post) i, KeepsBlocksOn
    {d : DReg A.W A.width X Y Req Resp | d.1 ∈ prevSeq G' G₀' k}
    (fun d : DReg A.W A.width X Y Req Resp => ℓ d.workspace) ((st' k).op i)
  /-- The two agree on the block, read along the permutations. -/
  hop : ∀ k : StepIdx A.slots A.post, OpRelOn₂ (tripPerm (σ k)) (tripPerm (prevSeq σ σ₀ k))
    {d : DReg A.W A.width X Y Req Resp | InBlock ℓ r d.workspace ∧ d.1 ∈ G k}
    {d : DReg A.W A.width X Y Req Resp | InBlock ℓ r d.workspace ∧ d.1 ∈ prevSeq G G₀ k}
    (A.step k) (st' k)
  /-- The initial state is supported on the initial set. -/
  init_supp : ∀ a b, A.init.mat a b ≠ 0 → a.1 ∈ G₀ ∧ b.1 ∈ G₀
  /-- The initial state is supported on the other initial set. -/
  init_supp' : ∀ a b, A.init.mat a b ≠ 0 → a.1 ∈ G₀' ∧ b.1 ∈ G₀'
  /-- The initial state is invariant on its block. -/
  init_eq : ∀ a b : DReg A.W A.width X Y Req Resp, a.1 ∈ G₀ → b.1 ∈ G₀ →
    InBlock ℓ r a.workspace → InBlock ℓ r b.workspace →
    A.init.mat (tripPerm σ₀ a) (tripPerm σ₀ b) = A.init.mat a b

/-- **The adversary and the adversary with the Kraus maps `st'` off the blocks** of the label
`ℓ`, along sets `G n` (for `A`) and `G' n` (for `st'`) after step `n` with the same states of
label `none` (`G₀`, `G₀'` of the initial state): each family moves from its set before its step into
its set after and keeps the blocks of `ℓ` on its columns, they agree on the rows in `G k` with
label `none` from the columns in the set before with label `none`, and their rows of every block
have the same overlaps from two columns in the set before with label `none`; the initial state is
supported on `G₀` and `G₀'`. -/
structure BlockNone [DecidableEq L] (ℓ : A.W → Option L)
    (G G' : ℕ → Set (A.W × Req × Option Resp)) (G₀ G₀' : Set (A.W × Req × Option Resp)) : Prop where
  /-- The sets of `A` and of `st'` have the same states of label `none`. -/
  none_eq : ∀ n x, ℓ x.1 = none → (x ∈ G' n ↔ x ∈ G n)
  /-- The initial sets have the same states of label `none`. -/
  none_eq₀ : ∀ x, ℓ x.1 = none → (x ∈ G₀' ↔ x ∈ G₀)
  /-- `A`'s Kraus maps move through the sets. -/
  keepsSet : ∀ (k : StepIdx A.slots A.post) i, KeepsSet
    {d : DReg A.W A.width X Y Req Resp | d.1 ∈ prevSeq G G₀ k}
    {d : DReg A.W A.width X Y Req Resp | d.1 ∈ G k} ((A.step k).op i)
  /-- The other Kraus maps move through their sets. -/
  keepsSet' : ∀ (k : StepIdx A.slots A.post) i, KeepsSet
    {d : DReg A.W A.width X Y Req Resp | d.1 ∈ prevSeq G' G₀' k}
    {d : DReg A.W A.width X Y Req Resp | d.1 ∈ G' k} ((st' k).op i)
  /-- `A`'s Kraus maps keep the blocks on the columns of the set before their step. -/
  keeps : ∀ (k : StepIdx A.slots A.post) i, KeepsBlocksOn
    {d : DReg A.W A.width X Y Req Resp | d.1 ∈ prevSeq G G₀ k}
    (fun d : DReg A.W A.width X Y Req Resp => ℓ d.workspace) ((A.step k).op i)
  /-- The other Kraus maps keep the blocks on the columns of their set before their step. -/
  keeps' : ∀ (k : StepIdx A.slots A.post) i, KeepsBlocksOn
    {d : DReg A.W A.width X Y Req Resp | d.1 ∈ prevSeq G' G₀' k}
    (fun d : DReg A.W A.width X Y Req Resp => ℓ d.workspace) ((st' k).op i)
  /-- The two agree on the rows in `G k` with label `none`, from the columns in the set before
  with label `none`. -/
  row_none_eq : ∀ (k : StepIdx A.slots A.post) i (a b : DReg A.W A.width X Y Req Resp),
    a.1 ∈ G k → b.1 ∈ prevSeq G G₀ k → ℓ a.workspace = none → ℓ b.workspace = none →
      (st' k).op i a b = (A.step k).op i a b
  /-- Their rows of every block have the same overlaps from two columns with label `none`. -/
  gram_eq : ∀ (k : StepIdx A.slots A.post) r (c d : DReg A.W A.width X Y Req Resp),
    c.1 ∈ prevSeq G G₀ k → d.1 ∈ prevSeq G G₀ k → ℓ c.workspace = none → ℓ d.workspace = none →
    rowGram (fun p : DReg A.W A.width X Y Req Resp => ℓ p.workspace) r (st' k) c d =
      rowGram (fun p : DReg A.W A.width X Y Req Resp => ℓ p.workspace) r (A.step k) c d
  /-- The initial state is supported on the initial set. -/
  init_supp : ∀ a b, A.init.mat a b ≠ 0 → a.1 ∈ G₀ ∧ b.1 ∈ G₀
  /-- The initial state is supported on the other initial set. -/
  init_supp' : ∀ a b, A.init.mat a b ≠ 0 → a.1 ∈ G₀' ∧ b.1 ∈ G₀'

/-! ### Other permutations agreeing on the sets -/

section CongrPerm

variable {A st'} {ℓ : A.W → Option L} {r : L}

/-- **A permutation agreeing with another on the block of a set maps that block as the other
does**, when both move the workspace alike. -/
theorem set_iff_of_agree {S S' : Set (A.W × Req × Option Resp)}
    {π π' : Equiv.Perm (A.W × Req × Option Resp)} (hπ : ∀ x, ℓ (π x).1 = ℓ x.1)
    (hW : ∀ x, (π' x).1 = (π x).1)
    (hS : ∀ x, InBlock ℓ r x.1 → x ∈ S → π' x = π x)
    (hset : ∀ x, InBlock ℓ r x.1 → (π x ∈ S' ↔ x ∈ S)) (x : A.W × Req × Option Resp)
    (hx : InBlock ℓ r x.1) : π' x ∈ S' ↔ x ∈ S := by
  constructor
  · intro h'
    have hy : InBlock ℓ r (π.symm (π' x)).1 := by
      have := hπ (π.symm (π' x))
      rw [Equiv.apply_symm_apply, hW, hπ] at this
      unfold InBlock at hx ⊢
      rwa [← this]
    have hyS : π.symm (π' x) ∈ S := (hset _ hy).1 (by rwa [Equiv.apply_symm_apply])
    have he : π' (π.symm (π' x)) = π' x := by
      rw [hS _ hy hyS, Equiv.apply_symm_apply]
    rwa [π'.injective he] at hyS
  · intro h'
    rw [hS x hx h']
    exact (hset x hx).2 h'

/-- **The block hypotheses along other permutations** that move the workspace as `σ n`, `σ₀` do
and agree with them on the blocks of `G n` and `G₀`. -/
theorem BlockRel.congrPerm {G G' : ℕ → Set (A.W × Req × Option Resp)}
    {G₀ G₀' : Set (A.W × Req × Option Resp)} {σ σ' : ℕ → Equiv.Perm (A.W × Req × Option Resp)}
    {σ₀ σ₀' : Equiv.Perm (A.W × Req × Option Resp)}
    (h : A.BlockRel st' ℓ G G' G₀ G₀' σ σ₀ r) (hW : ∀ n x, (σ' n x).1 = (σ n x).1)
    (hW₀ : ∀ x, (σ₀' x).1 = (σ₀ x).1)
    (hG : ∀ n x, InBlock ℓ r x.1 → x ∈ G n → σ' n x = σ n x)
    (hG₀ : ∀ x, InBlock ℓ r x.1 → x ∈ G₀ → σ₀' x = σ₀ x) :
    A.BlockRel st' ℓ G G' G₀ G₀' σ' σ₀' r where
  label_eq n x := by rw [hW]; exact h.label_eq n x
  label_eq₀ x := by rw [hW₀]; exact h.label_eq₀ x
  kind_eq n x := by rw [hW]; exact h.kind_eq n x
  set_eq n x hx := set_iff_of_agree (h.label_eq n) (hW n) (hG n) (h.set_eq n) x hx
  set_eq₀ x hx := set_iff_of_agree h.label_eq₀ hW₀ hG₀ h.set_eq₀ x hx
  keepsSet := h.keepsSet
  keepsSet' := h.keepsSet'
  keeps := h.keeps
  keeps' := h.keeps'
  hop k i a b ha hb := by
    have hpa : tripPerm (σ' k) a = tripPerm (σ k) a := by
      simp only [tripPerm, Equiv.prodCongr_apply, Prod.map, hG k a.1 ha.1 ha.2]
    have hpb : tripPerm (prevSeq σ' σ₀' k) b = tripPerm (prevSeq σ σ₀ k) b := by
      have hb2 := hb.2
      simp only [prevSeq] at hb2 ⊢
      split_ifs at hb2 ⊢
      · simp only [tripPerm, Equiv.prodCongr_apply, Prod.map, hG₀ b.1 hb.1 hb2]
      · simp only [tripPerm, Equiv.prodCongr_apply, Prod.map, hG _ b.1 hb.1 hb2]
    rw [hpa, hpb]
    exact h.hop k i a b ha hb
  init_supp := h.init_supp
  init_supp' := h.init_supp'
  init_eq a b haG hbG ha hb := by
    have hpa : tripPerm σ₀' a = tripPerm σ₀ a := by
      simp only [tripPerm, Equiv.prodCongr_apply, Prod.map, hG₀ a.1 ha haG]
    have hpb : tripPerm σ₀' b = tripPerm σ₀ b := by
      simp only [tripPerm, Equiv.prodCongr_apply, Prod.map, hG₀ b.1 hb hbG]
    rw [hpa, hpb]
    exact h.init_eq a b haG hbG ha hb

end CongrPerm

/-! ### At a fixed base part of a split oracle -/

section Restrict

variable {Y₁ Y₂ : Type} [Fintype Y₁] [DecidableEq Y₁] [Fintype Y₂] [DecidableEq Y₂] [AddGroup Y]
  [AddGroup Y₁] [AddGroup Y₂] (sp : Y ≃+ Y₁ × Y₂) (H₁ : X → Y₁)

/-- **The Kraus maps `st'` at the base part `H₁`**, as `restrictAt` reads `A`'s. -/
def restrictStep : StepIdx (A.restrictAt sp H₁).slots (A.restrictAt sp H₁).post →
    KrausMap (A.restrictAt sp H₁).R (DReg (A.restrictAt sp H₁).W (A.restrictAt sp H₁).width X Y₂
      Req Resp) (DReg (A.restrictAt sp H₁).W (A.restrictAt sp H₁).width X Y₂ Req Resp) :=
  fun k => ((st' k).reindex (splitReg sp A.W A.width X Req Resp).symm).permConj (Equiv.refl _)
    (basePerm H₁ (A.stepOn k) A.width Req Resp)

/-- **The adversary with the Kraus maps `st'` at the base part** is the adversary at the base part
with the Kraus maps `restrictStep`. -/
theorem restrictAt_withStep :
    (A.withStep st').restrictAt sp H₁ = (A.restrictAt sp H₁).withStep (A.restrictStep st' sp H₁) :=
  rfl

/-- **A permutation of `A`'s workspace, request and response at the base part**, the `Y₁`-parts
of the answers kept. -/
def restrictTrip (σ : Equiv.Perm (A.W × Req × Option Resp)) :
    Equiv.Perm ((A.restrictAt sp H₁).W × Req × Option Resp) where
  toFun x := ((((σ (x.1.1, x.2)).1, x.1.2), (σ (x.1.1, x.2)).2))
  invFun x := ((((σ.symm (x.1.1, x.2)).1, x.1.2), (σ.symm (x.1.1, x.2)).2))
  left_inv x := by
    obtain ⟨⟨w, ys⟩, q⟩ := x
    simp
  right_inv x := by
    obtain ⟨⟨w, ys⟩, q⟩ := x
    simp

theorem splitReg_tripPerm (σ : Equiv.Perm (A.W × Req × Option Resp))
    (d : DReg (A.restrictAt sp H₁).W A.width X Y₂ Req Resp) :
    splitReg sp A.W A.width X Req Resp (tripPerm (A.restrictTrip sp H₁ σ) d) =
      tripPerm σ (splitReg sp A.W A.width X Req Resp d) :=
  rfl

theorem basePerm_symm_tripPerm (σ : Equiv.Perm (A.W × Req × Option Resp))
    (hk : ∀ x, A.kind (σ x).1 = A.kind x.1) (k : StepIdx A.slots A.post)
    (d : DReg (A.restrictAt sp H₁).W A.width X Y₂ Req Resp) :
    (basePerm H₁ (A.stepOn k) A.width Req Resp).symm (tripPerm (A.restrictTrip sp H₁ σ) d) =
      tripPerm (A.restrictTrip sp H₁ σ) ((basePerm H₁ (A.stepOn k) A.width Req Resp).symm d) := by
  obtain ⟨⟨⟨w, ys⟩, q, a⟩, p⟩ := d
  have hs : A.stepOn k (σ (w, q, a)).1 = A.stepOn k w := by
    simp only [stepOn, hk]
  show (((((σ (w, q, a)).1, fun j => if A.stepOn k (σ (w, q, a)).1 then ys j - H₁ (p j).1
      else ys j), (σ (w, q, a)).2), p) : DReg (A.restrictAt sp H₁).W A.width X Y₂ Req Resp) =
    ((((σ (w, q, a)).1, fun j => if A.stepOn k w then ys j - H₁ (p j).1 else ys j),
      (σ (w, q, a)).2), p)
  rw [hs]

variable {A st'}

/-- **A set of `A`'s workspace, request and response read at the base part.** -/
def restrictSet (S : Set (A.W × Req × Option Resp)) :
    Set ((A.restrictAt sp H₁).W × Req × Option Resp) :=
  {x | (x.1.1, x.2) ∈ S}

theorem prevSeq_restrictSet (G : ℕ → Set (A.W × Req × Option Resp))
    (G₀ : Set (A.W × Req × Option Resp)) (n : ℕ) :
    prevSeq (fun n => A.restrictSet sp H₁ (G n)) (A.restrictSet sp H₁ G₀) n =
      A.restrictSet sp H₁ (prevSeq G G₀ n) := by
  simp only [prevSeq]
  split_ifs <;> rfl

/-- **The block hypotheses at a fixed base part**: those of the adversary at the base part, with
the label, the sets and the permutations read on `A`'s part of the workspace. -/
theorem BlockRel.restrictAt {ℓ : A.W → Option L} {G G' : ℕ → Set (A.W × Req × Option Resp)}
    {G₀ G₀' : Set (A.W × Req × Option Resp)} {σ : ℕ → Equiv.Perm (A.W × Req × Option Resp)}
    {σ₀ : Equiv.Perm (A.W × Req × Option Resp)} {r : L}
    (h : A.BlockRel st' ℓ G G' G₀ G₀' σ σ₀ r) :
    (A.restrictAt sp H₁).BlockRel (A.restrictStep st' sp H₁) (fun w => ℓ w.1)
      (fun n => A.restrictSet sp H₁ (G n)) (fun n => A.restrictSet sp H₁ (G' n))
      (A.restrictSet sp H₁ G₀) (A.restrictSet sp H₁ G₀')
      (fun n => A.restrictTrip sp H₁ (σ n)) (A.restrictTrip sp H₁ σ₀) r where
  label_eq n x := h.label_eq n (x.1.1, x.2)
  label_eq₀ x := h.label_eq₀ (x.1.1, x.2)
  kind_eq n x := h.kind_eq n (x.1.1, x.2)
  set_eq n x hx := h.set_eq n (x.1.1, x.2) hx
  set_eq₀ x hx := h.set_eq₀ (x.1.1, x.2) hx
  keepsSet k i a b hb hne := by
    rw [prevSeq_restrictSet] at hb
    exact h.keepsSet k i _ _ hb hne
  keepsSet' k i a b hb hne := by
    rw [prevSeq_restrictSet] at hb
    exact h.keepsSet' k i _ _ hb hne
  keeps k i r' a b hbG hb hne := by
    rw [prevSeq_restrictSet] at hbG
    exact h.keeps k i r' _ _ hbG hb hne
  keeps' k i r' a b hbG hb hne := by
    rw [prevSeq_restrictSet] at hbG
    exact h.keeps' k i r' _ _ hbG hb hne
  hop k i a b ha hb := by
    have hp : prevSeq (fun n => A.restrictTrip sp H₁ (σ n)) (A.restrictTrip sp H₁ σ₀) k =
        A.restrictTrip sp H₁ (prevSeq σ σ₀ k) := by
      simp only [prevSeq]
      split_ifs <;> rfl
    rw [hp]
    have hb' := hb
    simp only [Set.mem_ofPred_eq, prevSeq_restrictSet] at hb'
    show (st' k).op i (splitReg sp A.W A.width X Req Resp
        ((basePerm H₁ (A.stepOn k) A.width Req Resp).symm
          (tripPerm (A.restrictTrip sp H₁ (σ k)) a)))
      (splitReg sp A.W A.width X Req Resp (tripPerm (A.restrictTrip sp H₁ (prevSeq σ σ₀ k)) b)) =
      (A.step k).op i (splitReg sp A.W A.width X Req Resp
        ((basePerm H₁ (A.stepOn k) A.width Req Resp).symm a))
        (splitReg sp A.W A.width X Req Resp b)
    rw [basePerm_symm_tripPerm A sp H₁ (σ k) (h.kind_eq k) k a]
    exact h.hop k i (splitReg sp A.W A.width X Req Resp
      ((basePerm H₁ (A.stepOn k) A.width Req Resp).symm a)) (splitReg sp A.W A.width X Req Resp b)
      ha hb'
  init_supp a b hab := h.init_supp (splitReg sp A.W A.width X Req Resp a)
    (splitReg sp A.W A.width X Req Resp b) hab
  init_supp' a b hab := h.init_supp' (splitReg sp A.W A.width X Req Resp a)
    (splitReg sp A.W A.width X Req Resp b) hab
  init_eq a b haG hbG ha hb :=
    h.init_eq (splitReg sp A.W A.width X Req Resp a) (splitReg sp A.W A.width X Req Resp b) haG hbG
      ha hb

/-- **The `none`-block hypotheses at a fixed base part.** -/
theorem BlockNone.restrictAt [DecidableEq L] {ℓ : A.W → Option L}
    {G G' : ℕ → Set (A.W × Req × Option Resp)} {G₀ G₀' : Set (A.W × Req × Option Resp)}
    (h : A.BlockNone st' ℓ G G' G₀ G₀') :
    (A.restrictAt sp H₁).BlockNone (A.restrictStep st' sp H₁) (fun w => ℓ w.1)
      (fun n => A.restrictSet sp H₁ (G n)) (fun n => A.restrictSet sp H₁ (G' n))
      (A.restrictSet sp H₁ G₀) (A.restrictSet sp H₁ G₀') where
  none_eq n x hx := h.none_eq n (x.1.1, x.2) hx
  none_eq₀ x hx := h.none_eq₀ (x.1.1, x.2) hx
  keepsSet k i a b hb hne := by
    rw [prevSeq_restrictSet] at hb
    exact h.keepsSet k i _ _ hb hne
  keepsSet' k i a b hb hne := by
    rw [prevSeq_restrictSet] at hb
    exact h.keepsSet' k i _ _ hb hne
  keeps k i r' a b hbG hb hne := by
    rw [prevSeq_restrictSet] at hbG
    exact h.keeps k i r' _ _ hbG hb hne
  keeps' k i r' a b hbG hb hne := by
    rw [prevSeq_restrictSet] at hbG
    exact h.keeps' k i r' _ _ hbG hb hne
  row_none_eq k i _ _ haG hbG ha hb := by
    rw [prevSeq_restrictSet] at hbG
    exact h.row_none_eq k i _ _ haG hbG ha hb
  init_supp a b hab := h.init_supp (splitReg sp A.W A.width X Req Resp a)
    (splitReg sp A.W A.width X Req Resp b) hab
  init_supp' a b hab := h.init_supp' (splitReg sp A.W A.width X Req Resp a)
    (splitReg sp A.W A.width X Req Resp b) hab
  gram_eq k r c d hcG hdG hc hd := by
    rw [prevSeq_restrictSet] at hcG hdG
    -- the rows read through `basePerm` and `splitReg`, a bijection keeping the label
    set f := (basePerm H₁ (A.stepOn k) A.width Req Resp).symm.trans
      (splitReg sp A.W A.width X Req Resp)
    have hre : ∀ F : DReg A.W A.width X Y Req Resp → ℂ,
        ∑ a ∈ Finset.univ.filter (fun a : DReg (A.restrictAt sp H₁).W A.width X Y₂ Req Resp =>
          ℓ a.workspace.1 = some r), F (f a) =
        ∑ x ∈ Finset.univ.filter (fun x : DReg A.W A.width X Y Req Resp =>
          ℓ x.workspace = some r), F x := fun F => by
      rw [Finset.sum_filter, Finset.sum_filter, ← Equiv.sum_comp f]
      rfl
    have hg := h.gram_eq k r (splitReg sp A.W A.width X Req Resp c)
      (splitReg sp A.W A.width X Req Resp d) hcG hdG hc hd
    show ∑ i, ∑ a ∈ Finset.univ.filter (fun a : DReg (A.restrictAt sp H₁).W A.width X Y₂ Req Resp =>
        ℓ a.workspace.1 = some r), (st' k).op i (f a) (splitReg sp A.W A.width X Req Resp c) *
          star ((st' k).op i (f a) (splitReg sp A.W A.width X Req Resp d)) =
      ∑ i, ∑ a ∈ Finset.univ.filter (fun a : DReg (A.restrictAt sp H₁).W A.width X Y₂ Req Resp =>
        ℓ a.workspace.1 = some r), (A.step k).op i (f a) (splitReg sp A.W A.width X Req Resp c) *
          star ((A.step k).op i (f a) (splitReg sp A.W A.width X Req Resp d))
    refine (Finset.sum_congr rfl fun i _ => hre fun x =>
      (st' k).op i x (splitReg sp A.W A.width X Req Resp c) *
        star ((st' k).op i x (splitReg sp A.W A.width X Req Resp d))).trans ?_
    refine Eq.trans ?_ (Finset.sum_congr rfl fun i _ => hre fun x =>
      (A.step k).op i x (splitReg sp A.W A.width X Req Resp c) *
        star ((A.step k).op i x (splitReg sp A.W A.width X Req Resp d))).symm
    exact hg

end Restrict

end AdaptiveIAlg

end GordieHowe.Quantum
