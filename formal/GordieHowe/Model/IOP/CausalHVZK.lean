-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.IOP.CausalComplete
public import GordieHowe.Model.IOP.HVZK
public import GordieHowe.Model.IOP.Append
public import GordieHowe.Model.IOP.Completeness

@[expose] public section

/-!
# Honest-verifier zero knowledge of series–parallel compositions

The verifier reads each leaf's prover messages through message views (`CausalViews`), as an IOP
verifier reads a protocol's (`IOP`, `MessageView`). Its view of a composite transcript
(`CausalView`) is the composite challenges and, of every leaf's prover message, the entries at the
positions queried under the composite challenges.

`GordieHowe.IOP.CausalHVZK` is CY24 Definition 23.1.8 (p. 260; `IOP.HVZK`) for a composite: the honest
verifier's view (uniform challenges, uniform prover coins) and the law of a joint simulator's
output are at total variation distance at most `δ`. The simulator reads a public part `pub x` of
the statement; for a whole composite `pub` is the identity, and for the second part of a sequence
it is the statement with the first part's view (`GordieHowe.IOP.CausalHVZK.seq`).

* `GordieHowe.IOP.CausalHVZK.seq`: errors add. The composite simulator (`CausalJointSimulator.seq`) runs the
  first part's simulator and then the second part's on the statement and the simulated first-part
  view, so it never needs the first part's prover messages.
* `GordieHowe.IOP.CausalHVZK.par`, `GordieHowe.IOP.CausalHVZK.nodeN`: parts that do not read each other's transcripts, side
  by side or one after the other; errors add (`GordieHowe.IOP.CausalJointSimulator.par`).
* `GordieHowe.IOP.CausalHVZK.ofIOP`: an IOP that is zero knowledge in the form `IOP.HVZK` is so as a
  one-component composite.
-/

namespace GordieHowe.IOP

open scoped NNReal BigOperators
open SPTerm

namespace PMF

/-- **The uniform law pushed along an equivalence** is uniform. About Mathlib objects only; a
candidate for `GordieHowe/Foundations/ToMathlib/PMFTV.lean`. -/
theorem uniformOfFintype_map_equiv {α β : Type*} [Fintype α] [Nonempty α] [Fintype β]
    [Nonempty β] (e : α ≃ β) : (PMF.uniformOfFintype α).map e = PMF.uniformOfFintype β := by
  classical
  ext b
  rw [PMF.map_apply, tsum_eq_single (e.symm b) fun a ha => by
    simp only [ite_eq_right_iff]
    rintro rfl
    exact absurd (e.symm_apply_apply a).symm ha]
  simp [PMF.uniformOfFintype_apply, Fintype.card_congr e]

end PMF

variable {ι : Type} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}

variable (P) in
/-- **How the verifier reads every leaf's prover messages**: for each leaf and prover round, a
message view (`MessageView`) whose queries depend on the composite challenges (an oracle sent by
one leaf may be queried at positions drawn by a later leaf, as a commitment of the prefix is opened
at the positions of a join part's Ligero test). -/
structure CausalViews (t : SPTerm ι) where
  /-- The positions of each leaf's prover messages. -/
  Idx : (p : t.Leaf) → (P p.label).MessageIdx → Type
  /-- The entry types of each leaf's prover messages. -/
  Ans : (p : t.Leaf) → (P p.label).MessageIdx → Type
  /-- The message views. -/
  msg : ∀ p (i : (P p.label).MessageIdx),
    MessageView ((P p.label).Type i.1) (Chs P t) (Idx p i) (Ans p i)


/-- **The verifier's view of a composite transcript**: the composite challenges and the seen
entries of every leaf's prover messages. -/
@[ext]
structure CausalView {t : SPTerm ι} (M : CausalViews P t) where
  /-- The challenges. -/
  challenges : Chs P t
  /-- The seen entries of every leaf's prover messages. -/
  entries : ∀ p (i : (P p.label).MessageIdx), M.Idx p i → Option (M.Ans p i)

namespace CausalViews

variable {t : SPTerm ι}

/-- The verifier's view of a composite transcript: its challenges and, of every leaf's prover
messages, the entries at the positions queried under the composite challenges. -/
def view (M : CausalViews P t) (f : FullTr P t) : CausalView M :=
  ⟨f.challenges, fun p i => (M.msg p i).see f.challenges (f p i.1)⟩

end CausalViews

/-- The message views of a node from those of its subterms. -/
def CausalViews.node {k : Comp} {a b : SPTerm ι} (M₁ : CausalViews P a) (M₂ : CausalViews P b) :
    CausalViews P (node k a b) where
  Idx
    | .left p => M₁.Idx p
    | .right p => M₂.Idx p
  Ans
    | .left p => M₁.Ans p
    | .right p => M₂.Ans p
  msg
    | .left p => fun i => (M₁.msg p i).comap Chs.left
    | .right p => fun i => (M₂.msg p i).comap Chs.right

/-- The view of a node from the views of its subterms. -/
def CausalView.join {k : Comp} {a b : SPTerm ι} {M₁ : CausalViews P a} {M₂ : CausalViews P b}
    (v₁ : CausalView M₁) (v₂ : CausalView M₂) : CausalView (CausalViews.node (k := k) M₁ M₂) where
  challenges := Chs.equivNode.symm (v₁.challenges, v₂.challenges)
  entries
    | .left p => v₁.entries p
    | .right p => v₂.entries p

/-- The view of a joined transcript is the join of the views. -/
theorem CausalViews.view_join {k : Comp} {a b : SPTerm ι} (M₁ : CausalViews P a)
    (M₂ : CausalViews P b) (f₁ : FullTr P a) (f₂ : FullTr P b) :
    (CausalViews.node (k := k) M₁ M₂).view (FullTr.join f₁ f₂) =
      (M₁.view f₁).join (M₂.view f₂) := by
  ext1
  · funext c
    obtain ⟨p, i⟩ := c
    cases p <;> rfl
  · funext p
    cases p <;> rfl

section HVZK

variable [∀ j (i : (P j).ChallengeIdx), Fintype ((P j).Challenge i)]
  [∀ j (i : (P j).ChallengeIdx), Nonempty ((P j).Challenge i)] {t : SPTerm ι} {Stmt Wit : Type}
  {R : Type} [Fintype R] [Nonempty R]

/-- **The honest verifier's view** of a composite on `x` with the witness `w` (CY24 Definition
23.1.7, p. 260): uniform challenges together with what the verifier sees of the run of
`honest w ρ` at uniform prover coins `ρ`. -/
noncomputable def CausalViews.honestView (M : CausalViews P t)
    (honest : Wit → R → CausalProver P t Stmt) (x : Stmt) (w : Wit) : PMF (CausalView M) :=
  (PMF.uniformOfFintype (Chs P t)).bind fun ch =>
    (PMF.uniformOfFintype R).map fun ρ => M.view ((honest w ρ).run x ch)

/-- The honest view as one uniform draw of the challenges and the coins. -/
theorem CausalViews.honestView_eq_map (M : CausalViews P t)
    (honest : Wit → R → CausalProver P t Stmt) (x : Stmt) (w : Wit) :
    M.honestView honest x w = (PMF.uniformOfFintype (Chs P t × R)).map fun u =>
      M.view ((honest w u.2).run x u.1) := by
  rw [CausalViews.honestView, PMF.uniformOfFintype_prod_eq_bind, PMF.map_bind]
  congr 1
  funext ch
  rw [PMF.map_comp]
  rfl

/-- **A joint simulator** for the views `M` on public statements `Pub` (CY24 Definition 23.1.8;
`IOP.JointSimulator`): from the public statement and its own uniform coins, a composite view
(challenges included). It must run in polynomial time; every value is a named definition whose
docstring has a "Running time" paragraph arguing polynomial running time (`IOP.JointSimulator`),
checked by the Lean lint `scripts/CostLint.lean`. -/
structure CausalJointSimulator (M : CausalViews P t) (Pub : Type) where
  /-- The simulator's coins. -/
  Coins : Type
  [fintype : Fintype Coins]
  [nonempty : Nonempty Coins]
  /-- The simulated view. -/
  sim : Pub → Coins → CausalView M

attribute [instance] CausalJointSimulator.fintype CausalJointSimulator.nonempty

/-- The law of the simulated view on the public statement `y`. -/
noncomputable def CausalJointSimulator.law {M : CausalViews P t} {Pub : Type}
    (S : CausalJointSimulator M Pub) (y : Pub) : PMF (CausalView M) :=
  (PMF.uniformOfFintype S.Coins).map (S.sim y)

/-- **Honest-verifier zero knowledge of a composite at an error of the statement** (CY24
Definition 23.1.8; the paper's `def:hvzk`, an error of the statement): for every pair `(x, w)` of
`rel`, the honest view and the law of the simulator `S` on the public part `pub x` are at total
variation distance at most `δ x`. -/
def CausalHVZKStmt (M : CausalViews P t) (rel : Set (Stmt × Wit))
    (honest : Wit → R → CausalProver P t Stmt) {Pub : Type} (pub : Stmt → Pub)
    (S : CausalJointSimulator M Pub) (δ : Stmt → ℝ≥0) : Prop :=
  ∀ x w, (x, w) ∈ rel → PMF.tvDist (M.honestView honest x w) (S.law (pub x)) ≤ δ x

/-- **Honest-verifier zero knowledge of a composite** (CY24 Definition 23.1.8) at the error `δ` at
every statement (`CausalHVZKStmt` at the constant error). -/
abbrev CausalHVZK (M : CausalViews P t) (rel : Set (Stmt × Wit))
    (honest : Wit → R → CausalProver P t Stmt) {Pub : Type} (pub : Stmt → Pub)
    (S : CausalJointSimulator M Pub) (δ : ℝ≥0) : Prop :=
  CausalHVZKStmt M rel honest pub S fun _ => δ

/-- **A joint simulator that draws the challenges uniformly**, then runs `simAt` on the public
statement, the challenges and its own coins.

Running time: one uniform draw of the challenges (one per challenge round of every leaf) and one run
of `simAt` (polynomial by the instance's own Running time paragraph). This running time is argued
here, not proved in Lean. -/
def CausalJointSimulator.ofChallenges {M : CausalViews P t} {Pub : Type} (S0 : Type) [Fintype S0]
    [Nonempty S0] (simAt : Pub → Chs P t → S0 → CausalView M) : CausalJointSimulator M Pub where
  Coins := Chs P t × S0
  sim y c := simAt y c.1 c.2

omit [∀ j (i : (P j).ChallengeIdx), Fintype ((P j).Challenge i)]
  [∀ j (i : (P j).ChallengeIdx), Nonempty ((P j).Challenge i)] [Fintype R] [Nonempty R] in
open Classical in
/-- **Two mixtures over a uniform index that agree off an event** are at total variation distance
at most the event's probability. About Mathlib objects only. -/
theorem tvDist_uniform_bind_le {α β : Type} [Fintype α] [Nonempty α] (k₁ k₂ : α → PMF β)
    (bad : α → Prop) (h : ∀ a, ¬ bad a → k₁ a = k₂ a) :
    PMF.tvDist ((PMF.uniformOfFintype α).bind k₁) ((PMF.uniformOfFintype α).bind k₂) ≤
      (Pr[a ← α : bad a]).toReal := by
  refine (PMF.tvDist_bind_left_le' _ _ _).trans ?_
  rw [tsum_fintype]
  calc ∑ a, ((PMF.uniformOfFintype α) a).toReal * PMF.tvDist (k₁ a) (k₂ a)
      ≤ ∑ a, ((PMF.uniformOfFintype α) a).toReal * (if bad a then 1 else 0) :=
        Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (by
          split_ifs with hb
          · exact PMF.tvDist_le_one _ _
          · rw [h a hb, PMF.tvDist_self]) ENNReal.toReal_nonneg
    _ = 𝔼 a : α, (if bad a then (1 : ℝ) else 0) := by
        rw [Fintype.expect_eq_sum_div_card, Finset.sum_div]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]
        ring
    _ = (Pr[a ← α : bad a]).toReal := (toReal_probUniform _).symm

open Classical in
/-- **Zero knowledge off exceptions** (the composite form of `IOP.HVZKOffExceptions.hvzk`): if
outside an exception event of probability at most `δ x` at the statement `x` the honest view at the
challenges `ch` has the law of `simAt x ch`, the honest prover is zero knowledge at the simulator
drawing the challenges uniformly (`CausalJointSimulator.ofChallenges`) with error `δ`. -/
theorem CausalHVZK.of_offExceptions {M : CausalViews P t} {rel : Set (Stmt × Wit)}
    {honest : Wit → R → CausalProver P t Stmt} {S0 : Type} [Fintype S0] [Nonempty S0]
    {simAt : Stmt → Chs P t → S0 → CausalView M} {δ : Stmt → ℝ≥0} (bad : Stmt → Wit → Chs P t → Prop)
    (bad_le : ∀ x w, (x, w) ∈ rel → Pr[ch ← Chs P t : bad x w ch] ≤ δ x)
    (simulates : ∀ x w, (x, w) ∈ rel → ∀ ch, ¬ bad x w ch →
      (fun ρ => M.view ((honest w ρ).run x ch)) =ᵈ simAt x ch) :
    CausalHVZKStmt M rel honest id (CausalJointSimulator.ofChallenges S0 simAt) δ := by
  intro x w hw
  have hS : (CausalJointSimulator.ofChallenges S0 simAt).law x =
      (PMF.uniformOfFintype (Chs P t)).bind fun ch => (PMF.uniformOfFintype S0).map (simAt x ch) := by
    change (PMF.uniformOfFintype (Chs P t × S0)).map (fun c => simAt x c.1 c.2) = _
    rw [PMF.uniformOfFintype_prod_eq_bind, PMF.map_bind]
    congr 1
    funext ch
    rw [PMF.map_comp]
    rfl
  change PMF.tvDist (M.honestView honest x w) ((CausalJointSimulator.ofChallenges S0 simAt).law x) ≤ _
  rw [hS, CausalViews.honestView]
  refine (tvDist_uniform_bind_le _ _ (bad x w) fun ch hb => ?_).trans ?_
  · have hs := simulates x w hw ch hb
    simp only [IdentDistrib] at hs
    exact hs
  · exact ENNReal.toReal_le_of_le_ofReal (δ x).2 ((bad_le x w hw).trans (by simp))

open Classical in
/-- **Zero knowledge off exceptions depending on part of the coins**: for an honest prover whose
coins are a pair `(ω, ρ)`, if outside an exception event of `ω` and the challenges `ch`, of
probability at most `δ x` over uniform `ω` and `ch` at the statement `x`, the honest view at `ω` and `ch` over uniform
`ρ` has the law of `simAt x ch`, the honest prover is zero knowledge at the simulator drawing the
challenges uniformly (`CausalJointSimulator.ofChallenges`) with error `δ`. The exception may read
the coins `ω`, as the completeness events of a program with randomized functions read their
coins. -/
theorem CausalHVZK.of_offExceptions_coins {M : CausalViews P t} {rel : Set (Stmt × Wit)}
    {Ω R' : Type} [Fintype Ω] [Nonempty Ω] [Fintype R'] [Nonempty R']
    {honest : Wit → Ω → R' → CausalProver P t Stmt} {S0 : Type} [Fintype S0] [Nonempty S0]
    {simAt : Stmt → Chs P t → S0 → CausalView M} {δ : Stmt → ℝ≥0}
    (bad : Stmt → Wit → Ω → Chs P t → Prop)
    (bad_le : ∀ x w, (x, w) ∈ rel → Pr[u ← (Ω × Chs P t) : bad x w u.1 u.2] ≤ δ x)
    (simulates : ∀ x w, (x, w) ∈ rel → ∀ ω ch, ¬ bad x w ω ch →
      (fun ρ => M.view ((honest w ω ρ).run x ch)) =ᵈ simAt x ch) :
    CausalHVZKStmt M rel (fun w (ρ : Ω × R') => honest w ρ.1 ρ.2) id
      (CausalJointSimulator.ofChallenges S0 simAt) δ := by
  intro x w hw
  have hS : (CausalJointSimulator.ofChallenges S0 simAt).law x =
      (PMF.uniformOfFintype (Chs P t)).bind fun ch => (PMF.uniformOfFintype S0).map (simAt x ch) := by
    change (PMF.uniformOfFintype (Chs P t × S0)).map (fun c => simAt x c.1 c.2) = _
    rw [PMF.uniformOfFintype_prod_eq_bind, PMF.map_bind]
    congr 1
    funext ch
    rw [PMF.map_comp]
    rfl
  have hin : ∀ ch, PMF.tvDist
      ((PMF.uniformOfFintype (Ω × R')).map fun ρ => M.view ((honest w ρ.1 ρ.2).run x ch))
      ((PMF.uniformOfFintype S0).map (simAt x ch)) ≤ (Pr[ω ← Ω : bad x w ω ch]).toReal := by
    intro ch
    have e1 : ((PMF.uniformOfFintype (Ω × R')).map fun ρ => M.view ((honest w ρ.1 ρ.2).run x ch)) =
        (PMF.uniformOfFintype Ω).bind fun ω =>
          (PMF.uniformOfFintype R').map fun ρ => M.view ((honest w ω ρ).run x ch) := by
      rw [PMF.uniformOfFintype_prod_eq_bind, PMF.map_bind]
      congr 1
      funext ω
      rw [PMF.map_comp]
      rfl
    rw [e1, ← PMF.bind_const (PMF.uniformOfFintype Ω) ((PMF.uniformOfFintype S0).map (simAt x ch))]
    refine tvDist_uniform_bind_le _ _ (fun ω => bad x w ω ch) fun ω hb => ?_
    have hs := simulates x w hw ω ch hb
    simp only [IdentDistrib] at hs
    exact hs
  change PMF.tvDist (M.honestView _ x w) ((CausalJointSimulator.ofChallenges S0 simAt).law x) ≤ _
  rw [hS, CausalViews.honestView]
  refine (PMF.tvDist_bind_left_le' _ _ _).trans ?_
  rw [tsum_fintype]
  have hfin : ∀ ch, (PMF.uniformOfFintype (Chs P t)) ch * Pr[ω ← Ω : bad x w ω ch] ≠ ⊤ :=
    fun ch => ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
      (ne_top_of_le_ne_top ENNReal.one_ne_top (PMF.toOuterMeasure_apply_le_one _ _))
  calc ∑ ch, ((PMF.uniformOfFintype (Chs P t)) ch).toReal *
        PMF.tvDist ((PMF.uniformOfFintype (Ω × R')).map
          fun ρ => M.view ((honest w ρ.1 ρ.2).run x ch))
          ((PMF.uniformOfFintype S0).map (simAt x ch))
      ≤ ∑ ch, ((PMF.uniformOfFintype (Chs P t)) ch).toReal *
          (Pr[ω ← Ω : bad x w ω ch]).toReal :=
        Finset.sum_le_sum fun ch _ => mul_le_mul_of_nonneg_left (hin ch) ENNReal.toReal_nonneg
    _ = (∑ ch, (PMF.uniformOfFintype (Chs P t)) ch * Pr[ω ← Ω : bad x w ω ch]).toReal := by
        rw [ENNReal.toReal_sum fun ch _ => hfin ch]
        exact Finset.sum_congr rfl fun ch _ => (ENNReal.toReal_mul).symm
    _ = (Pr[u ← (Chs P t × Ω) : bad x w u.2 u.1]).toReal := by
        rw [probUniform_prod_eq_tsum, tsum_fintype]
    _ = (Pr[u ← (Ω × Chs P t) : bad x w u.1 u.2]).toReal := by
        rw [probUniform_equiv (Equiv.prodComm (Chs P t) Ω)]
        rfl
    _ ≤ δ x := ENNReal.toReal_le_of_le_ofReal (δ x).2 ((bad_le x w hw).trans (by simp))

end HVZK

/-! ### Sequence and parallel -/

section Node

variable [∀ j (i : (P j).ChallengeIdx), Fintype ((P j).Challenge i)]
  [∀ j (i : (P j).ChallengeIdx), Nonempty ((P j).Challenge i)] {Stmt Wit Pub : Type}
  {a b : SPTerm ι}

/-- **The simulator of a sequence**: `S₁` on the public statement, then `S₂` on the public
statement together with the simulated first-part view, with independent coins.

Running time: one run of `S₁` and one of `S₂` (their own Running time paragraphs) plus joining the
two views, linear in the view sizes; polynomial when both simulators are. This running time is
argued here, not proved in Lean. -/
def CausalJointSimulator.seq {M₁ : CausalViews P a} {M₂ : CausalViews P b}
    (S₁ : CausalJointSimulator M₁ Pub) (S₂ : CausalJointSimulator M₂ (Pub × CausalView M₁)) :
    CausalJointSimulator (CausalViews.node (k := .seq) M₁ M₂) Pub where
  Coins := S₁.Coins × S₂.Coins
  sim y c := (S₁.sim y c.1).join (S₂.sim (y, S₁.sim y c.1) c.2)

/-- **The simulator of a composite with independent parts**: `S₁` and `S₂` on the public
statement with independent coins.

Running time: one run of `S₁` and one of `S₂` (their own Running time paragraphs) plus joining the
two views, linear in the view sizes; polynomial when both simulators are. This running time is
argued here, not proved in Lean. -/
def CausalJointSimulator.par {k : Comp} {M₁ : CausalViews P a} {M₂ : CausalViews P b}
    (S₁ : CausalJointSimulator M₁ Pub) (S₂ : CausalJointSimulator M₂ Pub) :
    CausalJointSimulator (CausalViews.node (k := k) M₁ M₂) Pub where
  Coins := S₁.Coins × S₂.Coins
  sim y c := (S₁.sim y c.1).join (S₂.sim y c.2)

/-- The uniform draws of a node's challenges and a pair of coins, as the draws of each part's
challenges and coins. -/
def nodeDrawEquiv {k : Comp} (R₁ R₂ : Type) :
    (Chs P a × R₁) × (Chs P b × R₂) ≃ Chs P (node k a b) × (R₁ × R₂) :=
  (Equiv.prodProdProdComm (Chs P a) R₁ (Chs P b) R₂).trans
    (Chs.equivNode.symm.prodCongr (Equiv.refl _))

/-- **Mixing a bounded kernel distance**: if two kernels are within `δ` at every point, their
mixtures by the same law on a finite type are within `δ`. -/
theorem tvDist_bind_left_le_of_le {α β : Type} [Fintype α] (p : PMF α) (k₁ k₂ : α → PMF β)
    {δ : ℝ} (h : ∀ a, PMF.tvDist (k₁ a) (k₂ a) ≤ δ) :
    PMF.tvDist (p.bind k₁) (p.bind k₂) ≤ δ := by
  refine (PMF.tvDist_bind_left_le' p k₁ k₂).trans ?_
  rw [tsum_fintype]
  calc ∑ a, (p a).toReal * PMF.tvDist (k₁ a) (k₂ a) ≤ ∑ a, (p a).toReal * δ :=
        Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (h a) ENNReal.toReal_nonneg
    _ = δ := by rw [← Finset.sum_mul, PMF.sum_toReal, one_mul]

variable {R₁ R₂ : Type} [Fintype R₁] [Nonempty R₁] [Fintype R₂] [Nonempty R₂]

/-- **Zero knowledge of a sequence.** The first part is zero knowledge for `rel` at `S₁` with
error `δ₁`; the second, on statements extended by the first part's transcripts, is zero knowledge
for `rel₂` at `S₂` with error `δ₂`, its simulator reading the public statement and the first
part's view; and from every pair of `rel` and every honest first-part run, `wit` gives a witness of
`rel₂` (`split_witness`). The composite of the honest provers, with independent coins and the
second reading its witness off its statement, is zero knowledge for `rel` at `S₁.seq S₂` with
error `δ₁ + δ₂`. -/
theorem CausalHVZK.seq {M₁ : CausalViews P a} {M₂ : CausalViews P b} {W₂ : Type}
    {rel : Set (Stmt × Wit)}
    {rel₂ : Set ((Stmt × FullTr P a) × W₂)} {honest₁ : Wit → R₁ → CausalProver P a Stmt}
    {honest₂ : W₂ → R₂ → CausalProver P b (Stmt × FullTr P a)} {pub : Stmt → Pub}
    {S₁ : CausalJointSimulator M₁ Pub}
    {S₂ : CausalJointSimulator M₂ (Pub × CausalView M₁)} {δ₁ δ₂ : ℝ≥0}
    (h₁ : CausalHVZK M₁ rel honest₁ pub S₁ δ₁)
    (h₂ : CausalHVZK M₂ rel₂ honest₂ (fun y => (pub y.1, M₁.view y.2)) S₂ δ₂)
    (wit : Stmt → Wit → FullTr P a → W₂)
    (split_witness : ∀ x w, (x, w) ∈ rel → ∀ ρ ch,
      ((x, (honest₁ w ρ).run x ch), wit x w ((honest₁ w ρ).run x ch)) ∈ rel₂) :
    CausalHVZK (CausalViews.node (k := .seq) M₁ M₂) rel (fun w (ρ : R₁ × R₂) =>
        (honest₁ w ρ.1).seq (CausalProver.ofStmt fun y => honest₂ (wit y.1 w y.2) ρ.2))
      pub (S₁.seq S₂) (δ₁ + δ₂) := by
  intro x w hw
  let f₁ : Chs P a × R₁ → FullTr P a := fun u => (honest₁ w u.2).run x u.1
  let K : CausalView M₁ → PMF (CausalView (CausalViews.node (k := .seq) M₁ M₂)) :=
    fun v₁ => (S₂.law (pub x, v₁)).map v₁.join
  have hH : (CausalViews.node (k := .seq) M₁ M₂).honestView (fun w (ρ : R₁ × R₂) =>
        (honest₁ w ρ.1).seq (CausalProver.ofStmt fun y => honest₂ (wit y.1 w y.2) ρ.2)) x w =
      (PMF.uniformOfFintype (Chs P a × R₁)).bind fun u =>
        (M₂.honestView honest₂ (x, f₁ u) (wit x w (f₁ u))).map (M₁.view (f₁ u)).join := by
    rw [CausalViews.honestView_eq_map, ← PMF.uniformOfFintype_map_equiv (nodeDrawEquiv R₁ R₂),
      PMF.map_comp, PMF.uniformOfFintype_prod_eq_bind, PMF.map_bind]
    congr 1
    funext u
    rw [CausalViews.honestView_eq_map, PMF.map_comp, PMF.map_comp]
    congr 1
    funext v
    simp only [Function.comp_apply]
    rw [CausalProver.run_seq, CausalProver.run_ofStmt, CausalViews.view_join]
    rfl
  have hS : (S₁.seq S₂).law (pub x) = (S₁.law (pub x)).bind K := by
    change (PMF.uniformOfFintype (S₁.Coins × S₂.Coins)).map (fun c : S₁.Coins × S₂.Coins =>
      (S₁.sim (pub x) c.1).join (S₂.sim (pub x, S₁.sim (pub x) c.1) c.2)) = _
    rw [PMF.uniformOfFintype_prod_eq_bind, PMF.map_bind,
      CausalJointSimulator.law, PMF.bind_map]
    congr 1
    funext c₁
    simp only [Function.comp_apply, K, CausalJointSimulator.law, PMF.map_comp]
    rfl
  have hM : (PMF.uniformOfFintype (Chs P a × R₁)).bind (fun u => K (M₁.view (f₁ u))) =
      (M₁.honestView honest₁ x w).bind K := by
    rw [CausalViews.honestView_eq_map, PMF.bind_map]
    rfl
  rw [hH, hS]
  calc PMF.tvDist _ _
      ≤ PMF.tvDist ((PMF.uniformOfFintype (Chs P a × R₁)).bind fun u =>
            (M₂.honestView honest₂ (x, f₁ u) (wit x w (f₁ u))).map (M₁.view (f₁ u)).join)
          ((PMF.uniformOfFintype (Chs P a × R₁)).bind fun u => K (M₁.view (f₁ u))) +
        PMF.tvDist ((PMF.uniformOfFintype (Chs P a × R₁)).bind fun u => K (M₁.view (f₁ u)))
          ((S₁.law (pub x)).bind K) := PMF.tvDist_triangle _ _ _
    _ ≤ δ₂ + δ₁ := by
      refine add_le_add (tvDist_bind_left_le_of_le _ _ _ fun u => ?_) ?_
      · exact (PMF.tvDist_map_le _ _ _).trans
          (h₂ (x, f₁ u) _ (split_witness x w hw u.2 u.1))
      · rw [hM]
        exact (PMF.tvDist_bind_right_le _ _ _).trans (h₁ x w hw)
    _ = ((δ₁ + δ₂ : ℝ≥0) : ℝ) := by push_cast; ring

/-- **Zero knowledge of a composite with independent parts**: parts zero knowledge for `rel₁` at
`S₁` and for `rel₂` at `S₂`, on the same statements, witnesses and public statements, run side by
side or one after the other without reading each other's transcripts, with independent coins, are
zero knowledge for both relations at `S₁.indep S₂` with error `δ₁ + δ₂`. -/
theorem CausalHVZK.par {k : Comp} {M₁ : CausalViews P a} {M₂ : CausalViews P b}
    {rel₁ rel₂ : Set (Stmt × Wit)}
    {honest₁ : Wit → R₁ → CausalProver P a Stmt} {honest₂ : Wit → R₂ → CausalProver P b Stmt}
    {pub : Stmt → Pub} {S₁ : CausalJointSimulator M₁ Pub}
    {S₂ : CausalJointSimulator M₂ Pub} {δ₁ δ₂ : ℝ≥0}
    (h₁ : CausalHVZK M₁ rel₁ honest₁ pub S₁ δ₁)
    (h₂ : CausalHVZK M₂ rel₂ honest₂ pub S₂ δ₂) :
    CausalHVZK (CausalViews.node (k := k) M₁ M₂) (rel₁ ∩ rel₂)
      (fun w (ρ : R₁ × R₂) => (honest₁ w ρ.1).par (honest₂ w ρ.2))
      pub (S₁.par S₂) (δ₁ + δ₂) := by
  intro x w hw
  let f₁ : Chs P a × R₁ → FullTr P a := fun u => (honest₁ w u.2).run x u.1
  let K : CausalView M₁ → PMF (CausalView (CausalViews.node (k := k) M₁ M₂)) :=
    fun v₁ => (S₂.law (pub x)).map v₁.join
  have hH : (CausalViews.node (k := k) M₁ M₂).honestView
      (fun w (ρ : R₁ × R₂) => (honest₁ w ρ.1).par (honest₂ w ρ.2)) x w =
      (PMF.uniformOfFintype (Chs P a × R₁)).bind fun u =>
        (M₂.honestView honest₂ x w).map (M₁.view (f₁ u)).join := by
    rw [CausalViews.honestView_eq_map, ← PMF.uniformOfFintype_map_equiv (nodeDrawEquiv R₁ R₂),
      PMF.map_comp, PMF.uniformOfFintype_prod_eq_bind, PMF.map_bind]
    congr 1
    funext u
    rw [CausalViews.honestView_eq_map, PMF.map_comp, PMF.map_comp]
    congr 1
    funext v
    simp only [Function.comp_apply]
    rw [CausalProver.run_par, CausalViews.view_join]
    rfl
  have hS : (S₁.par S₂).law (pub x) = (S₁.law (pub x)).bind K := by
    change (PMF.uniformOfFintype (S₁.Coins × S₂.Coins)).map (fun c : S₁.Coins × S₂.Coins =>
      (S₁.sim (pub x) c.1).join (S₂.sim (pub x) c.2)) = _
    rw [PMF.uniformOfFintype_prod_eq_bind, PMF.map_bind,
      CausalJointSimulator.law, PMF.bind_map]
    congr 1
    funext c₁
    simp only [Function.comp_apply, K, CausalJointSimulator.law, PMF.map_comp]
    rfl
  have hM : (PMF.uniformOfFintype (Chs P a × R₁)).bind (fun u => K (M₁.view (f₁ u))) =
      (M₁.honestView honest₁ x w).bind K := by
    rw [CausalViews.honestView_eq_map, PMF.bind_map]
    rfl
  rw [hH, hS]
  calc PMF.tvDist _ _
      ≤ PMF.tvDist ((PMF.uniformOfFintype (Chs P a × R₁)).bind fun u =>
            (M₂.honestView honest₂ x w).map (M₁.view (f₁ u)).join)
          ((PMF.uniformOfFintype (Chs P a × R₁)).bind fun u => K (M₁.view (f₁ u))) +
        PMF.tvDist ((PMF.uniformOfFintype (Chs P a × R₁)).bind fun u => K (M₁.view (f₁ u)))
          ((S₁.law (pub x)).bind K) := PMF.tvDist_triangle _ _ _
    _ ≤ δ₂ + δ₁ := by
      refine add_le_add (tvDist_bind_left_le_of_le _ _ _ fun u => ?_) ?_
      · exact (PMF.tvDist_map_le _ _ _).trans (h₂ x w hw.2)
      · rw [hM]
        exact (PMF.tvDist_bind_right_le _ _ _).trans (h₁ x w hw.1)
    _ = ((δ₁ + δ₂ : ℝ≥0) : ℝ) := by push_cast; ring

end Node

/-! ### Views built from parts -/

/-- The message views of `m` subterms composed by `k`. -/
def CausalViews.nodeN (k : Comp) : (m : ℕ) → {c : Fin m → SPTerm ι} →
    (∀ i, CausalViews P (c i)) → CausalViews P (SPTerm.nodeN k m c)
  | 0, _, _ => ⟨fun p => (nomatch p), fun p => (nomatch p), fun p => (nomatch p)⟩
  | m + 1, _, M => CausalViews.node (M 0) (CausalViews.nodeN k m fun i => M i.succ)

/-- The message views of a one-component term from an IOP of the component. -/
def CausalViews.ofIOP {j : ι} {StmtC : Type} (I : IOP (P j) StmtC) : CausalViews P (leaf j) where
  Idx
    | .here _ => I.Idx
  Ans
    | .here _ => I.Ans
  msg
    | .here _ => fun i => (I.msg i).comap Chs.equivLeaf

/-- The composite transcript of a one-component term. -/
def FullTr.ofLeaf {j : ι} (tr : (P j).Transcript (Fin.last (n j))) : FullTr P (leaf j)
  | .here _ => tr

/-- The run of a one-component causal prover, as a composite transcript. -/
theorem CausalProver.run_ofLeaf_eq {j : ι} {Stmt : Type} (prv : Prover (P j) Stmt) (x : Stmt)
    (ch : Chs P (leaf j)) :
    (CausalProver.ofLeaf prv).run x ch = FullTr.ofLeaf (prv.run x (Chs.equivLeaf ch)) := by
  funext p
  cases p
  exact CausalProver.run_ofLeaf prv x ch

/-- The view of a one-component composite as the IOP's view. -/
def CausalView.ofIOP {j : ι} {StmtC : Type} {I : IOP (P j) StmtC} (v : TranscriptView I.msg) :
    CausalView (CausalViews.ofIOP I) where
  challenges := Chs.equivLeaf.symm v.challenges
  entries
    | .here _ => v.entries

/-- The composite view of a one-component run is the IOP's view under the same challenges. -/
theorem CausalViews.view_ofIOP {j : ι} {StmtC : Type} (I : IOP (P j) StmtC)
    (tr : (P j).Transcript (Fin.last (n j))) (ch : (P j).Challenges)
    (htr : ∀ i : (P j).ChallengeIdx, tr i.1 = ch i) :
    (CausalViews.ofIOP I).view (FullTr.ofLeaf tr) = CausalView.ofIOP ⟨ch, I.view ch tr⟩ := by
  have hc : (FullTr.ofLeaf (P := P) tr).challenges.at (.here j) = ch := funext htr
  ext1
  · funext c
    obtain ⟨p, i⟩ := c
    cases p
    exact htr i
  · funext p
    cases p
    funext i
    change (I.msg i).see ((FullTr.ofLeaf (P := P) tr).challenges.at (.here j)) (tr i.1) = _
    rw [hc]
    rfl

section Parts

variable [∀ j (i : (P j).ChallengeIdx), Fintype ((P j).Challenge i)]
  [∀ j (i : (P j).ChallengeIdx), Nonempty ((P j).Challenge i)] {Stmt Wit Pub : Type}

/-- **A one-component simulator from an IOP's joint simulator**: `S` on the component statement
`g y` of the public statement `y`, its view read as a composite view.

Running time: one run of `S` (its own Running time paragraph) and one evaluation of `g`; polynomial
when both are. This running time is argued here, not proved in Lean. -/
def CausalJointSimulator.ofIOP {j : ι} {StmtC : Type} {I : IOP (P j) StmtC} (S : I.JointSimulator)
    (g : Pub → StmtC) : CausalJointSimulator (CausalViews.ofIOP I) Pub where
  Coins := S.Coins
  sim y c := CausalView.ofIOP (S.sim (g y) c)

/-- **The simulator of `m` composites with independent parts**: each composite's simulator on the
public statement, with independent coins.

Running time: one run of each `S i` (their own Running time paragraphs) plus joining the views;
polynomial when each `S i` is and `m` is polynomial. This running time is argued here, not proved in
Lean. -/
def CausalJointSimulator.nodeN (k : Comp) : (m : ℕ) → {c : Fin m → SPTerm ι} →
    {M : ∀ i, CausalViews P (c i)} → (∀ i, CausalJointSimulator (M i) Pub) →
    CausalJointSimulator (CausalViews.nodeN k m M) Pub
  | 0, _, _, _ => ⟨Unit, fun _ _ => ⟨fun ⟨p, _⟩ => (nomatch p), fun p => (nomatch p)⟩⟩
  | m + 1, _, _, S => CausalJointSimulator.par (k := k) (S 0)
    (CausalJointSimulator.nodeN k m fun i => S i.succ)

/-- A composite with no leaves has one view. -/
instance CausalView.subsingleton_nodeN_zero {k : Comp} {c : Fin 0 → SPTerm ι}
    (M : CausalViews P (SPTerm.nodeN k 0 c)) : Subsingleton (CausalView M) :=
  ⟨fun v v' => by
    ext1
    · funext c
      obtain ⟨p, _⟩ := c
      exact nomatch p
    · funext p
      exact nomatch p⟩

/-- Two laws on a type with at most one element are equal. About Mathlib objects only; a candidate
for `PQ/ToMathlib`. -/
theorem PMF.eq_of_subsingleton {α : Type*} [Subsingleton α] (p q : PMF α) : p = q := by
  ext a
  have hp := p.tsum_coe
  have hq := q.tsum_coe
  rw [tsum_eq_single a fun b hb => absurd (Subsingleton.elim b a) hb] at hp hq
  rw [hp, hq]

/-- **Zero knowledge is unchanged by reading the honest coins through an equivalence.** -/
theorem CausalHVZK.comapCoins {t : SPTerm ι} {M : CausalViews P t} {rel : Set (Stmt × Wit)}
    {R R' : Type} [Fintype R] [Nonempty R] [Fintype R'] [Nonempty R']
    {honest : Wit → R → CausalProver P t Stmt} {pub : Stmt → Pub} {S : CausalJointSimulator M Pub}
    {δ : ℝ≥0} (h : CausalHVZK M rel honest pub S δ) (e : R' ≃ R) :
    CausalHVZK M rel (fun w ρ => honest w (e ρ)) pub S δ := by
  intro x w hw
  have heq : M.honestView (fun w ρ => honest w (e ρ)) x w = M.honestView honest x w := by
    rw [CausalViews.honestView_eq_map, CausalViews.honestView_eq_map,
      ← PMF.uniformOfFintype_map_equiv ((Equiv.refl (Chs P t)).prodCongr e), PMF.map_comp]
    rfl
  rw [heq]
  exact h x w hw

/-- The coins of `m + 1` components: the first component's and the rest's. -/
def finSuccPiEquiv {m : ℕ} (R : Fin (m + 1) → Type) :
    (∀ i, R i) ≃ R 0 × ∀ i : Fin m, R i.succ where
  toFun ρ := (ρ 0, fun i => ρ i.succ)
  invFun q := Fin.cons q.1 q.2
  left_inv ρ := Fin.cons_self_tail ρ
  right_inv q := by
    simp only [Fin.cons_zero, Fin.cons_succ]

/-- **Zero knowledge of `m` composites** side by side or one after the other, none reading
another's transcripts: on the same statements, witnesses and public statements, with independent
coins, errors add, for the intersection of the relations. -/
theorem CausalHVZK.nodeN (k : Comp) : (m : ℕ) → {c : Fin m → SPTerm ι} →
    {M : ∀ i, CausalViews P (c i)} →
    {rel : Fin m → Set (Stmt × Wit)} → {R : Fin m → Type} → [∀ i, Fintype (R i)] →
    [∀ i, Nonempty (R i)] → {honest : ∀ i, Wit → R i → CausalProver P (c i) Stmt} →
    {pub : Stmt → Pub} → {S : ∀ i, CausalJointSimulator (M i) Pub} → {δ : Fin m → ℝ≥0} →
    (∀ i, CausalHVZK (M i) (rel i) (honest i) pub (S i) (δ i)) →
    CausalHVZK (CausalViews.nodeN k m M) {p | ∀ i, p ∈ rel i}
      (fun w (ρ : ∀ i, R i) => CausalProver.nodeN k m fun i => honest i w (ρ i)) pub
      (CausalJointSimulator.nodeN k m S) (∑ i, δ i)
  | 0, _, _, _, _, _, _, _, _, _, _, _ => fun x w _ => by
    rw [PMF.eq_of_subsingleton (CausalViews.honestView _ _ x w)
      (CausalJointSimulator.law _ _), PMF.tvDist_self]
    simp
  | m + 1, _, M, rel, R, _, _, honest, pub, S, δ, h => by
    have hpar := par (k := k) (h 0) (nodeN k m fun i => h i.succ)
    have hc := hpar.comapCoins (finSuccPiEquiv R)
    intro x w hw
    refine (hc x w ⟨hw 0, fun i => hw i.succ⟩).trans_eq ?_
    rw [Fin.sum_univ_succ]

/-- **Zero knowledge of an IOP as a one-component composite** (from CY24 Definition 23.1.8 in the
form `IOP.HVZK`): on statements `y` whose component statement `g (pub y)` is computed from their
public part, with witnesses read through `ω`, the component's honest prover is zero knowledge at
the simulator `S.ofIOP g` with the same error. -/
theorem CausalHVZK.ofIOP {j : ι} {Y W StmtC WitC : Type} {I : IOP (P j) StmtC}
    {relC : Set (StmtC × WitC)} {R : Type} [Fintype R] [Nonempty R]
    {honest : WitC → R → Prover (P j) StmtC} {S : I.JointSimulator} {δ : ℝ≥0}
    (h : I.HVZK relC honest S δ) (g : Pub → StmtC) (pub : Y → Pub) (ω : Y → W → WitC) :
    CausalHVZK (CausalViews.ofIOP I) {p | (g (pub p.1), ω p.1 p.2) ∈ relC}
      (fun w ρ => CausalProver.ofLeaf
        (Prover.ofStatement fun y => (honest (ω y w) ρ).comap (g ∘ pub))) pub
      (CausalJointSimulator.ofIOP S g) δ := by
  intro y w hw
  have hH : (CausalViews.ofIOP I).honestView (fun w ρ => CausalProver.ofLeaf
        (Prover.ofStatement fun y => (honest (ω y w) ρ).comap (g ∘ pub))) y w =
      (I.honestView honest (g (pub y)) (ω y w)).map CausalView.ofIOP := by
    rw [CausalViews.honestView_eq_map, IOP.honestView, PMF.map_bind,
      ← PMF.uniformOfFintype_map_equiv (Chs.equivLeaf.symm.prodCongr (Equiv.refl R)), PMF.map_comp,
      PMF.uniformOfFintype_prod_eq_bind, PMF.map_bind]
    congr 1
    funext ch
    simp only [PMF.map_comp]
    refine congrArg (fun f => PMF.map f (PMF.uniformOfFintype R)) (funext fun ρ => ?_)
    simp only [Function.comp_apply, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply]
    rw [CausalProver.run_ofLeaf_eq, Equiv.apply_symm_apply, Prover.run_ofStatement,
      Prover.run_comap]
    exact CausalViews.view_ofIOP I _ ch fun i => Prover.run_challenge _ _ ch i
  have hS : (CausalJointSimulator.ofIOP S g).law (pub y) =
      (S.law (g (pub y))).map CausalView.ofIOP := by
    rw [CausalJointSimulator.law, IOP.JointSimulator.law, PMF.map_comp]
    rfl
  rw [hH, hS]
  exact (PMF.tvDist_map_le _ _ _).trans (h _ _ hw)

end Parts

end GordieHowe.IOP
