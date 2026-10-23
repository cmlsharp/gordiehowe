-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.FieldProof.MaskedRowReduction
public import GordieHowe.ProofSystem.GKR.Schedule
public import GordieHowe.Model.IOP.ClaimReductionSeq
public import GordieHowe.Model.IOP.ChallengeEventReduction
public import GordieHowe.Model.IOP.RBR

@[expose] public section

/-!
# Masked reductions: masked protocols that leave claims on logical coordinates

GordieHowe's domain proofs end their masked row reductions not only in rows on the committed cells but in
**claims on logical coordinates**: the GKR input claim on circuit inputs that are bits packed into
words, a batch's terminal claim on the bits of its table words (`lib/gordiehowe/compiler/tree_zk.h`,
header: "Claims are linear rows over the logical coordinates L"). A packing stage reduces such
claims to rows on the words (`GordieHowe/ProofSystem/RingSwitching/PackingStage.lean`).

* **Levels** (`Level F ι Y`): logical coordinates `Y` over the cells `ι`, with the logical
  assignment read from the cells (`view`) and each cell's own coordinate (`cell`). The cells
  themselves are the base level (`Level.base`).
* **`MaskedReduction`** (a masked reduction): a protocol whose prover messages are masked by
  committed pads, a `MaskedRowReduction` with `nc` affine claims on a level's coordinates `Z`,
  computed by the verifier from the public input and the transcript. Its soundness
  (`MaskedReduction.Sound`) yields a round-by-round reduction (`IOP.Reduction`) from the relation to
  the rows on the cells and the claims on the logical assignment (`OutHolds`); its honest prover (`MaskedReduction.Honest`) is that
  of a masked row reduction with the claims added to completeness.
* **Constructions**: fixed affine claims with no rounds (`static`); two masked reductions in sequence,
  claims side by side (`append`); **claim combination** (`combine`): one fresh coefficient per claim
  drawn after all of them are fixed, the claims replaced by their combination, at the error `1/|F|`
  (`Sound.combine`: a nonzero vector of claim values is orthogonal to a uniform coefficient vector
  with probability `1/|F|`, `card_filter_combination_le`; the stage of a packing-tree node in
  `lib/gordiehowe/compiler/tree_zk.h` combines the rows that touch the node's region by fresh
  challenges); and **closing** a masked reduction whose claims are on the cells into a masked row
  reduction (`close`).
-/

namespace GordieHowe

open IOP IOP.ProtocolSpec
open GKR.Schedule (one oneValue)
open scoped NNReal

/-! ### Levels of logical coordinates -/

/-- **A level of logical coordinates** `Y` over the cells `ι`: the logical assignment read from the
cells (`view`) and each cell's coordinate (`cell`), at which the logical assignment is the cell's
value (`view_cell`). -/
structure Level (F ι Y : Type) where
  /-- The logical assignment read from the cells. -/
  view : (ι → F) → Y → F
  /-- Each cell's coordinate. -/
  cell : ι → Y
  /-- A cell's coordinate reads the cell. -/
  view_cell : ∀ x i, view x (cell i) = x i

/-- **The cells as their own level.** -/
def Level.base {F ι : Type} : Level F ι ι where
  view x := x
  cell i := i
  view_cell _ _ := rfl

@[simp] theorem Level.base_view {F ι : Type} (x : ι → F) : (Level.base (F := F)).view x = x :=
  rfl

/-! ### Combining claims -/

section Combination

variable {F Z : Type} [Field F] {nc : ℕ}

/-- **The combination of claims** `Σ_c ρ_c · claim_c` (`tree_zk.h:504-541`, the weighted sum of
the touching rows). -/
def combination (ρ : Fin nc → F) (cl : Fin nc → AffineForm F Z) : AffineForm F Z :=
  AffineForm.sumFin fun c => ρ c • cl c

@[simp] theorem eval_combination (ρ : Fin nc → F) (cl : Fin nc → AffineForm F Z) (z : Z → F) :
    (combination ρ cl).eval z = ∑ c, ρ c * (cl c).eval z := by
  simp [combination]

/-- **The combination event** for claim values `e`: some claim fails, and the coefficient vector `ρ`
is orthogonal to the values. -/
def CombinationBad (e : Fin nc → F) (ρ : Fin nc → F) : Prop :=
  (∃ c, e c ≠ 0) ∧ ∑ c, ρ c * e c = 0

open Classical in
/-- **A nonzero vector is orthogonal to at most `|F|^(nc - 1)` coefficient vectors**: the
combination event has probability at most `1/|F|` under a uniform coefficient vector (fix the other
coefficients; the coefficient of a nonzero value then has at most one bad value). -/
theorem card_filter_combination_le [Fintype F] [DecidableEq F] (e : Fin nc → F) :
    ((Finset.univ.filter fun ρ : Fin nc → F => CombinationBad e ρ).card : ℝ≥0) ≤
      (1 / Fintype.card F) * Fintype.card (Fin nc → F) := by
  by_cases he : ∃ c, e c ≠ 0
  · obtain ⟨c₀, hc₀⟩ := he
    refine IOP.card_le_of_card_update_le c₀ fun f => ?_
    have hF : (Fintype.card F : ℝ≥0) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    rw [one_div, inv_mul_cancel₀ hF]
    rw [← Nat.cast_one, Nat.cast_le]
    refine Finset.card_le_one.mpr ?_
    intro x hx y hy
    rw [Finset.mem_filter, Finset.mem_filter] at hx hy
    have hx' : CombinationBad e (Function.update f c₀ x) := hx.2.2
    have hy' : CombinationBad e (Function.update f c₀ y) := hy.2.2
    have hdiff : ∑ c, Function.update f c₀ x c * e c - ∑ c, Function.update f c₀ y c * e c =
        (x - y) * e c₀ := by
      rw [← Finset.sum_sub_distrib, Finset.sum_eq_single c₀]
      · simp only [Function.update_self]
        ring
      · intro c _ hc
        simp only [Function.update_of_ne hc, sub_self]
      · simp
    rw [hx'.2, hy'.2, sub_self] at hdiff
    exact sub_eq_zero.mp ((mul_eq_zero.mp hdiff.symm).resolve_right hc₀)
  · have hempty : (Finset.univ.filter fun ρ : Fin nc → F => CombinationBad e ρ) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun ρ _ h => he h.1
    rw [hempty, Finset.card_empty, Nat.cast_zero]
    positivity

end Combination

variable {F ι : Type} [Field F] [Fintype ι]

/-! ### The interface -/

/-- **A masked reduction**: a protocol whose prover messages are masked by committed pads, a
`MaskedRowReduction` on the cells whose verifier also computes `nc` affine claims `claims p tr` on logical coordinates `Z`, from the public input and the
full transcript. The claims hold on the logical assignment of a level of `Z`, and a packing stage or
`close` turns them into rows on the cells. -/
structure FieldProof.MaskedReduction (F ι : Type) [Field F] [Fintype ι] (Pub Wit : Type) (cells : Wit → ι → F)
    (Z : Type) (nc : ℕ) extends MaskedRowReduction F ι Pub Wit cells where
  /-- The claims the verifier computes. -/
  claims : Pub → spec.Transcript (Fin.last n) → Fin nc → AffineForm F Z

namespace FieldProof.MaskedReduction

variable {Pub Wit Z : Type} {cells : Wit → ι → F} {nc : ℕ}

/-- **The output of a masked reduction holds** on the cells `x`, at the logical assignment `view x`: the
rows on the cells and every claim. -/
structure OutHolds (M : MaskedReduction F ι Pub Wit cells Z nc) (view : (ι → F) → Z → F) (p : Pub)
    (tr : M.spec.Transcript (Fin.last M.n)) (x : ι → F) : Prop where
  /-- The rows on the cells hold. -/
  rows : RowsHold (M.linear p tr) M.products x
  /-- Every claim holds on the logical assignment. -/
  claims : ∀ c, (M.claims p tr c).eval (view x) = 0

/-- **Soundness of a masked reduction** for the relation `sat`, at the logical assignment `view`, with
per-round errors `ε`: a `ClaimReduction` from `sat` (`claim_iff`) to the output (`claimOut_iff`),
round by round. -/
structure Sound (M : MaskedReduction F ι Pub Wit cells Z nc) (view : (ι → F) → Z → F)
    (sat : Pub → Wit → Prop) (ε : M.spec.ChallengeIdx → ℝ≥0) where
  /-- The reduction from `sat` to the output. -/
  reduction : ClaimReduction M.spec (MaskedRowReduction.Instance Pub Wit) ε
  claim_iff : ∀ p w, reduction.claim ⟨p, w⟩ ↔ sat p w
  claimOut_iff : ∀ p w tr, reduction.claimOut ⟨p, w⟩ tr ↔ M.OutHolds view p tr (cells w)

/-- **A simulator of a masked reduction's transcript** (`IOP.TranscriptSim`), data apart from the honest
prover (`Honest`). -/
abbrev Sim (M : MaskedReduction F ι Pub Wit cells Z nc) : Type 1 := IOP.TranscriptSim Pub M.spec

/-- **The honest prover of a masked reduction**, on honest inputs `In` in the domain `dom`, at the
logical assignment `view`, simulated by `S`: `MaskedRowReduction.Honest` with the claims added to
completeness (`complete`: the honest transcript's output holds on every committing witness).
Completeness holds on the domain; the simulation (`identDistrib`) holds at every public input and
every honest input, as paper `def:red-sec` (c) quantifies over every statement and witness. -/
structure Honest (M : MaskedReduction F ι Pub Wit cells Z nc) (view : (ι → F) → Z → F) (In : Type)
    (dom : Pub → In → Prop) (S : M.Sim) where
  /-- The pads. -/
  Pads : Type
  [fintype : Fintype Pads]
  [nonempty : Nonempty Pads]
  /-- The honest prover's transcript family. -/
  prover : Pub → In → Pads → CausalTranscript M.spec
  /-- The committed witness holds the honest input and the pads. -/
  Commits : Pub → In → Pads → Wit → Prop
  /-- The honest transcript's output holds. -/
  complete : ∀ p x, dom p x → ∀ π w, Commits p x π w → ∀ ch,
    M.OutHolds view p ((prover p x π).transcript ch) (cells w)
  /-- The honest transcript has the simulator's law, at every public input and honest input. -/
  identDistrib : ∀ p x ch, (fun π => (prover p x π).transcript ch) =ᵈ S.sim p ch

attribute [instance] Honest.fintype Honest.nonempty

/-- **Soundness for an equivalent relation**: the same reduction and errors. -/
def Sound.congr {M : MaskedReduction F ι Pub Wit cells Z nc} {view : (ι → F) → Z → F}
    {s₁ s₂ : Pub → Wit → Prop} {ε : M.spec.ChallengeIdx → ℝ≥0} (S : M.Sound view s₁ ε)
    (h : ∀ p w, s₁ p w ↔ s₂ p w) : M.Sound view s₂ ε where
  reduction := S.reduction
  claim_iff p w := (S.claim_iff p w).trans (h p w)
  claimOut_iff := S.claimOut_iff

/-! ### Closing: claims on the cells become rows -/

/-- **Closing a masked reduction whose claims are on the cells**: the claims become affine rows beside the
IP's rows. -/
def close (M : MaskedReduction F ι Pub Wit cells ι nc) : MaskedRowReduction F ι Pub Wit cells where
  n := M.n
  spec := M.spec
  Lin := M.Lin ⊕ Fin nc
  linear p tr := Sum.elim (M.linear p tr) (M.claims p tr)
  Q := M.Q
  products := M.products

theorem rowsHold_close_iff (M : MaskedReduction F ι Pub Wit cells ι nc) (p : Pub)
    (tr : M.spec.Transcript (Fin.last M.n)) (x : ι → F) :
    RowsHold (M.close.linear p tr) M.close.products x ↔ M.OutHolds (Level.base (F := F)).view p tr x :=
  ⟨fun h => ⟨⟨fun l => h.linear (.inl l), h.products⟩, fun c => h.linear (.inr c)⟩,
    fun h => ⟨Sum.rec h.rows.linear h.claims, h.rows.products⟩⟩

/-- Soundness of a masked reduction on the cells is soundness of its closing. -/
def Sound.close {M : MaskedReduction F ι Pub Wit cells ι nc} {sat : Pub → Wit → Prop}
    {ε : M.spec.ChallengeIdx → ℝ≥0} (S : M.Sound (Level.base (F := F)).view sat ε) :
    M.close.Sound sat ε where
  reduction := S.reduction
  claim_iff := S.claim_iff
  claimOut_iff p w tr := (S.claimOut_iff p w tr).trans (rowsHold_close_iff M p tr _).symm

/-- The honest prover of a masked reduction on the cells is that of its closing. -/
def Honest.close {M : MaskedReduction F ι Pub Wit cells ι nc} {In : Type} {dom : Pub → In → Prop}
    {S : M.Sim} (H : M.Honest (Level.base (F := F)).view In dom S) : M.close.Honest In dom S where
  Pads := H.Pads
  prover := H.prover
  Commits := H.Commits
  complete p x hx π w hw ch := (rowsHold_close_iff M p _ _).mpr (H.complete p x hx π w hw ch)
  identDistrib p x _ ch := H.identDistrib p x ch

/-! ### Two masked reductions in sequence -/

variable {n₁ n₂ : ℕ}

/-- **Two masked reductions in sequence** on the same cells and level: the rows and the claims stand side
by side (`MaskedRowReduction.append`, claims `Fin.append`). -/
def append (A : MaskedReduction F ι Pub Wit cells Z n₁) (B : MaskedReduction F ι Pub Wit cells Z n₂) :
    MaskedReduction F ι Pub Wit cells Z (n₁ + n₂) where
  toMaskedRowReduction := A.toMaskedRowReduction.append B.toMaskedRowReduction
  claims p tr := Fin.append (A.claims p tr.left) (B.claims p tr.right)

theorem outHolds_append_iff (A : MaskedReduction F ι Pub Wit cells Z n₁)
    (B : MaskedReduction F ι Pub Wit cells Z n₂) (view : (ι → F) → Z → F) (p : Pub)
    (tr : (A.append B).spec.Transcript (Fin.last (A.append B).n)) (x : ι → F) :
    (A.append B).OutHolds view p tr x ↔ A.OutHolds view p tr.left x ∧ B.OutHolds view p tr.right x := by
  constructor
  · intro h
    have hr := (rowsHold_sum _ _ _ _ _).mp h.rows
    refine ⟨⟨hr.1, fun c => ?_⟩, ⟨hr.2, fun c => ?_⟩⟩
    · have hc := h.claims (Fin.castAdd n₂ c)
      simpa only [append, Fin.append_left] using hc
    · have hc := h.claims (Fin.natAdd n₁ c)
      simpa only [append, Fin.append_right] using hc
  · rintro ⟨ha, hb⟩
    refine ⟨(rowsHold_sum _ _ _ _ _).mpr ⟨ha.rows, hb.rows⟩, fun c => ?_⟩
    refine Fin.addCases (fun c => ?_) (fun c => ?_) c
    · simpa only [append, Fin.append_left] using ha.claims c
    · simpa only [append, Fin.append_right] using hb.claims c

/-- **Soundness of two masked reductions in sequence**: the conjunction of their relations, each round
with its error (`ClaimReduction.and`). -/
def Sound.append {A : MaskedReduction F ι Pub Wit cells Z n₁} {B : MaskedReduction F ι Pub Wit cells Z n₂}
    {view : (ι → F) → Z → F} {s₁ s₂ : Pub → Wit → Prop} {εA : A.spec.ChallengeIdx → ℝ≥0}
    {εB : B.spec.ChallengeIdx → ℝ≥0} (SA : A.Sound view s₁ εA) (SB : B.Sound view s₂ εB) :
    (A.append B).Sound view (fun p w => s₁ p w ∧ s₂ p w) (appendError εA εB) where
  reduction := SA.reduction.and SB.reduction
  claim_iff p w := and_congr (SA.claim_iff p w) (SB.claim_iff p w)
  claimOut_iff p w _ :=
    (and_congr (SA.claimOut_iff p w _) (SB.claimOut_iff p w _)).trans
      (outHolds_append_iff A B view p _ _).symm

/-- **The simulators in sequence**: the two simulators, their transcripts joined.

Running time: the two simulators' and a concatenation.
This running time is argued here, not proved in Lean. -/
def Sim.append {A : MaskedReduction F ι Pub Wit cells Z n₁} {B : MaskedReduction F ι Pub Wit cells Z n₂}
    (SA : A.Sim) (SB : B.Sim) : (A.append B).Sim where
  SimCoins := SA.SimCoins × SB.SimCoins
  sim p ch s := Transcript.join (SA.sim p ch.left s.1) (SB.sim p ch.right s.2)

/-- **The honest provers in sequence** (`MaskedRowReduction.Honest.append` with the claims): the second
prover's honest input carries the first one's pads; simulated by the two simulators in sequence
(`Sim.append`). -/
def Honest.append {A : MaskedReduction F ι Pub Wit cells Z n₁} {B : MaskedReduction F ι Pub Wit cells Z n₂}
    {view : (ι → F) → Z → F} {In : Type} {dom : Pub → In → Prop} {SA : A.Sim} {SB : B.Sim}
    (HA : A.Honest view In dom SA)
    (HB : B.Honest view (MaskedRowReduction.WithPads In HA.Pads) (fun p x => dom p x.input) SB) :
    (A.append B).Honest view In dom (SA.append SB) where
  Pads := HA.Pads × HB.Pads
  prover p x π := (HA.prover p x π.1).append fun _ => HB.prover p ⟨x, π.1⟩ π.2
  Commits p x π w := HA.Commits p x π.1 w ∧ HB.Commits p ⟨x, π.1⟩ π.2 w
  complete p x hx π w hw ch := by
    have e₁ := CausalTranscript.append_left (HA.prover p x π.1)
      (fun _ => HB.prover p ⟨x, π.1⟩ π.2) ch
    have e₂ := CausalTranscript.append_right (HA.prover p x π.1)
      (fun _ => HB.prover p ⟨x, π.1⟩ π.2) ch
    refine (outHolds_append_iff A B view p _ _).mpr ⟨?_, ?_⟩
    · exact (congrArg (fun tr => A.OutHolds view p tr (cells w)) e₁).mpr
        (HA.complete p x hx π.1 w hw.1 ch.left)
    · exact (congrArg (fun tr => B.OutHolds view p tr (cells w)) e₂).mpr
        (HB.complete p ⟨x, π.1⟩ hx π.2 w hw.2 ch.right)
  identDistrib p x ch :=
    (IdentDistrib.dependent (f₁ := fun π₁ => (HA.prover p x π₁).transcript ch.left)
      (g₁ := SA.sim p ch.left)
      (f₂ := fun π₁ π₂ => (HB.prover p ⟨x, π₁⟩ π₂).transcript ch.right)
      (g₂ := fun _ => SB.sim p ch.right)
      (HA.identDistrib p x ch.left) fun π₁ => HB.identDistrib p ⟨x, π₁⟩ ch.right).comp
      fun v => Transcript.join v.1 v.2

/-! ### Fixed claims -/

/-- **Fixed affine claims as a masked reduction** (the rows a domain places in a packing node's affine stage:
`Placement::kAffine` rows reading packed bits and bit views, whose claims join the node's combined
measurement): no rounds, no rows on the cells, and the claims `claims p` on the logical
coordinates, fixed by the public input. Appended to a node's other masked reductions (`append`), its
claims are combined with theirs at the stage. -/
def static (claims : Pub → Fin nc → AffineForm F Z) : MaskedReduction F ι Pub Wit cells Z nc where
  toMaskedRowReduction := MaskedRowReduction.static (fun _ (e : Empty) => e.elim)
    (⟨Empty.elim⟩ : Ligero.Routing.ProductLayout ι Empty)
  claims p _ := claims p

theorem outHolds_static_iff (claims : Pub → Fin nc → AffineForm F Z) (view : (ι → F) → Z → F)
    (p : Pub) (tr : (static (ι := ι) (Wit := Wit) (cells := cells) claims).spec.Transcript
      (Fin.last (static (ι := ι) (Wit := Wit) (cells := cells) claims).n)) (x : ι → F) :
    (static (cells := cells) claims).OutHolds view p tr x ↔ ∀ c, (claims p c).eval (view x) = 0 :=
  ⟨fun h => h.claims, fun h => ⟨⟨fun e => e.elim, fun q => q.elim⟩, h⟩⟩

/-- **Soundness of fixed claims**: the relation is the claims on the logical assignment of the
committed cells (`hsat`), with no error. -/
def Sound.static {claims : Pub → Fin nc → AffineForm F Z} {view : (ι → F) → Z → F}
    {sat : Pub → Wit → Prop} (hsat : ∀ p w, sat p w ↔ ∀ c, (claims p c).eval (view (cells w)) = 0) :
    (MaskedReduction.static (cells := cells) claims).Sound view sat fun i => i.1.elim0 where
  reduction :=
    { claim := fun c => sat c.pub c.wit
      claimOut := fun c _ => sat c.pub c.wit
      S := fun _ c _ => sat c.pub c.wit
      start := fun _ _ h => h
      next := fun m => m.elim0
      full := fun _ _ h => h
      rbr := fun _ i => i.1.elim0 }
  claim_iff _ _ := Iff.rfl
  claimOut_iff p w tr := (hsat p w).trans (outHolds_static_iff claims view p tr (cells w)).symm

/-- **The simulator of fixed claims**: no coins, the empty transcript.

Running time: constant. This running time is argued here, not proved in Lean. -/
def Sim.static (claims : Pub → Fin nc → AffineForm F Z) :
    (MaskedReduction.static (ι := ι) (Wit := Wit) (cells := cells) claims).Sim where
  SimCoins := Unit
  sim _ _ _ := fun i => i.elim0

/-- **The honest prover of fixed claims**: no pads and the empty transcript, simulated by
`Sim.static`; completeness is the claims on the committing witnesses (`hcomplete`). -/
def Honest.static {claims : Pub → Fin nc → AffineForm F Z} {view : (ι → F) → Z → F} {In : Type}
    {dom : Pub → In → Prop} (Commits : Pub → In → Wit → Prop)
    (hcomplete : ∀ p x, dom p x → ∀ w, Commits p x w →
      ∀ c, (claims p c).eval (view (cells w)) = 0) :
    (MaskedReduction.static (cells := cells) claims).Honest view In dom (Sim.static claims) where
  Pads := Unit
  prover _ _ _ := CausalTranscript.empty MaskedRowReduction.noRounds
  Commits p x _ := Commits p x
  complete p x hx _ w hw _ := (outHolds_static_iff claims view p _ (cells w)).mpr
    (hcomplete p x hx w hw)
  identDistrib _ _ _ := IdentDistrib.of_equiv (Equiv.refl Unit) fun _ => funext fun i => i.elim0

/-! ### Claim combination -/

variable [Fintype F] [DecidableEq F]

/-- **Claim combination** (`tree_zk.h:493-503`): after the masked reduction, the verifier draws one
coefficient per claim (after the label `gordiehowe.stage:<stage>`), and the claims are replaced by
their combination. The rows on the cells are unchanged. -/
def combine (M : MaskedReduction F ι Pub Wit cells Z nc) : MaskedReduction F ι Pub Wit cells Z 1 where
  n := M.n + 1
  spec := M.spec ++ one .V_to_P (Fin nc → F)
  Lin := M.Lin
  linear p tr := M.linear p tr.left
  Q := M.Q
  products := M.products
  claims p tr _ := combination (oneValue tr.right) (M.claims p tr.left)

/-- **The combination error**: `1/|F|` at the combination challenge, the masked reduction's errors
before. -/
noncomputable def combineError (M : MaskedReduction F ι Pub Wit cells Z nc)
    (ε : M.spec.ChallengeIdx → ℝ≥0) : M.combine.spec.ChallengeIdx → ℝ≥0 :=
  appendError ε fun _ => 1 / Fintype.card F

/-- The combination error sums to the masked reduction's errors plus `1/|F|`. -/
theorem sum_combineError (M : MaskedReduction F ι Pub Wit cells Z nc) (ε : M.spec.ChallengeIdx → ℝ≥0) :
    ∑ i, M.combineError ε i = ∑ i, ε i + 1 / Fintype.card F := by
  refine (sum_appendError (P₁ := M.spec) (P₂ := one .V_to_P (Fin nc → F)) ε _).trans ?_
  congr 1
  rw [Fintype.sum_equiv (GKR.Schedule.verifierIndex (Fin nc → F)) _
    (fun _ => (1 : ℝ≥0) / Fintype.card F) fun _ => rfl]
  simp

/-- **Soundness of claim combination**: the masked reduction's reduction, then the combination challenge,
whose event (`CombinationBad` of the claim values, fixed by the cells and the masked reduction's
transcript) has probability at most `1/|F|` (`card_filter_combination_le`). -/
noncomputable def Sound.combine {M : MaskedReduction F ι Pub Wit cells Z nc} {view : (ι → F) → Z → F}
    {sat : Pub → Wit → Prop} {ε : M.spec.ChallengeIdx → ℝ≥0} (S : M.Sound view sat ε) :
    M.combine.Sound view sat (M.combineError ε) :=
  let vals : AppendContext (MaskedRowReduction.Instance Pub Wit) M.spec → Fin nc → F :=
    fun c i => (M.claims c.ctx.pub c.transcript i).eval (view (cells c.ctx.wit))
  let R₂ : ClaimReduction (one .V_to_P (Fin nc → F))
      (AppendContext (MaskedRowReduction.Instance Pub Wit) M.spec) (fun _ => 1 / Fintype.card F) :=
    ChallengeEventReduction.reduction (one .V_to_P (Fin nc → F))
      (fun _ c _ ρ => CombinationBad (vals c) ρ)
      (fun c => M.OutHolds view c.ctx.pub c.transcript (cells c.ctx.wit))
      (fun c tr => RowsHold (M.linear c.ctx.pub c.transcript) M.products (cells c.ctx.wit) ∧
        ∑ i, oneValue tr i * vals c i = 0)
      (fun _ => 1 / Fintype.card F)
      (fun c _ _ => card_filter_combination_le (vals c))
      (fun c tr h => by
        by_cases hall : ∀ i, vals c i = 0
        · exact Or.inl ⟨h.1, hall⟩
        · push Not at hall
          exact Or.inr ⟨⟨0, rfl⟩, Nat.one_pos, hall, h.2⟩)
  { reduction := S.reduction.seq R₂ fun c tr h => (S.claimOut_iff c.pub c.wit tr).mpr h
    claim_iff := S.claim_iff
    claimOut_iff := fun p w tr =>
      ⟨fun h => ⟨h.1, fun _ => by simpa only [MaskedReduction.combine, eval_combination] using h.2⟩,
        fun h => ⟨h.rows, by simpa only [MaskedReduction.combine, eval_combination] using h.claims 0⟩⟩ }

/-- **The simulator of claim combination**: the masked reduction's simulator, then the combination
challenge.

Running time: the masked reduction's simulator's and a copy of the challenge.
This running time is argued here, not proved in Lean. -/
def Sim.combine {M : MaskedReduction F ι Pub Wit cells Z nc} (S : M.Sim) : M.combine.Sim where
  SimCoins := S.SimCoins
  sim p ch s := Transcript.join (S.sim p ch.left s)
    ((CausalTranscript.oneChallenge (Fin nc → F)).transcript ch.right)

/-- **The honest prover of claim combination**: the masked reduction's prover, then the combination
challenge, simulated by `Sim.combine`. -/
def Honest.combine {M : MaskedReduction F ι Pub Wit cells Z nc} {view : (ι → F) → Z → F} {In : Type}
    {dom : Pub → In → Prop} {S : M.Sim} (H : M.Honest view In dom S) :
    M.combine.Honest view In dom S.combine where
  Pads := H.Pads
  prover p x π := (H.prover p x π).append fun _ => CausalTranscript.oneChallenge (Fin nc → F)
  Commits := H.Commits
  complete p x hx π w hw ch := by
    have e₁ := CausalTranscript.append_left (H.prover p x π)
      (fun _ => CausalTranscript.oneChallenge (Fin nc → F)) ch
    have h := (congrArg (fun tr => M.OutHolds view p tr (cells w)) e₁).mpr
      (H.complete p x hx π w hw ch.left)
    refine ⟨h.rows, fun _ => ?_⟩
    simp only [MaskedReduction.combine, eval_combination]
    exact Finset.sum_eq_zero fun c _ => mul_eq_zero_of_right _ (h.claims c)
  identDistrib p x ch := (H.identDistrib p x ch.left).comp fun v =>
    Transcript.join v ((CausalTranscript.oneChallenge (Fin nc → F)).transcript ch.right)

end FieldProof.MaskedReduction

/-! ### Honest masked reductions: precomposition and stronger commitments -/

section MaskedReductionHonest

variable {K ι Pub Wit V : Type} [Field K] [Fintype ι] {cells : Wit → ι → K} {nc : ℕ}
  {Mi : FieldProof.MaskedReduction K ι Pub Wit cells V nc} {view : (ι → K) → V → K} {In : Type}
  {dom : Pub → In → Prop} {S : Mi.Sim}

/-- **Precompose the honest input of a masked reduction**: an honest prover on `In` is one on `In'` through
`f`, on any domain `f` maps into `dom`. -/
def _root_.GordieHowe.FieldProof.MaskedReduction.Honest.comap (H : Mi.Honest view In dom S) {In' : Type}
    {dom' : Pub → In' → Prop} (f : Pub → In' → In) (hf : ∀ p x, dom' p x → dom p (f p x)) :
    Mi.Honest view In' dom' S where
  Pads := H.Pads
  prover p x := H.prover p (f p x)
  Commits p x := H.Commits p (f p x)
  complete p x hx := H.complete p (f p x) (hf p x hx)
  identDistrib p x := H.identDistrib p (f p x)

/-- **A stronger commitment condition** of an honest masked reduction: the same prover and simulator, the
committed witness also satisfying `P`. -/
def _root_.GordieHowe.FieldProof.MaskedReduction.Honest.withCommits (H : Mi.Honest view In dom S)
    (P : Pub → In → H.Pads → Wit → Prop) : Mi.Honest view In dom S where
  Pads := H.Pads
  prover := H.prover
  Commits p x π w := H.Commits p x π w ∧ P p x π w
  complete p x hx π w hw ch := H.complete p x hx π w hw.1 ch
  identDistrib := H.identDistrib

end MaskedReductionHonest

end GordieHowe
