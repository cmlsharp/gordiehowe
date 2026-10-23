-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Export.PackingTree
public import GordieHowe.ProofSystem.RingSwitching.PackingUniform
public import GordieHowe.Headline

@[expose] public section

/-!
# Ring switching along a packing tree, in the form of the paper's theorem

The paper's theorem on ring switching along a packing tree (`thm:tree`, in Appendix C.2, Ring
switching along a packing tree) states the tree's stages alone, run on fixed linear claims on the
stored values: (1) a reduction from those claims to linear claims and product constraints on the
committed data and membership claims on the mask entries, with round error `1/|K|` at each
combination challenge; (2) completeness; (3) honest-verifier zero knowledge with error `0`.

The Lean proves the stages as a transformation of a masked reduction (`GordieHowe.RingSwitching.Tree.run`, `GordieHowe.RingSwitching.Tree.soundRun`,
`GordieHowe.RingSwitching.Tree.honestRun`, `GordieHowe/ProofSystem/RingSwitching/PackingTree.lean`), with the mask condition as a hypothesis of
the input relation. This file instantiates it at fixed claims (`MaskedReduction.static`, no rounds, no
pads), which is the paper's protocol:

* `RingSwitching.Tree.ringSwitch P claims`: the stages of `P` on the fixed claims `claims`.
* `GordieHowe.RingSwitching.Tree.ringSwitchReduction`: part (1), a round-by-round reduction from "the claims hold on the
  logical assignment of the committed cells" to "the output rows and claims hold on the cells and
  every stage's mask condition holds" (`MasksValid`: subfield masks in `S0`), obtained by moving the
  mask condition from the input to the output (`ClaimReduction.sideToOut`).
* `GordieHowe.RingSwitching.Tree.ringSwitchError_le`, `GordieHowe.RingSwitching.Tree.sum_ringSwitchError`: at most `1/|K|` at every challenge,
  `combinations/|K| ≤ stages/|K|` in all (`GordieHowe.RingSwitching.Tree.combinations_le_stages`); equality with the
  number of stages when every stage combines every claim (`GordieHowe.RingSwitching.Tree.AllCombine`).
* `GordieHowe.RingSwitching.Tree.ringSwitchHonest`: parts (2) and (3), the honest run with its completeness at every pad
  value and its perfect simulation; part (3) is stated with respect to the uniform simulator of
  paper `def:red-sec` (c): the honest transcript under uniform challenges and pads is uniform
  (`MaskedReduction.Honest.UniformHVZK`).
-/

namespace GordieHowe

open scoped NNReal

namespace IOP.ClaimReduction

variable {n : ℕ} {P : ProtocolSpec n} {Ctx : Type} [∀ i, Fintype (P.Challenge i)]
  {ε : P.ChallengeIdx → ℝ≥0}

/-- **Moving a side condition from the input claim to the output claim**: a reduction from
"`side` implies `claim₀`" to `claimOut` is a reduction from `claim₀` to "`claimOut` and `side`",
with the same round errors (the state function is conjoined with `side`, which no message or
challenge changes). -/
def sideToOut (R : ClaimReduction P Ctx ε) (claim₀ side : Ctx → Prop)
    (h : ∀ c, R.claim c ↔ (side c → claim₀ c)) : ClaimReduction P Ctx ε where
  claim := claim₀
  claimOut c tr := R.claimOut c tr ∧ side c
  S m c tr := R.S m c tr ∧ side c
  start c tr h0 hs := R.start c tr (fun hc => h0 ((h c).1 hc hs.2)) hs.1
  next m hm c tr msg hn hs := R.next m hm c tr msg (fun h' => hn ⟨h', hs.2⟩) hs.1
  full c tr hc := ⟨R.full c tr hc.1, hc.2⟩
  rbr c i tr := by
    refine le_trans ?_ (R.rbr c i tr)
    exact_mod_cast Finset.card_le_card fun ch hch => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and] at hch ⊢
      exact ⟨fun h' => hch.1 h' hch.2.2, hch.2.1⟩

theorem sideToOut_claim (R : ClaimReduction P Ctx ε) (claim₀ side : Ctx → Prop)
    (h : ∀ c, R.claim c ↔ (side c → claim₀ c)) (c : Ctx) :
    (R.sideToOut claim₀ side h).claim c ↔ claim₀ c :=
  Iff.rfl

theorem sideToOut_claimOut (R : ClaimReduction P Ctx ε) (claim₀ side : Ctx → Prop)
    (h : ∀ c, R.claim c ↔ (side c → claim₀ c)) (c : Ctx) (tr : P.Transcript (Fin.last n)) :
    (R.sideToOut claim₀ side h).claimOut c tr ↔ R.claimOut c tr ∧ side c :=
  Iff.rfl

end IOP.ClaimReduction

section

open IOP IOP.ProtocolSpec PackingStage RelativePacking
open scoped NNReal

variable {F ι : Type} [Field F] [Fintype ι] {p : ℕ} [ExpChar F p]

namespace RingSwitching.Tree

/-- **The number of stages** (the non-root nodes of the tree, the paper's `N`). -/
def stages : {V : Type} → {nc : ℕ} → Tree F p ι V nc → ℕ
  | _, _, .nil => 0
  | _, _, (@Tree.cons _ _ _ _ _ _ _ _ _ _ _ _ _ rest) => rest.stages + 1
  | _, _, (@Tree.route _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rest) => rest.stages + 1

/-- **Every stage combines every claim** (`cons` throughout): one combination challenge per
stage. -/
def AllCombine : {V : Type} → {nc : ℕ} → Tree F p ι V nc → Prop
  | _, _, .nil => True
  | _, _, (@Tree.cons _ _ _ _ _ _ _ _ _ _ _ _ _ rest) => rest.AllCombine
  | _, _, (@Tree.route _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) => False

omit [Fintype ι] in
/-- **At most one combination per stage.** -/
theorem combinations_le_stages {V : Type} {nc : ℕ} (P : Tree F p ι V nc) :
    P.combinations ≤ P.stages := by
  induction P with
  | nil => exact le_rfl
  | cons S rest ih => exact Nat.succ_le_succ ih
  | route S R rest ih =>
    change rest.combinations + R.combinations ≤ rest.stages + 1
    have : R.combinations ≤ 1 := by cases R <;> simp [StageRouting.combinations]
    omega

omit [Fintype ι] in
/-- **One combination per stage** when every stage combines every claim. -/
theorem combinations_eq_stages {V : Type} {nc : ℕ} {P : Tree F p ι V nc}
    (h : P.AllCombine) : P.combinations = P.stages := by
  induction P with
  | nil => rfl
  | cons S rest ih => exact congrArg (· + 1) (ih h)
  | route S R rest ih => exact h.elim

variable [Fintype F] [DecidableEq F] {Pub Wit : Type} {cells : Wit → ι → F}

/-- **Every round error of the run is at most `c`** when the masked reduction's are and `1/|F| ≤ c`: each
stage adds `1/|F|` at its combination challenge, if any, and nothing at its measurement. -/
theorem runError_le {c : ℝ≥0} (hF : 1 / (Fintype.card F : ℝ≥0) ≤ c) : {V : Type} → {nc : ℕ} →
    (P : Tree F p ι V nc) → (M : FieldProof.MaskedReduction F ι Pub Wit cells V nc) →
    (ε : M.spec.ChallengeIdx → ℝ≥0) → (∀ i, ε i ≤ c) → ∀ i, P.runError M ε i ≤ c
  | _, _, .nil, _, _, hε => hε
  | _, _, (@Tree.cons _ _ _ _ _ _ _ _ _ _ _ _ _ rest), _, _, hε =>
    runError_le hF rest _ _
      (appendError_le (appendError_le hε fun _ => hF) fun _ => zero_le)
  | _, _, (@Tree.route _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (.none _) rest), _, _, hε =>
    runError_le hF rest _ _ (appendError_le hε fun _ => zero_le)
  | _, _, (@Tree.route _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (.single _) rest), _, _, hε =>
    runError_le hF rest _ _ (appendError_le hε fun _ => zero_le)
  | _, _, (@Tree.route _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (.combine _ _) rest), _, _, hε =>
    runError_le hF rest _ _
      (appendError_le (appendError_le hε fun _ => hF) fun _ => zero_le)

/-! ### The stages on fixed claims -/

variable {V : Type} {nc : ℕ} (P : Tree F p ι V nc) (claims : Pub → Fin nc → AffineForm F V)

/-- **Ring switching along the tree** (the paper's protocol `prot:tree`): the stages of `P` run on
the fixed linear claims `claims` on the logical coordinates (`MaskedReduction.static`). -/
def ringSwitch : FieldProof.MaskedReduction F ι Pub Wit cells ι P.outClaims :=
  P.run (FieldProof.MaskedReduction.static claims)

/-- **The round errors of ring switching**: those of the run on the fixed claims, which have no
rounds. -/
noncomputable def ringSwitchError :
    (P.ringSwitch (cells := cells) claims).spec.ChallengeIdx → ℝ≥0 :=
  P.runError (FieldProof.MaskedReduction.static claims) fun i => i.1.elim0

/-- **The input relation of ring switching**: the claims hold on the logical assignment read from
the committed cells. -/
def ClaimsHold (pub : Pub) (x : ι → F) : Prop :=
  ∀ c, (claims pub c).eval (P.level.view x) = 0

/-- **Ring switching is sound** in the Lean form: for "every stage's mask condition implies the
claims", with the run's errors (`soundRun` at `MaskedReduction.Sound.static`). -/
noncomputable def ringSwitchSound (hR : P.Routes (FieldProof.MaskedReduction.static (cells := cells) claims)) :
    (P.ringSwitch (cells := cells) claims).Sound (Level.base (F := F)).view
      (fun pub w => P.MasksValid (cells w) → P.ClaimsHold claims pub (cells w))
      (P.ringSwitchError claims) :=
  P.soundRun (FieldProof.MaskedReduction.Sound.static (sat := fun pub w => P.ClaimsHold claims pub (cells w))
    fun _ _ => Iff.rfl) hR

/-- **The reduction of the paper's theorem, part (1)**: from the claims on the logical assignment
of the committed cells (`ringSwitchReduction_claim`) to the output rows and claims on the cells
together with every stage's mask condition (`ringSwitchReduction_claimOut`), round by round with
the errors `ringSwitchError`. -/
noncomputable def ringSwitchReduction (hR : P.Routes (FieldProof.MaskedReduction.static (cells := cells) claims)) :
    ClaimReduction (P.ringSwitch (cells := cells) claims).spec (FieldProof.MaskedRowReduction.Instance Pub Wit)
      (P.ringSwitchError claims) :=
  (P.ringSwitchSound claims hR).reduction.sideToOut
    (fun c => P.ClaimsHold claims c.pub (cells c.wit)) (fun c => P.MasksValid (cells c.wit))
    fun c => (P.ringSwitchSound claims hR).claim_iff c.pub c.wit

theorem ringSwitchReduction_claim (hR : P.Routes (FieldProof.MaskedReduction.static (cells := cells) claims))
    (pub : Pub) (w : Wit) :
    (P.ringSwitchReduction claims hR).claim ⟨pub, w⟩ ↔ P.ClaimsHold claims pub (cells w) :=
  Iff.rfl

theorem ringSwitchReduction_claimOut (hR : P.Routes (FieldProof.MaskedReduction.static (cells := cells) claims))
    (pub : Pub) (w : Wit) (tr : (P.ringSwitch (cells := cells) claims).spec.Transcript
      (Fin.last (P.ringSwitch (cells := cells) claims).n)) :
    (P.ringSwitchReduction claims hR).claimOut ⟨pub, w⟩ tr ↔
      (P.ringSwitch claims).OutHolds (Level.base (F := F)).view pub tr (cells w) ∧
        P.MasksValid (cells w) :=
  and_congr_left' ((P.ringSwitchSound claims hR).claimOut_iff pub w tr)

/-- **Round error at most `1/|K|` at every challenge** of ring switching. -/
theorem ringSwitchError_le (i : (P.ringSwitch (cells := cells) claims).spec.ChallengeIdx) :
    P.ringSwitchError claims i ≤ 1 / Fintype.card F :=
  P.runError_le le_rfl _ _ (fun i => i.1.elim0) i

/-- **The round errors of ring switching sum to `combinations/|K|`.** -/
theorem sum_ringSwitchError :
    ∑ i, P.ringSwitchError (cells := cells) claims i = P.combinations / Fintype.card F := by
  refine (P.sum_runError (FieldProof.MaskedReduction.static claims) _).trans ?_
  simp only [add_eq_right]
  exact Finset.sum_eq_zero fun i _ => i.1.elim0

/-- **The soundness error of ring switching is at most `N/|K|`**, `N` the number of stages. -/
theorem sum_ringSwitchError_le :
    ∑ i, P.ringSwitchError (cells := cells) claims i ≤ P.stages / Fintype.card F := by
  rw [sum_ringSwitchError]
  gcongr
  exact_mod_cast P.combinations_le_stages

/-- **A full transcript of ring switching.** -/
abbrev RingSwitchTranscript :=
  (P.ringSwitch (cells := cells) claims).spec.Transcript
    (Fin.last (P.ringSwitch (cells := cells) claims).n)

/-- **The guarantees of part (1) of the paper's theorem `thm:tree`** for the round-by-round
reduction `ringSwitchReduction` (a `ClaimReduction` with round errors `ringSwitchError`): its input
claim is "the claims hold on the logical assignment of the committed cells" (`claim_iff`), its
output claim is "the output rows and claims hold on the cells and every stage's mask condition
holds" (`claimOut_iff`), every round error is at most `1/|K|` (`error_le`), the errors sum to
`combinations/|K|` (`sum_error`), there is at most one combination per stage
(`combinations_le_stages`), so the sum is at most `N/|K|` (`sum_error_le`), and there is exactly one
combination per stage when every stage combines every claim (`combinations_eq_stages`). -/
structure RingSwitchReduces (hR : P.Routes (FieldProof.MaskedReduction.static (cells := cells) claims)) : Prop where
  /-- The input claim: the fixed claims on the logical assignment of the committed cells. -/
  claim_iff : ∀ pub w,
    (P.ringSwitchReduction claims hR).claim ⟨pub, w⟩ ↔ P.ClaimsHold claims pub (cells w)
  /-- The output claim: the output rows and claims on the cells, and every mask condition. -/
  claimOut_iff : ∀ pub w (tr : P.RingSwitchTranscript (cells := cells) claims),
    (P.ringSwitchReduction claims hR).claimOut ⟨pub, w⟩ tr ↔
      (P.ringSwitch claims).OutHolds (Level.base (F := F)).view pub tr (cells w) ∧
        P.MasksValid (cells w)
  /-- Round error at most `1/|K|` at every challenge. -/
  error_le : ∀ i, P.ringSwitchError (cells := cells) claims i ≤ 1 / Fintype.card F
  /-- The round errors sum to `combinations/|K|`. -/
  sum_error : ∑ i, P.ringSwitchError (cells := cells) claims i = P.combinations / Fintype.card F
  /-- The soundness error is at most `N/|K|`. -/
  sum_error_le : ∑ i, P.ringSwitchError (cells := cells) claims i ≤ P.stages / Fintype.card F
  /-- At most one combination per stage. -/
  combinations_le_stages : P.combinations ≤ P.stages
  /-- One combination per stage when every stage combines every claim. -/
  combinations_eq_stages : P.AllCombine → P.combinations = P.stages

/-- **Paper `thm:tree`, part (1)**: ring switching along a packing tree on fixed linear claims is a
round-by-round reduction (`ringSwitchReduction`) from the claims on the stored values to the output
rows and claims on the committed cells and every stage's mask condition, with round error at most
`1/|K|` at every challenge, at most one combination per stage, and soundness error
`combinations/|K| ≤ N/|K|`, with equality when every stage combines every claim. -/
@[headline]
theorem reduces (hR : P.Routes (FieldProof.MaskedReduction.static (cells := cells) claims)) :
    P.RingSwitchReduces claims hR where
  claim_iff := P.ringSwitchReduction_claim claims hR
  claimOut_iff := P.ringSwitchReduction_claimOut claims hR
  error_le := P.ringSwitchError_le claims
  sum_error := P.sum_ringSwitchError claims
  sum_error_le := P.sum_ringSwitchError_le claims
  combinations_le_stages := P.combinations_le_stages
  combinations_eq_stages := combinations_eq_stages

/-! ### The honest run on fixed claims -/

variable {In : Type} {dom : Pub → In → Prop}

/-- **The simulator of ring switching** (`simRun` at `MaskedReduction.Sim.static`).

Running time: a copy of each combination challenge and uniform measurements per stage. This running
time is argued here, not proved in Lean. -/
def ringSwitchSim : (P.ringSwitch (cells := cells) claims).Sim :=
  P.simRun (FieldProof.MaskedReduction.Sim.static (cells := cells) claims)

/-- **The honest prover of ring switching** (`honestRun` at `MaskedReduction.Honest.static`),
simulated by `ringSwitchSim`: on committed cells related to the honest input by `Commits`, on which the
claims hold for inputs in the domain (`hcomplete`), with the honest masks of every stage and the
words' values `val`, which the committed cells match at every word (`hval`). Its fields give the
paper's parts (2) and (3) (`complete`, `hvzk`). -/
def ringSwitchHonest (hR : P.Routes (FieldProof.MaskedReduction.static (cells := cells) claims))
    (Commits : Pub → In → Wit → Prop)
    (hcomplete : ∀ pub x, dom pub x → ∀ w, Commits pub x w → P.ClaimsHold claims pub (cells w))
    (MH : P.MaskHonest) (val : Pub → In → V → F)
    (hval : ∀ pub x w, Commits pub x w → ∀ z, P.IsWord z → P.level.view (cells w) z = val pub x z) :
    (P.ringSwitch (cells := cells) claims).Honest (Level.base (F := F)).view In dom
      (P.ringSwitchSim claims) :=
  P.honestRun hR (FieldProof.MaskedReduction.Honest.static Commits hcomplete) MH (fun pub x _ => val pub x)
    fun pub x _ w hw => hval pub x w hw

variable (hR : P.Routes (FieldProof.MaskedReduction.static (cells := cells) claims)) (Commits : Pub → In → Wit → Prop)
  (hcomplete : ∀ pub x, dom pub x → ∀ w, Commits pub x w → P.ClaimsHold claims pub (cells w))
  (MH : P.MaskHonest) (val : Pub → In → V → F)
  (hval : ∀ pub x w, Commits pub x w → ∀ z, P.IsWord z → P.level.view (cells w) z = val pub x z)

/-- **Paper `thm:tree`, part (2)**: completeness of ring switching in the Lean form: for every
honest input in the domain, every value of the stages' pads and every committed cells holding them
(the honest run's `Commits`, which gives every stage's mask condition and products), the output rows
and claims hold on the cells at every challenge. -/
@[headline]
theorem complete {pub : Pub} {x : In} (hx : dom pub x)
    (π : (P.ringSwitchHonest claims hR Commits hcomplete MH val hval).Pads) {w : Wit}
    (hw : (P.ringSwitchHonest claims hR Commits hcomplete MH val hval).Commits pub x π w)
    (ch : (P.ringSwitch (cells := cells) claims).spec.Challenges) :
    (P.ringSwitch claims).OutHolds (Level.base (F := F)).view pub
      (((P.ringSwitchHonest claims hR Commits hcomplete MH val hval).prover pub x π).transcript ch)
      (cells w) :=
  (P.ringSwitchHonest claims hR Commits hcomplete MH val hval).complete pub x hx π w hw ch

/-- The message types of ring switching are finite. -/
instance ringSwitch_typeFintype :
    ∀ i, Fintype ((P.ringSwitch (cells := cells) claims).spec.Type i) :=
  inferInstanceAs (∀ i, Fintype ((P.run (FieldProof.MaskedReduction.static (cells := cells) claims)).spec.Type i))

/-- The message types of ring switching are nonempty. -/
instance ringSwitch_typeNonempty :
    ∀ i, Nonempty ((P.ringSwitch (cells := cells) claims).spec.Type i) :=
  inferInstanceAs (∀ i, Nonempty ((P.run (FieldProof.MaskedReduction.static (cells := cells) claims)).spec.Type i))

/-- **Paper `thm:tree`, part (3)**: honest-verifier zero knowledge of ring switching with error `0`
with respect to the uniform simulator (paper `def:red-sec` (c)): at every public input and every
honest input, the honest transcript under uniform challenges and uniform pads is a uniform full
transcript. -/
@[headline]
theorem hvzk : (P.ringSwitchHonest claims hR Commits hcomplete MH val hval).UniformHVZK :=
  (P.honestRun_simBijective hR (FieldProof.MaskedReduction.Honest.simBijective_static Commits hcomplete) MH _
    _).uniformHVZK

end RingSwitching.Tree

end

end GordieHowe
