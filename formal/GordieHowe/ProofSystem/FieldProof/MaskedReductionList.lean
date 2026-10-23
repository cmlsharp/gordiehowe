-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.FieldProof.MaskedReduction

@[expose] public section

/-!
# Lists of masked reductions, and fixed claims with product triples

Two constructions on masked reductions (`GordieHowe/ProofSystem/FieldProof/MaskedReduction.lean`) that a domain with any number of
subprotocols needs:

* **Fixed claims with product triples** (`MaskedReduction.staticProducts`): no rounds, the claims `claims p`
  on the logical coordinates and the product triples `products` on the cells, fixed by the public
  input; the quadratic equalities a domain assigns to Ligero's quadratic test are such triples.
  Soundness (`Sound.staticProducts`) has no error; the honest prover (`Honest.staticProducts`) has no
  pads.
* **A list of masked reductions in sequence** (`MaskedReduction.ofList`): the masked reductions `M b` of the entries `b` of a
  list, appended in order (`MaskedReduction.append`), the empty masked reduction for the empty list. Soundness
  (`Sound.ofList`) is the conjunction of the relations (`ListSat`), each round with its masked reduction's
  error (`ofListError`, summing to the sum of the masked reductions' errors, `sum_ofListError`); the honest
  prover (`Honest.ofList`) runs the honest provers in order on the same honest input.
-/

namespace GordieHowe

open IOP IOP.ProtocolSpec
open scoped NNReal

variable {F ι : Type} [Field F] [Fintype ι] {Pub Wit Z : Type} {cells : Wit → ι → F}

namespace FieldProof.MaskedReduction

/-! ### Fixed claims with product triples -/

/-- **Fixed claims with product triples as a masked reduction**: no rounds, no affine rows on the cells, the
product triples `products` on the cells and the claims `claims p` on the logical coordinates, fixed
by the public input. -/
def staticProducts {nc : ℕ} {Q : Type} [Fintype Q] [Encodable Q]
    (claims : Pub → Fin nc → AffineForm F Z)
    (products : Ligero.Routing.ProductLayout ι Q) : MaskedReduction F ι Pub Wit cells Z nc where
  toMaskedRowReduction := MaskedRowReduction.static (fun _ (e : Empty) => e.elim) products
  claims p _ := claims p

theorem outHolds_staticProducts_iff {nc : ℕ} {Q : Type} [Fintype Q] [Encodable Q]
    (claims : Pub → Fin nc → AffineForm F Z) (products : Ligero.Routing.ProductLayout ι Q)
    (view : (ι → F) → Z → F) (p : Pub)
    (tr : (staticProducts (Wit := Wit) (cells := cells) claims products).spec.Transcript
      (Fin.last (staticProducts (Wit := Wit) (cells := cells) claims products).n)) (x : ι → F) :
    (staticProducts (cells := cells) claims products).OutHolds view p tr x ↔
      (∀ c, (claims p c).eval (view x) = 0) ∧ Ligero.Routing.SourceProducts products x :=
  ⟨fun h => ⟨h.claims, h.rows.products⟩, fun h => ⟨⟨fun e => e.elim, h.2⟩, h.1⟩⟩

/-- **Soundness of fixed claims with product triples**: the relation is the claims on the logical
assignment of the committed cells and the product triples on the cells (`hsat`), with no error. -/
def Sound.staticProducts {nc : ℕ} {Q : Type} [Fintype Q] [Encodable Q]
    {claims : Pub → Fin nc → AffineForm F Z}
    {products : Ligero.Routing.ProductLayout ι Q} {view : (ι → F) → Z → F}
    {sat : Pub → Wit → Prop}
    (hsat : ∀ p w, sat p w ↔ (∀ c, (claims p c).eval (view (cells w)) = 0) ∧
      Ligero.Routing.SourceProducts products (cells w)) :
    (MaskedReduction.staticProducts (cells := cells) claims products).Sound view sat fun i => i.1.elim0 where
  reduction :=
    { claim := fun c => sat c.pub c.wit
      claimOut := fun c _ => sat c.pub c.wit
      S := fun _ c _ => sat c.pub c.wit
      start := fun _ _ h => h
      next := fun m => m.elim0
      full := fun _ _ h => h
      rbr := fun _ i => i.1.elim0 }
  claim_iff _ _ := Iff.rfl
  claimOut_iff p w tr :=
    (hsat p w).trans (outHolds_staticProducts_iff claims products view p tr (cells w)).symm

/-- **The simulator of fixed claims with product triples**: no coins, the empty transcript.

Running time: constant. This running time is argued here, not proved in Lean. -/
def Sim.staticProducts {nc : ℕ} {Q : Type} [Fintype Q] [Encodable Q]
    (claims : Pub → Fin nc → AffineForm F Z) (products : Ligero.Routing.ProductLayout ι Q) :
    (MaskedReduction.staticProducts (Wit := Wit) (cells := cells) claims products).Sim where
  SimCoins := Unit
  sim _ _ _ := fun i => i.elim0

/-- **The honest prover of fixed claims with product triples**: no pads and the empty transcript,
simulated by `Sim.staticProducts`; completeness is the claims and the triples on the committing
witnesses (`hcomplete`). -/
def Honest.staticProducts {nc : ℕ} {Q : Type} [Fintype Q] [Encodable Q]
    {claims : Pub → Fin nc → AffineForm F Z}
    {products : Ligero.Routing.ProductLayout ι Q} {view : (ι → F) → Z → F} {In : Type}
    {dom : Pub → In → Prop} (Commits : Pub → In → Wit → Prop)
    (hcomplete : ∀ p x, dom p x → ∀ w, Commits p x w →
      (∀ c, (claims p c).eval (view (cells w)) = 0) ∧
        Ligero.Routing.SourceProducts products (cells w)) :
    (MaskedReduction.staticProducts (cells := cells) claims products).Honest view In dom
      (Sim.staticProducts claims products) where
  Pads := Unit
  prover _ _ _ := CausalTranscript.empty MaskedRowReduction.noRounds
  Commits p x _ := Commits p x
  complete p x hx _ w hw _ := (outHolds_staticProducts_iff claims products view p _ (cells w)).mpr
    (hcomplete p x hx w hw)
  identDistrib _a _b _c := IdentDistrib.of_equiv (Equiv.refl Unit) fun _ => funext fun i => i.elim0

/-! ### A list of masked reductions in sequence -/

variable {β : Type} {ncOf : β → ℕ}

/-- **The masked reductions of a list's entries in sequence** (`append`), the empty masked reduction (no rounds, no
rows, no claims) for the empty list. -/
def ofList (M : (b : β) → MaskedReduction F ι Pub Wit cells Z (ncOf b)) :
    (l : List β) → MaskedReduction F ι Pub Wit cells Z (l.map ncOf).sum
  | [] => static (nc := 0) fun _ => Fin.elim0
  | b :: l => (M b).append (ofList M l)

/-- **The conjunction of the entries' relations** over a list. -/
def ListSat (sat : β → Pub → Wit → Prop) : List β → Pub → Wit → Prop
  | [], _, _ => True
  | b :: l, p, w => sat b p w ∧ ListSat sat l p w

theorem listSat_iff (sat : β → Pub → Wit → Prop) :
    (l : List β) → ∀ p w, ListSat sat l p w ↔ ∀ b ∈ l, sat b p w
  | [], _, _ => by simp [ListSat]
  | b :: l, p, w => by simp [ListSat, listSat_iff sat l p w]

variable (M : (b : β) → MaskedReduction F ι Pub Wit cells Z (ncOf b))

/-- **The round errors of a list of masked reductions**: each masked reduction's errors at its own rounds
(`appendError`). -/
def ofListError (ε : (b : β) → (M b).spec.ChallengeIdx → ℝ≥0) :
    (l : List β) → (ofList M l).spec.ChallengeIdx → ℝ≥0
  | [] => fun i => i.1.elim0
  | b :: l => appendError (ε b) (ofListError ε l)

/-- **The errors of a list of masked reductions sum to the sum of the masked reductions' errors.** -/
theorem sum_ofListError (ε : (b : β) → (M b).spec.ChallengeIdx → ℝ≥0) :
    (l : List β) → ∑ i, ofListError M ε l i = (l.map fun b => ∑ i, ε b i).sum
  | [] => by
    simp only [List.map_nil, List.sum_nil]
    exact Finset.sum_eq_zero fun i _ => i.1.elim0
  | b :: l => by
    have h : (((b :: l).map fun b => ∑ i, ε b i).sum) =
        ∑ i, ε b i + (l.map fun b => ∑ i, ε b i).sum := List.sum_cons
    rw [h, ← sum_ofListError ε l]
    exact sum_appendError (ε b) (ofListError M ε l)

variable {M} in
/-- **A bound on every masked reduction's round errors bounds every round error of the list**
(`appendError_le`). -/
theorem ofListError_le {ε : (b : β) → (M b).spec.ChallengeIdx → ℝ≥0} {δ : ℝ≥0}
    (h : ∀ b i, ε b i ≤ δ) : (l : List β) → ∀ i, ofListError M ε l i ≤ δ
  | [] => fun i => i.1.elim0
  | b :: l => appendError_le (h b) (ofListError_le h l)

variable {M}

/-- **Soundness of a list of masked reductions**: the conjunction of the relations (`ListSat`), each round
with its masked reduction's error (`Sound.append`). -/
def Sound.ofList {view : (ι → F) → Z → F} {sat : β → Pub → Wit → Prop}
    {ε : (b : β) → (M b).spec.ChallengeIdx → ℝ≥0} (S : ∀ b, (M b).Sound view (sat b) (ε b)) :
    (l : List β) → (MaskedReduction.ofList M l).Sound view (ListSat sat l) (ofListError M ε l)
  | [] => Sound.static (cells := cells) fun _ _ => ⟨fun _ c => c.elim0, fun _ => trivial⟩
  | b :: l => (S b).append (Sound.ofList S l)

/-- **The simulators of a list of masked reductions**, in order (`Sim.append`), the empty simulator
for the empty list.

Running time: the masked reductions' simulators' and the concatenations.
This running time is argued here, not proved in Lean. -/
def Sim.ofList (S : ∀ b, (M b).Sim) : (l : List β) → (MaskedReduction.ofList M l).Sim
  | [] => Sim.static (Wit := Wit) (cells := cells) fun _ => Fin.elim0
  | b :: l => (S b).append (Sim.ofList S l)

/-- **The honest provers of a list of masked reductions**, in order on the same honest input
(`Honest.append`; each later prover ignores the earlier pads, `Honest.comap`), simulated by
`Sim.ofList`. -/
def Honest.ofList {view : (ι → F) → Z → F} {In : Type} {dom : Pub → In → Prop}
    {S : ∀ b, (M b).Sim} (H : ∀ b, (M b).Honest view In dom (S b)) :
    (l : List β) → (MaskedReduction.ofList M l).Honest view In dom (Sim.ofList S l)
  | [] => Honest.static (cells := cells) (fun _ _ _ => True) fun _a _b _c _d _e c => c.elim0
  | b :: l => (H b).append ((Honest.ofList H l).comap (fun _ x => x.input) fun _ _ h => h)

/-- **An honest masked reduction at an equal logical assignment**: the same prover, pads, commitment and
simulator. -/
def Honest.congrView {nc : ℕ} {M' : MaskedReduction F ι Pub Wit cells Z nc} {view view' : (ι → F) → Z → F}
    {In : Type} {dom : Pub → In → Prop} {S : M'.Sim} (h : view = view') (H : M'.Honest view In dom S) :
    M'.Honest view' In dom S where
  Pads := H.Pads
  prover := H.prover
  Commits := H.Commits
  complete := h ▸ H.complete
  identDistrib := H.identDistrib

/-- **The pads of entry `b`** among the honest provers of a list (at its first occurrence). -/
def Honest.ofListPads [DecidableEq β] {view : (ι → F) → Z → F} {In : Type} {dom : Pub → In → Prop}
    {S : ∀ b, (M b).Sim} (H : ∀ b, (M b).Honest view In dom (S b)) :
    (l : List β) → (Honest.ofList H l).Pads → (b : β) → b ∈ l → (H b).Pads
  | [], _, _, hb => absurd hb List.not_mem_nil
  | b' :: l, π, b, hb =>
    if h : b = b' then cast (congrArg (fun b => (H b).Pads) h.symm) π.1
    else Honest.ofListPads H l π.2 b ((List.mem_cons.1 hb).resolve_left h)

/-- **The honest provers of a list commit every entry's pads**, for a list without repetitions. -/
theorem Honest.commits_ofList_iff [DecidableEq β] {view : (ι → F) → Z → F} {In : Type}
    {dom : Pub → In → Prop} {S : ∀ b, (M b).Sim} (H : ∀ b, (M b).Honest view In dom (S b)) :
    (l : List β) → l.Nodup → ∀ p x π w, (Honest.ofList H l).Commits p x π w ↔
      ∀ b (hb : b ∈ l), (H b).Commits p x (Honest.ofListPads H l π b hb) w
  | [], _, _, _, _, _ => ⟨fun _ b hb => absurd hb List.not_mem_nil, fun _ => trivial⟩
  | b' :: l, hnd, p, x, π, w => by
    change (H b').Commits p x π.1 w ∧ (Honest.ofList H l).Commits p x π.2 w ↔ _
    rw [Honest.commits_ofList_iff H l (List.nodup_cons.1 hnd).2 p x π.2 w]
    constructor
    · rintro ⟨h1, h2⟩ b hb
      by_cases h : b = b'
      · subst h
        simp only [ofListPads, ↓reduceDIte, cast_eq]
        exact h1
      · rw [ofListPads, dif_neg h]
        exact h2 b _
    · intro h
      refine ⟨?_, fun b hb => ?_⟩
      · have := h b' List.mem_cons_self
        simp only [ofListPads, ↓reduceDIte, cast_eq] at this
        exact this
      · have hne : b ≠ b' := fun e => (List.nodup_cons.1 hnd).1 (e ▸ hb)
        have := h b (List.mem_cons_of_mem _ hb)
        rwa [ofListPads, dif_neg hne] at this

/-- **The full transcript of a list of masked reductions** from each entry's full transcript, joined in
order (`Transcript.join`). -/
def ofListTranscript (trs : ∀ b, (M b).spec.Transcript (Fin.last (M b).n)) :
    (l : List β) → (MaskedReduction.ofList M l).spec.Transcript (Fin.last (MaskedReduction.ofList M l).n)
  | [] => fun i => i.elim0
  | b :: l => Transcript.join (trs b) (ofListTranscript trs l)

/-- **The output of a list of masked reductions at the joined transcripts** is every entry's output at its
own transcript. -/
theorem outHolds_ofList_iff (view : (ι → F) → Z → F) (p : Pub)
    (trs : ∀ b, (M b).spec.Transcript (Fin.last (M b).n)) (x : ι → F) :
    (l : List β) → ((MaskedReduction.ofList M l).OutHolds view p (ofListTranscript trs l) x ↔
      ∀ b ∈ l, (M b).OutHolds view p (trs b) x)
  | [] => by
    simp only [List.not_mem_nil, false_implies, implies_true, iff_true]
    exact (outHolds_static_iff (ι := ι) (Wit := Wit) (cells := cells) (nc := 0)
      (fun _ => Fin.elim0) view p _ x).mpr fun c => c.elim0
  | b :: l => by
    refine (outHolds_append_iff (M b) (MaskedReduction.ofList M l) view p _ x).trans ?_
    erw [Transcript.left_join, Transcript.right_join]
    rw [outHolds_ofList_iff view p trs x l, List.forall_mem_cons]

end FieldProof.MaskedReduction

end GordieHowe
