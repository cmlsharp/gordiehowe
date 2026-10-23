-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.FieldProof.ClaimFix
public import GordieHowe.ProofSystem.FieldProof.MaskedReductionList
public import GordieHowe.Foundations.Algebra.AffineFormCoeff

@[expose] public section

/-!
# What the claims of a masked reduction read

The claims of a masked reduction read only the coordinates of `T` (`MaskedReduction.ReadsOnly`):
claim `c` has a nonzero coefficient only at coordinates of `T c`, at every public input and
transcript (`AffineForm.ReadsOnly`). A packing tree routes each claim to the stages of the nodes it
reads (`GordieHowe/ProofSystem/RingSwitching/RouteSupport.lean`).

The library: weakening (`ReadsOnly.mono`), every coordinate (`ReadsOnly.of_forall`), fixed claims
(`readsOnly_static`, `readsOnly_staticProducts`), two masked reductions side by side
(`ReadsOnly.append`) and a fixed transcript (`ReadsOnly.fixAt`).
-/

namespace GordieHowe.FieldProof.MaskedReduction

variable {F ι : Type} [Field F] [Fintype ι] {Pub Wit Z : Type} [DecidableEq Z]
  {cells : Wit → ι → F} {nc : ℕ}

/-- **The claims of a masked reduction read only `T`**: claim `c` reads only the coordinates of
`T c`, at every public input and transcript. -/
def ReadsOnly (M : MaskedReduction F ι Pub Wit cells Z nc) (T : Fin nc → Z → Prop) : Prop :=
  ∀ p tr c, (M.claims p tr c).ReadsOnly (T c)

theorem ReadsOnly.mono {M : MaskedReduction F ι Pub Wit cells Z nc} {T T' : Fin nc → Z → Prop}
    (h : M.ReadsOnly T) (hT : ∀ c z, T c z → T' c z) : M.ReadsOnly T' :=
  fun p tr c => (h p tr c).mono (hT c)

/-- **Every claim reads only `T`** when `T` holds everywhere. -/
theorem ReadsOnly.of_forall (M : MaskedReduction F ι Pub Wit cells Z nc) {T : Fin nc → Z → Prop}
    (hT : ∀ c z, T c z) : M.ReadsOnly T :=
  fun _ _ c => AffineForm.ReadsOnly.of_forall (hT c)

/-- **At a fixed transcript the claims read what they read.** -/
theorem ReadsOnly.fixAt {Pub' : Type} {M : MaskedReduction F ι Pub Wit cells Z nc}
    {T : Fin nc → Z → Prop} (h : M.ReadsOnly T) (pub : Pub' → Pub)
    (tr : Pub' → M.spec.Transcript (Fin.last M.n)) : (M.fixAt pub tr).ReadsOnly T :=
  fun p' _ c => h (pub p') (tr p') c

/-- **Fixed claims read what they read.** -/
theorem readsOnly_static {claims : Pub → Fin nc → AffineForm F Z} {T : Fin nc → Z → Prop}
    (h : ∀ p c, (claims p c).ReadsOnly (T c)) :
    (static (ι := ι) (Wit := Wit) (cells := cells) claims).ReadsOnly T :=
  fun p _ c => h p c

/-- **Fixed claims with product triples read what they read.** -/
theorem readsOnly_staticProducts {Q : Type} [Fintype Q] [Encodable Q]
    {claims : Pub → Fin nc → AffineForm F Z} {products : Ligero.Routing.ProductLayout ι Q}
    {T : Fin nc → Z → Prop} (h : ∀ p c, (claims p c).ReadsOnly (T c)) :
    (staticProducts (Wit := Wit) (cells := cells) claims products).ReadsOnly T :=
  fun p _ c => h p c

/-- **Two masked reductions side by side read what each reads.** -/
theorem ReadsOnly.append {n₁ n₂ : ℕ} {A : MaskedReduction F ι Pub Wit cells Z n₁}
    {B : MaskedReduction F ι Pub Wit cells Z n₂} {TA : Fin n₁ → Z → Prop} {TB : Fin n₂ → Z → Prop}
    (hA : A.ReadsOnly TA) (hB : B.ReadsOnly TB) : (A.append B).ReadsOnly (Fin.append TA TB) := by
  intro p tr c
  refine Fin.addCases (fun c => ?_) (fun c => ?_) c
  · change (Fin.append (A.claims p tr.left) (B.claims p tr.right) (Fin.castAdd n₂ c)).ReadsOnly _
    rw [Fin.append_left, Fin.append_left]
    exact hA p tr.left c
  · change (Fin.append (A.claims p tr.left) (B.claims p tr.right) (Fin.natAdd n₁ c)).ReadsOnly _
    rw [Fin.append_right, Fin.append_right]
    exact hB p tr.right c

/-- **A family on a list's claims** from a family on each entry's claims: the entries' in order. -/
def ofListFamily {β α : Type} {ncOf : β → ℕ} (f : (b : β) → Fin (ncOf b) → α) :
    (l : List β) → Fin (l.map ncOf).sum → α
  | [] => fun i => i.elim0
  | b :: l => Fin.append (f b) (ofListFamily f l)

/-- **A property of every entry's family holds of the list's.** -/
theorem ofListFamily_of {β α : Type} {ncOf : β → ℕ} {f : (b : β) → Fin (ncOf b) → α}
    {P : α → Prop} (h : ∀ b c, P (f b c)) : (l : List β) → ∀ c, P (ofListFamily f l c)
  | [] => fun c => c.elim0
  | b :: l => fun c => by
    refine Fin.addCases (m := ncOf b) (n := (l.map ncOf).sum)
      (motive := fun c => P (ofListFamily f (b :: l) c)) (fun c => ?_) (fun c => ?_) c
    · change P (Fin.append (f b) (ofListFamily f l) (Fin.castAdd _ c))
      rw [Fin.append_left]
      exact h b c
    · change P (Fin.append (f b) (ofListFamily f l) (Fin.natAdd _ c))
      rw [Fin.append_right]
      exact ofListFamily_of h l c

/-- **A list of masked reductions reads what each entry reads.** -/
theorem ReadsOnly.ofList {β α : Type} {ncOf : β → ℕ}
    {M : (b : β) → MaskedReduction F ι Pub Wit cells Z (ncOf b)} {f : (b : β) → Fin (ncOf b) → α}
    {S : α → Z → Prop} (h : ∀ b, (M b).ReadsOnly fun c => S (f b c)) :
    (l : List β) → (ofList M l).ReadsOnly fun c => S (ofListFamily f l c)
  | [] => fun _ _ c => c.elim0
  | b :: l => by
    refine ((h b).append (ReadsOnly.ofList h l)).mono fun c z hz => ?_
    refine Fin.addCases (fun c hz => ?_) (fun c hz => ?_) c hz
    · rw [Fin.append_left] at hz
      change S (Fin.append (f b) (ofListFamily f l) (Fin.castAdd _ c)) z
      rw [Fin.append_left]
      exact hz
    · rw [Fin.append_right] at hz
      change S (Fin.append (f b) (ofListFamily f l) (Fin.natAdd _ c)) z
      rw [Fin.append_right]
      exact hz

end GordieHowe.FieldProof.MaskedReduction
