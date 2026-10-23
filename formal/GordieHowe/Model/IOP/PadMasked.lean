-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Probability.IdentDistrib

@[expose] public section

/-!
# Pad-masked messages are uniform

Messages `t j = e j + P j`, one for each index `j` of a finite type `ι`, each in its own additive
group `M j` (the message's masking space: a field, a subfield, or a module over the masking
subfield), with pads `P j` independent and uniform over `M j`. The value `e j` is computed from the
witness, the challenges and the pads. **`PadMasked r e`** states the structural condition: `e j`
reads only the pads `P i` of the messages before `j` in the order `r`. The witness and the
challenges are fixed parameters of `e`, so the condition and its conclusion hold at every fixed
witness and challenge vector.

`PadMasked.uniform`: when the order `r` is well founded (any strict order on a finite type, for
example the order of the messages in the transcript), the message vector has the uniform law. The
map from pads to messages is triangular, hence injective (`PadMasked.injective`), hence a bijection
of the finite pad space.

Special cases and forms for the instances:
* `PadMasked.uniform_padFree`: no value reads a pad (the relation is empty);
* `PadMasked.uniform_of_sub`: stated on the messages, with `e j = t j - P j`;
* `PadMasked.uniform_prod`: two blocks of pads, the second block's values reading the first block's
  pads only (the MAC phase: the accumulators read the MAC pad, the target's pad).
-/

namespace GordieHowe.IOP

variable {ι : Type} {M : ι → Type}

/-- **Each value reads only earlier pads**: `e j` is unchanged when the pads `p i` of every
message `i` before `j` in the order `r` are unchanged. This is the pad order the GordieHowe core
checks (`lib/gordiehowe/system.h`, the pad-dependency check): no message depends on its own pad or
on the pad of a later message. -/
def PadMasked (r : ι → ι → Prop) (e : ∀ j, (∀ i, M i) → M j) : Prop :=
  ∀ j ⦃p p' : ∀ i, M i⦄, (∀ i, r i j → p i = p' i) → e j p = e j p'

namespace PadMasked

/-- **The messages**: each value plus its own pad. -/
def messages [∀ i, Add (M i)] (e : ∀ j, (∀ i, M i) → M j) (p : ∀ i, M i) : ∀ j, M j :=
  fun j => e j p + p j

@[simp] theorem messages_apply [∀ i, Add (M i)] (e : ∀ j, (∀ i, M i) → M j) (p : ∀ i, M i)
    (j : ι) : messages e p j = e j p + p j :=
  rfl

variable {r r' : ι → ι → Prop} {e : ∀ j, (∀ i, M i) → M j}

/-- Pads that agree before `j` give the same value at `j`. -/
theorem eq (h : PadMasked r e) (j : ι) {p p' : ∀ i, M i} (hp : ∀ i, r i j → p i = p' i) :
    e j p = e j p' :=
  h j hp

/-- A value that reads only earlier pads in a smaller order reads only earlier pads. -/
theorem mono (h : PadMasked r e) (hrr' : ∀ i j, r i j → r' i j) : PadMasked r' e :=
  fun j _ _ hp => h j fun i hi => hp i (hrr' i j hi)

/-- **Pad-free values**: with the empty order, the condition says that no value reads a pad. -/
theorem padFree_iff :
    PadMasked (fun _ _ => False) e ↔ ∀ j (p p' : ∀ i, M i), e j p = e j p' :=
  ⟨fun h j _ _ => h j fun _ hi => hi.elim, fun h j p p' _ => h j p p'⟩

/-- Values that read no pad read only earlier pads, in every order. -/
theorem of_padFree (h : ∀ j (p p' : ∀ i, M i), e j p = e j p') : PadMasked r e :=
  (padFree_iff.mpr h).mono fun _ _ hi => hi.elim

/-- **The triangular map is injective**: by well-founded induction along `r`, equal messages have
equal pads, since each value is determined by the earlier pads and the message then determines
the pad. -/
theorem injective [∀ i, AddGroup (M i)] (hr : WellFounded r) (h : PadMasked r e) :
    Function.Injective (messages e) := by
  intro p p' hpp'
  funext j
  induction j using hr.induction with
  | _ j ih =>
    have hj := congrFun hpp' j
    simp only [messages_apply] at hj
    rw [h j ih] at hj
    exact add_left_cancel hj

variable [Fintype ι] [DecidableEq ι] [∀ i, AddGroup (M i)] [∀ i, Fintype (M i)]

/-- **Pad-masked messages are uniform.** Messages `e j p + p j` whose values read only earlier
pads in a well-founded order `r` have the uniform law under uniform pads `p`: the triangular map
is a bijection of the finite pad space. -/
theorem uniform (hr : WellFounded r) (h : PadMasked r e) : Uniform (messages e) :=
  Uniform.of_equiv (Equiv.ofBijective _ (h.injective hr).bijective_of_finite)

/-- **Pad-free messages are uniform**: messages whose values read no pad. -/
theorem uniform_padFree (h : ∀ j (p p' : ∀ i, M i), e j p = e j p') : Uniform (messages e) :=
  uniform (r := fun _ _ => False) ⟨fun j => ⟨j, fun _ hi => hi.elim⟩⟩ (of_padFree h)

/-- **Pad-masked messages, stated on the messages**: a message map `t` whose message minus its
own pad, `t p j - p j`, reads only earlier pads is uniform. -/
theorem uniform_of_sub {t : (∀ i, M i) → ∀ j, M j} (hr : WellFounded r)
    (h : PadMasked r fun j p => t p j - p j) : Uniform t := by
  have ht : messages (fun j p => t p j - p j) = t := funext fun p => funext fun j => by
    simp
  exact ht ▸ h.uniform hr

end PadMasked

/-- **Two blocks of pad-masked messages are uniform**: on pads `(g, h)` in `G × H`, messages
`t₁ g h` and `t₂ g h` where `t₁ g h - g` reads no pad and `t₂ g h - h` reads the first block's pad
`g` only. This is `PadMasked.uniform_of_sub` on the two-element index `Fin 2` with `0` before `1`,
read through `piFinTwoEquiv`. -/
theorem PadMasked.uniform_prod {G H : Type} [AddGroup G] [AddGroup H] [Fintype G] [Fintype H]
    {t₁ : G → H → G} {t₂ : G → H → H} (h₁ : ∀ g h g' h', t₁ g h - g = t₁ g' h' - g')
    (h₂ : ∀ g h h', t₂ g h - h = t₂ g h' - h') :
    Uniform fun p : G × H => (Function.uncurry t₁ p, Function.uncurry t₂ p) := by
  let M : Fin 2 → Type := ![G, H]
  let _ : ∀ i, AddGroup (M i) := Fin.cases ‹AddGroup G› (Fin.cases ‹AddGroup H› finZeroElim)
  let _ : ∀ i, Fintype (M i) := Fin.cases ‹Fintype G› (Fin.cases ‹Fintype H› finZeroElim)
  let e : (∀ i, M i) ≃ G × H := piFinTwoEquiv M
  let t : G × H → G × H := fun p => (Function.uncurry t₁ p, Function.uncurry t₂ p)
  let t' : (∀ i, M i) → ∀ i, M i := fun p => e.symm (t (e p))
  have ht' : Uniform t' := by
    refine PadMasked.uniform_of_sub (r := fun i j => i < j)
      (Finite.wellFounded_of_trans_of_irrefl _) fun j p p' hp => ?_
    match j with
    | 0 => exact h₁ (p 0) (p 1) (p' 0) (p' 1)
    | 1 =>
      have h0 : p 0 = p' 0 := hp 0 (by decide)
      exact (h₂ (p 0) (p 1) (p' 1)).trans (by rw [h0]; rfl)
  have hcomp : t = e ∘ t' ∘ e.symm := funext fun p => by simp [t']
  change Uniform t
  rw [hcomp]
  exact ((ht'.comp_equiv e.symm).comp e).trans (IdentDistrib.of_equiv e fun _ => rfl)

end GordieHowe.IOP
