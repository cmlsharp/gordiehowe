-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.FieldProof.MaskedReduction

@[expose] public section

/-!
# A masked reduction at a fixed transcript

A forked domain proof (`GordieHowe/ProofSystem/FieldProof/Fork.lean`) runs its masked reductions as branches; its join part
reads their transcripts from its statement. The join's packing stages and Ligero then run on the
masked reduction **at the fixed transcript** (`MaskedReduction.fixAt`): no rounds, the same rows, products and
claims, read at the public input and the transcript the join's statement carries. The rows and
products keep their types, so the stages and the Ligero setup built on the masked reduction apply
unchanged.

* `MaskedReduction.fixAt M pub tr`: the masked reduction `M` on public inputs `Pub'`, read at `pub p'` and the
  transcript `tr p'`.
* `MaskedReduction.Sound.fixAt`: its output on the cells is `M`'s output at the fixed transcript; it is
  sound for any relation equivalent to that output, with no error (no rounds).
* `MaskedReduction.Honest.fixAt`: its honest prover sends nothing; completeness is `M`'s output at the
  fixed transcript on the committed cells of the honest inputs (`hcomplete`).
-/

namespace GordieHowe

open IOP IOP.ProtocolSpec
open scoped NNReal

variable {F ι : Type} [Field F] [Fintype ι] {Pub Pub' Wit Z : Type} {cells : Wit → ι → F} {nc : ℕ}

namespace FieldProof.MaskedReduction

/-- **A masked reduction at a fixed transcript** (module docstring). -/
def fixAt (M : MaskedReduction F ι Pub Wit cells Z nc) (pub : Pub' → Pub)
    (tr : Pub' → M.spec.Transcript (Fin.last M.n)) : MaskedReduction F ι Pub' Wit cells Z nc where
  n := 0
  spec := MaskedRowReduction.noRounds
  Lin := M.Lin
  linear p' _ := M.linear (pub p') (tr p')
  Q := M.Q
  products := M.products
  claims p' _ := M.claims (pub p') (tr p')

variable (M : MaskedReduction F ι Pub Wit cells Z nc) (pub : Pub' → Pub)
  (tr : Pub' → M.spec.Transcript (Fin.last M.n))

/-- **The output at a fixed transcript** is the masked reduction's output there. -/
theorem outHolds_fixAt_iff (view : (ι → F) → Z → F) (p' : Pub')
    (t : (M.fixAt pub tr).spec.Transcript (Fin.last (M.fixAt pub tr).n)) (x : ι → F) :
    (M.fixAt pub tr).OutHolds view p' t x ↔ M.OutHolds view (pub p') (tr p') x :=
  ⟨fun h => ⟨h.rows, h.claims⟩, fun h => ⟨h.rows, h.claims⟩⟩

/-- **Soundness at a fixed transcript**: for a relation `sat` equivalent to the masked reduction's output at
the fixed transcript on the committed cells (`hsat`), with no error. -/
def Sound.fixAt {view : (ι → F) → Z → F} {sat : Pub' → Wit → Prop}
    (hsat : ∀ p' w, sat p' w ↔ M.OutHolds view (pub p') (tr p') (cells w)) :
    (M.fixAt pub tr).Sound view sat fun i => i.1.elim0 where
  reduction :=
    { claim := fun c => sat c.pub c.wit
      claimOut := fun c _ => sat c.pub c.wit
      S := fun _ c _ => sat c.pub c.wit
      start := fun _ _ h => h
      next := fun m => m.elim0
      full := fun _ _ h => h
      rbr := fun _ i => i.1.elim0 }
  claim_iff _ _ := Iff.rfl
  claimOut_iff p' w t := (hsat p' w).trans (M.outHolds_fixAt_iff pub tr view p' t (cells w)).symm

/-- **The simulator at a fixed transcript**: no coins, the empty transcript.

Running time: constant. This running time is argued here, not proved in Lean. -/
def Sim.fixAt : (M.fixAt pub tr).Sim where
  SimCoins := Unit
  sim _ _ _ := fun i => i.elim0

/-- **The honest prover at a fixed transcript**: no pads and the empty transcript, simulated by
`Sim.fixAt`; completeness is the masked reduction's output at the fixed transcript on the cells the
honest inputs commit (`hcomplete`). -/
def Honest.fixAt {view : (ι → F) → Z → F} {In : Type} {dom : Pub' → In → Prop}
    (Commits : Pub' → In → Wit → Prop)
    (hcomplete : ∀ p' x, dom p' x → ∀ w, Commits p' x w →
      M.OutHolds view (pub p') (tr p') (cells w)) :
    (M.fixAt pub tr).Honest view In dom (Sim.fixAt M pub tr) where
  Pads := Unit
  prover _ _ _ := CausalTranscript.empty MaskedRowReduction.noRounds
  Commits p' x _ := Commits p' x
  complete p' x hx _ w hw _ :=
    (M.outHolds_fixAt_iff pub tr view p' _ (cells w)).mpr (hcomplete p' x hx w hw)
  identDistrib _ _ _ := IdentDistrib.of_equiv (Equiv.refl Unit) fun _ => funext fun i => i.elim0

end FieldProof.MaskedReduction

end GordieHowe
