-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.FieldProof.MaskedReductionList
public import GordieHowe.ProofSystem.GKR.ScheduleFintype

@[expose] public section

/-!
# The uniform simulator of a masked reduction

The paper's `def:red-sec` (c) states honest-verifier zero
knowledge with error `0` **with respect to the uniform simulator**: the view (the uniform
challenges and the prover's messages, so the full transcript) at every statement and every
witness, under the honest masks, is distributed as the output of the algorithm that draws every
challenge uniformly and every prover message uniformly from its finite message set, independently,
that is, as a uniform full transcript.

A masked reduction's honest prover (`MaskedReduction.Honest`) carries a simulator `sim` with the law of the honest
transcript at each fixed challenge vector (`identDistrib`). Here:

* `MaskedReduction.Honest.SimBijective`: the simulator, as a function of the challenges and its coins, is a
  bijection onto the full transcripts. Every simulator of the batch, GKR and ring-switching masked
  reductions is one.
* `MaskedReduction.Honest.UniformSim`: the simulator under uniform challenges and coins is the uniform
  simulator (`SimBijective.uniformSim`).
* `MaskedReduction.Honest.UniformHVZK`: the honest transcript under uniform challenges and uniform pads is
  uniform, at every public input and every honest input; paper `def:red-sec` (c) with error `0`
  (`UniformSim.uniformHVZK`, from `identDistrib` at each challenge vector, joined over uniform
  challenges by `IdentDistrib.dependent`).
* The constructions of `GordieHowe/ProofSystem/FieldProof/MaskedReduction.lean` and `MaskedReductionList.lean` preserve
  `SimBijective`, and their protocols have finite, nonempty message types when their parts do.
-/

namespace GordieHowe

open IOP IOP.ProtocolSpec
open GKR.Schedule (one)

/-- The protocol with no moves has no message types. -/
instance FieldProof.MaskedRowReduction.noRounds_typeFintype : ∀ i, Fintype (MaskedRowReduction.noRounds.Type i) :=
  fun i => i.elim0

/-- The protocol with no moves has no message types. -/
instance FieldProof.MaskedRowReduction.noRounds_typeNonempty : ∀ i, Nonempty (MaskedRowReduction.noRounds.Type i) :=
  fun i => i.elim0

/-- The protocol with no moves has one full transcript and one challenge vector: its simulator
with one coin value is a bijection. -/
theorem FieldProof.MaskedRowReduction.noRounds_bijective {S : Type} [Subsingleton S] [Nonempty S]
    (f : MaskedRowReduction.noRounds.Challenges × S → MaskedRowReduction.noRounds.Transcript (Fin.last 0)) :
    Function.Bijective f := by
  obtain ⟨s⟩ := ‹Nonempty S›
  refine ⟨fun x y _ => Prod.ext (funext fun i => i.1.elim0) (Subsingleton.elim _ _),
    fun tr => ⟨(fun i => i.1.elim0, s), funext fun i => i.elim0⟩⟩

variable {F ι : Type} [Field F] [Fintype ι] {Pub Wit Z : Type} {cells : Wit → ι → F} {nc : ℕ}

namespace FieldProof.MaskedReduction

/-! ### The predicates -/

namespace Honest

variable {M : MaskedReduction F ι Pub Wit cells Z nc} {view : (ι → F) → Z → F} {In : Type}
  {dom : Pub → In → Prop} {S : M.Sim}

/-- **The simulator is a bijection**: at every public input, the simulated transcript, as a
function of the challenges and the simulator's coins, is a bijection onto the full transcripts. -/
def SimBijective (H : M.Honest view In dom S) : Prop :=
  ∀ p, Function.Bijective fun x : M.spec.Challenges × S.SimCoins => S.sim p x.1 x.2

/-- **The simulator is the uniform simulator** (paper `def:red-sec` (c)): at every public input,
the simulated transcript under uniform challenges and uniform coins is a uniform full transcript,
as the uniform simulator draws every challenge and every prover message uniformly and
independently. -/
def UniformSim (H : M.Honest view In dom S) [∀ i, Fintype (M.spec.Type i)]
    [∀ i, Nonempty (M.spec.Type i)] : Prop :=
  ∀ p, Uniform fun x : M.spec.Challenges × S.SimCoins => S.sim p x.1 x.2

/-- **Honest-verifier zero knowledge with error `0` with respect to the uniform simulator** (paper
`def:red-sec` (c)): at every public input `p` and every honest input `x`, the view (the full
transcript of the honest prover) under uniform challenges and uniform pads is a uniform full
transcript, the output of the uniform simulator. -/
def UniformHVZK (H : M.Honest view In dom S) [∀ i, Fintype (M.spec.Type i)]
    [∀ i, Nonempty (M.spec.Type i)] : Prop :=
  ∀ p x, Uniform fun y : M.spec.Challenges × H.Pads => (H.prover p x y.2).transcript y.1

variable {H : M.Honest view In dom S} [∀ i, Fintype (M.spec.Type i)]
  [∀ i, Nonempty (M.spec.Type i)]

/-- A bijective simulator is the uniform simulator. -/
theorem SimBijective.uniformSim (h : H.SimBijective) : H.UniformSim :=
  fun p => Uniform.of_equiv (Equiv.ofBijective _ (h p))

/-- **The view of a masked reduction with the uniform simulator is uniform**: at each challenge vector the
honest transcript under uniform pads has the simulator's law (`identDistrib`); over uniform
challenges the pair of the challenges and the transcript then has the law of the challenges and the
simulated transcript (`IdentDistrib.dependent`), whose transcript is uniform. -/
theorem UniformSim.uniformHVZK (hU : H.UniformSim) : H.UniformHVZK := fun p x =>
  ((IdentDistrib.dependent (f₁ := (id : M.spec.Challenges → M.spec.Challenges)) (g₁ := id)
      (f₂ := fun ch π => (H.prover p x π).transcript ch) (g₂ := fun ch s => S.sim p ch s)
      (IdentDistrib.refl _) fun ch => H.identDistrib p x ch).comp Prod.snd).trans (hU p)

/-- A masked reduction with a bijective simulator is honest-verifier zero knowledge with error `0` with
respect to the uniform simulator. -/
theorem SimBijective.uniformHVZK (h : H.SimBijective) : H.UniformHVZK :=
  h.uniformSim.uniformHVZK

end Honest

/-! ### Finite message types of the constructions -/

variable {n₁ n₂ : ℕ} {A : MaskedReduction F ι Pub Wit cells Z n₁} {B : MaskedReduction F ι Pub Wit cells Z n₂}

/-- The message types of two masked reductions in sequence are finite when those of both are. -/
instance append_typeFintype [∀ i, Fintype (A.spec.Type i)] [∀ i, Fintype (B.spec.Type i)] :
    ∀ i, Fintype ((A.append B).spec.Type i) :=
  ProtocolSpec.appendTypeFintype (P₁ := A.spec) (P₂ := B.spec)

/-- The message types of two masked reductions in sequence are nonempty when those of both are. -/
instance append_typeNonempty [∀ i, Nonempty (A.spec.Type i)] [∀ i, Nonempty (B.spec.Type i)] :
    ∀ i, Nonempty ((A.append B).spec.Type i) :=
  ProtocolSpec.appendTypeNonempty (P₁ := A.spec) (P₂ := B.spec)

/-- Fixed claims have no message types. -/
instance static_typeFintype {claims : Pub → Fin nc → AffineForm F Z} :
    ∀ i, Fintype ((static (ι := ι) (Wit := Wit) (cells := cells) claims).spec.Type i) :=
  MaskedRowReduction.noRounds_typeFintype

/-- Fixed claims have no message types. -/
instance static_typeNonempty {claims : Pub → Fin nc → AffineForm F Z} :
    ∀ i, Nonempty ((static (ι := ι) (Wit := Wit) (cells := cells) claims).spec.Type i) :=
  MaskedRowReduction.noRounds_typeNonempty

/-- Fixed claims with product triples have no message types. -/
instance staticProducts_typeFintype {Q : Type} [Fintype Q] [Encodable Q]
    {claims : Pub → Fin nc → AffineForm F Z} {products : Ligero.Routing.ProductLayout ι Q} :
    ∀ i, Fintype ((staticProducts (Wit := Wit) (cells := cells) claims products).spec.Type i) :=
  MaskedRowReduction.noRounds_typeFintype

/-- Fixed claims with product triples have no message types. -/
instance staticProducts_typeNonempty {Q : Type} [Fintype Q] [Encodable Q]
    {claims : Pub → Fin nc → AffineForm F Z} {products : Ligero.Routing.ProductLayout ι Q} :
    ∀ i, Nonempty ((staticProducts (Wit := Wit) (cells := cells) claims products).spec.Type i) :=
  MaskedRowReduction.noRounds_typeNonempty

section Combine

variable [Fintype F] [DecidableEq F] {M : MaskedReduction F ι Pub Wit cells Z nc}

/-- The message types of claim combination are finite when the masked reduction's are. -/
instance combine_typeFintype [∀ i, Fintype (M.spec.Type i)] :
    ∀ i, Fintype (M.combine.spec.Type i) :=
  ProtocolSpec.appendTypeFintype (P₁ := M.spec) (P₂ := one .V_to_P (Fin nc → F))

/-- The message types of claim combination are nonempty when the masked reduction's are. -/
instance combine_typeNonempty [∀ i, Nonempty (M.spec.Type i)] :
    ∀ i, Nonempty (M.combine.spec.Type i) :=
  ProtocolSpec.appendTypeNonempty (P₁ := M.spec) (P₂ := one .V_to_P (Fin nc → F))

end Combine

/-! ### The constructions preserve bijective simulators -/

namespace Honest

variable {view : (ι → F) → Z → F} {In : Type} {dom : Pub → In → Prop}

/-- **Two masked reductions in sequence** have a bijective simulator when both have. -/
theorem SimBijective.append {SA : A.Sim} {SB : B.Sim} {HA : A.Honest view In dom SA}
    {HB : B.Honest view (MaskedRowReduction.WithPads In HA.Pads) (fun p x => dom p x.input) SB}
    (hA : HA.SimBijective) (hB : HB.SimBijective) : (HA.append HB).SimBijective := fun p =>
  bijective_join (f₁ := fun y => SA.sim p y.1 y.2) (f₂ := fun y => SB.sim p y.1 y.2) (hA p) (hB p)

/-- **Fixed claims** have a bijective simulator. -/
theorem simBijective_static {claims : Pub → Fin nc → AffineForm F Z} (Commits : Pub → In → Wit → Prop)
    (hcomplete : ∀ p x, dom p x → ∀ w, Commits p x w →
      ∀ c, (claims p c).eval (view (cells w)) = 0) :
    (Honest.static (cells := cells) (view := view) (dom := dom) Commits hcomplete).SimBijective :=
  fun _ => MaskedRowReduction.noRounds_bijective (S := Unit) _

/-- **Fixed claims with product triples** have a bijective simulator. -/
theorem simBijective_staticProducts {Q : Type} [Fintype Q] [Encodable Q]
    {claims : Pub → Fin nc → AffineForm F Z} {products : Ligero.Routing.ProductLayout ι Q}
    (Commits : Pub → In → Wit → Prop)
    (hcomplete : ∀ p x, dom p x → ∀ w, Commits p x w →
      (∀ c, (claims p c).eval (view (cells w)) = 0) ∧
        Ligero.Routing.SourceProducts products (cells w)) :
    (Honest.staticProducts (claims := claims) (products := products) (view := view) (dom := dom)
      Commits hcomplete).SimBijective :=
  fun _ => MaskedRowReduction.noRounds_bijective (S := Unit) _

variable {M : MaskedReduction F ι Pub Wit cells Z nc} {S : M.Sim} {H : M.Honest view In dom S}

/-- **Claim combination** keeps a bijective simulator: the combination challenge is copied. -/
theorem SimBijective.combine [Fintype F] [DecidableEq F] (h : H.SimBijective) :
    H.combine.SimBijective := fun p =>
  bijective_join_unit (f₁ := fun y => S.sim p y.1 y.2)
    (f₂ := fun y => (CausalTranscript.oneChallenge (Fin nc → F)).transcript y.1) (h p)
    (CausalTranscript.valuesBijective_oneChallenge (Fin nc → F))

/-- **Precomposing the honest input** keeps the simulator. -/
theorem SimBijective.comap (h : H.SimBijective) {In' : Type} {dom' : Pub → In' → Prop}
    (f : Pub → In' → In) (hf : ∀ p x, dom' p x → dom p (f p x)) : (H.comap f hf).SimBijective :=
  h

/-- **A stronger commitment condition** keeps the simulator. -/
theorem SimBijective.withCommits (h : H.SimBijective) (P : Pub → In → H.Pads → Wit → Prop) :
    (H.withCommits P).SimBijective :=
  h

/-- **An equal logical assignment** keeps the simulator. -/
theorem SimBijective.congrView {view' : (ι → F) → Z → F} (hv : view = view')
    (h : H.SimBijective) : (H.congrView hv).SimBijective :=
  h

end Honest

end FieldProof.MaskedReduction

end GordieHowe
