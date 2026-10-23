-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.FieldProof.MaskedReduction
public import GordieHowe.Model.IOP.FuseChallenges
public import GordieHowe.ProofSystem.FieldProof.UniformSim

@[expose] public section

/-!
# Masked reductions with two leading verifier moves fused

A masked reduction whose protocol is two verifier moves `a ∈ A`, `b ∈ B` followed by `Q` (`SpecIs`) is a
masked reduction on one verifier move `(a, b) ∈ A × B` followed by `Q` (`fuse`): the rows and the claims
are read on the original transcript (`GordieHowe.IOP.unfuseFull`). Its soundness (`Sound.fuse`) has the
error `ε₀ + ε₁` at the fused move and each later move's error (`GordieHowe.IOP.fuseError`,
`ClaimReduction.fuse`); its honest prover and simulator are the original ones read through the
transcript bijection `GordieHowe.IOP.fuseEquiv` (`Honest.fuse`, `Honest.fuse_sim`).
-/

namespace GordieHowe

open IOP IOP.ProtocolSpec GKR.Schedule
open scoped NNReal

variable {F ι : Type} [Field F] [Fintype ι] {Pub Wit Z : Type} {cells : Wit → ι → F} {nc : ℕ}
  {m : ℕ} {A B : Type} {Q : ProtocolSpec m}

namespace FieldProof.MaskedReduction

/-- **The protocol of a masked reduction is two verifier moves `A`, `B` followed by `Q`.** -/
abbrev SpecIs (M : MaskedReduction F ι Pub Wit cells Z nc) (A B : Type) (Q : ProtocolSpec m) : Prop :=
  (⟨M.n, M.spec⟩ : Σ n, ProtocolSpec n) = ⟨1 + (1 + m), orig A B Q⟩

variable [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
  [∀ i, Fintype (Q.Challenge i)] [∀ i, DecidableEq (Q.Challenge i)]
  [∀ i, Nonempty (Q.Challenge i)]

/-- **A masked reduction with its two leading verifier moves fused** into one move `(a, b) ∈ A × B`: the
rows, products and claims of `M`, read on the original transcript. -/
def fuse (M : MaskedReduction F ι Pub Wit cells Z nc) (hM : M.SpecIs A B Q) :
    MaskedReduction F ι Pub Wit cells Z nc where
  n := 1 + m
  spec := fused A B Q
  Lin := M.Lin
  linear p tr := M.linear p (specTranscript hM (unfuseFull tr))
  Q := M.Q
  products := M.products
  claims p tr := M.claims p (specTranscript hM (unfuseFull tr))

theorem outHolds_fuse_iff (M : MaskedReduction F ι Pub Wit cells Z nc) (hM : M.SpecIs A B Q)
    (view : (ι → F) → Z → F) (p : Pub) (tr : (fused A B Q).Transcript (Fin.last (1 + m)))
    (x : ι → F) :
    (M.fuse hM).OutHolds view p tr x ↔ M.OutHolds view p (specTranscript hM (unfuseFull tr)) x :=
  ⟨fun h => ⟨h.rows, h.claims⟩, fun h => ⟨h.rows, h.claims⟩⟩

/-- **Soundness with the two leading verifier moves fused**: the same relation, the error
`ε₀ + ε₁` at the fused move and each later move's error (`ClaimReduction.fuse`). -/
def Sound.fuse {M : MaskedReduction F ι Pub Wit cells Z nc} (hM : M.SpecIs A B Q)
    {view : (ι → F) → Z → F} {sat : Pub → Wit → Prop} {ε : M.spec.ChallengeIdx → ℝ≥0}
    (S : M.Sound view sat ε) : (M.fuse hM).Sound view sat (fuseError (ε ∘ specIdx hM)) where
  reduction := (ClaimReduction.ofSpecEq hM M.fintype inferInstance S.reduction).fuse
  claim_iff p w := (ClaimReduction.ofSpecEq_claim hM _ _ S.reduction _).trans (S.claim_iff p w)
  claimOut_iff p w tr :=
    (ClaimReduction.ofSpecEq_claimOut hM _ _ S.reduction _ _).trans
      ((S.claimOut_iff p w _).trans (outHolds_fuse_iff M hM view p tr _).symm)

/-- **The simulator with the two leading verifier moves fused**: `S` on the original challenges
(`IOP.unfuseChallenges`), read through the transcript bijection.

Running time: `S` and a relabelling of the transcript's first two entries. This running time is
argued here, not proved in Lean. -/
def Sim.fuse {M : MaskedReduction F ι Pub Wit cells Z nc} (hM : M.SpecIs A B Q) (S : M.Sim) :
    (M.fuse hM).Sim where
  SimCoins := S.SimCoins
  sim p ch s :=
    fuseEquiv A B Q (specTranscript hM.symm (S.sim p (specChallenges hM (unfuseChallenges ch)) s))

/-- **The honest prover with the two leading verifier moves fused**: the honest prover of `H`, on
the original challenges (`IOP.unfuseChallenges`), read through the transcript bijection, simulated
by `Sim.fuse`. -/
def Honest.fuse {M : MaskedReduction F ι Pub Wit cells Z nc} (hM : M.SpecIs A B Q)
    {view : (ι → F) → Z → F} {In : Type} {dom : Pub → In → Prop} {S : M.Sim}
    (H : M.Honest view In dom S) : (M.fuse hM).Honest view In dom (S.fuse hM) where
  Pads := H.Pads
  prover p x π := ((H.prover p x π).ofSpecEq hM).fuse
  Commits := H.Commits
  complete p x hx π w hw ch := by
    rw [outHolds_fuse_iff]
    change M.OutHolds view p (specTranscript hM (unfuseFull (fuseFull
      (((H.prover p x π).ofSpecEq hM).transcript (unfuseChallenges ch))))) _
    rw [unfuseFull_fuseFull, CausalTranscript.ofSpecEq_transcript, specTranscript_symm]
    exact H.complete p x hx π w hw _
  identDistrib p x ch := by
    have h := (H.identDistrib p x (specChallenges hM (unfuseChallenges ch))).comp
      fun tr => fuseEquiv A B Q (specTranscript hM.symm tr)
    have e : (fun π => (((H.prover p x π).ofSpecEq hM).fuse).transcript ch) =
        (fun tr => fuseEquiv A B Q (specTranscript hM.symm tr)) ∘
          fun π => (H.prover p x π).transcript (specChallenges hM (unfuseChallenges ch)) := by
      funext π
      exact (CausalTranscript.fuse_transcript _ ch).trans
        (congrArg _ (CausalTranscript.ofSpecEq_transcript hM _ _))
    rw [e]
    exact h

/-- **The fused simulator is the original simulator read through the transcript bijection**, on
the original challenges. -/
theorem Sim.fuse_sim {M : MaskedReduction F ι Pub Wit cells Z nc} (hM : M.SpecIs A B Q)
    (S : M.Sim) (p : Pub) (ch : (fused A B Q).Challenges) (s : S.SimCoins) :
    (S.fuse hM).sim p ch s =
      fuseEquiv A B Q (specTranscript hM.symm (S.sim p (specChallenges hM (unfuseChallenges ch)) s)) :=
  rfl

/-- **Fusing preserves a bijective simulator**: the fused simulator is the original one read
through the challenge bijection (`unfuseChallenges`, `specChallenges`) and the transcript bijection
(`specTranscript`, `fuseEquiv`), so it is the uniform simulator when the original one is
(`Honest.SimBijective.uniformHVZK`). -/
theorem Honest.SimBijective.fuse {M : MaskedReduction F ι Pub Wit cells Z nc} (hM : M.SpecIs A B Q)
    {view : (ι → F) → Z → F} {In : Type} {dom : Pub → In → Prop} {S : M.Sim}
    {H : M.Honest view In dom S} (h : H.SimBijective) : (H.fuse hM).SimBijective := by
  intro p
  have hc : Function.Bijective fun x : (fused A B Q).Challenges × S.SimCoins =>
      (specChallenges hM (unfuseChallenges x.1), x.2) :=
    ((specChallenges_bijective hM).comp unfuseChallenges_bijective).prodMap Function.bijective_id
  exact ((fuseEquiv A B Q).bijective.comp (specTranscript_bijective hM.symm)).comp ((h p).comp hc)

end FieldProof.MaskedReduction

end GordieHowe
