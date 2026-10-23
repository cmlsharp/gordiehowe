-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Keccak.HashCircuit.Skip
public import GordieHowe.ProofSystem.Ligero.Routing
public import GordieHowe.Foundations.Algebra.AffineForm
public import GordieHowe.Applications.Falcon512.Circuits.HashStep
public import GordieHowe.Applications.Keccak.HashCircuit.SkipCompleteness
public import GordieHowe.Foundations.Algebra.QuadraticSystem
public import GordieHowe.Applications.Keccak.HashCircuit.Packed.Basic
public import GordieHowe.ProofSystem.Ligero.Preparation
public import GordieHowe.ProofSystem.GKR.TranscriptRouting
public import GordieHowe.ProofSystem.GKR.SourceCircuit
public import GordieHowe.Foundations.ReedSolomon.AffineProximity
public import GordieHowe.Model.IOP.Append
public import GordieHowe.Applications.Rows.Basic
public import GordieHowe.Foundations.Probability.ChallengeEvent
public import GordieHowe.ProofSystem.GKR.HonestTranscript
public import GordieHowe.ProofSystem.Ligero.ShapeEncoding
public import GordieHowe.Foundations.ReedSolomon.SubfieldInterpolation
public import GordieHowe.ProofSystem.Ligero.PlacementHiding
public import GordieHowe.ProofSystem.Ligero.HVZK
public import GordieHowe.Model.IOP.Completeness
public import GordieHowe.Model.IOP.CompletenessAppend
public import GordieHowe.ProofSystem.RingSwitching.PackedClaim
public import GordieHowe.Model.IOP.AppendView
public import GordieHowe.Foundations.Probability.IdentDistrib

@[expose] public section

/-!
# Transcript extensionality for the batched-Keccak univariate-skip phase

A complete skip transcript is determined by its parts (`one_ext`, `split_ext`, `alt_ext`). The
hiding law of a masked honest phase is `GordieHowe.BatchedZerocheck.maskedPhase_identDistrib`.
-/

namespace GordieHowe.HashCircuit.Skip

open GordieHowe.KeccakTrace IOP GKR.Schedule Sumcheck.UnivariateSkip Packed.Opening

variable {K : Type} [Field K] {w n : ℕ}

/-! ### A complete skip transcript from its parts -/

section Ext

theorem one_ext {dir : Direction} {Msg : Type} {tr tr' : (one dir Msg).Transcript (Fin.last 1)}
    (h : oneValue tr = oneValue tr') : tr = tr' := by
  funext i
  have hi : i = ⟨0, by decide⟩ := Fin.ext (by have := i.isLt; simp at this; omega)
  subst hi
  exact h

theorem split_ext {n₁ n₂ : ℕ} {P₁ : ProtocolSpec n₁} {P₂ : ProtocolSpec n₂}
    {tr tr' : (P₁ ++ P₂).Transcript (Fin.last (n₁ + n₂))}
    (h₁ : tr.left = tr'.left) (h₂ : tr.right = tr'.right) : tr = tr' := by
  rw [← ProtocolSpec.Transcript.join_left_right tr, ← ProtocolSpec.Transcript.join_left_right tr', h₁, h₂]

theorem alt_ext (M C : Type) : (k : ℕ) → {tr tr' : (alt M C k).Transcript (Fin.last (roundLength k))} →
    altValues M C k tr = altValues M C k tr' → tr = tr'
  | 0, _, _, _ => funext fun i => i.elim0
  | k + 1, _, _, h => by
    have h0 := congrFun h 0
    simp only [altValues, Fin.cases_zero, Prod.mk.injEq] at h0
    exact split_ext (one_ext h0.1) (split_ext (one_ext h0.2)
      (alt_ext M C k (funext fun j => by simpa only [altValues, Fin.cases_succ] using congrFun h j.succ)))

end Ext

end GordieHowe.HashCircuit.Skip
