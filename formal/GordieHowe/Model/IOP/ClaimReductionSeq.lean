-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.IOP.ClaimReduction

@[expose] public section

/-!
# Claim reductions in sequence, and conditional claims

`ClaimReduction.seq`: a reduction followed by a second reduction whose input claim is about the
first one's context and transcript, and implies the first one's output claim, is a reduction from
the first input claim to the second output claim; each round keeps its error. It is
`ClaimReduction.append` with the second reduction read as a claim proof whose verifier decides its
output claim (`toClaimProof`). A masked row reduction whose verifier leaves claims for a later phase
(`MaskedReduction`) composes with that phase this way.

`ClaimReduction.imp`: a reduction of `claim` to `claimOut` is one of `Q → claim` to
`Q → claimOut` for a fact `Q` about the context that no round changes, such as subfield
membership of committed masks that the commitment's subfield test supplies.
-/

namespace GordieHowe.IOP

open scoped NNReal

variable {n n₁ n₂ : ℕ}

namespace ClaimReduction

variable {P : ProtocolSpec n} {Ctx : Type} [∀ i, Fintype (P.Challenge i)]
  {ε : P.ChallengeIdx → ℝ≥0}

open Classical in
/-- **A reduction as a claim proof** whose verifier decides the output claim (classically). -/
noncomputable def toClaimProof (R : ClaimReduction P Ctx ε) : ClaimProof P Ctx ε where
  claim := R.claim
  V c tr := decide (R.claimOut c tr)
  S := R.S
  start := R.start
  next := R.next
  full c tr h := R.full c tr (of_decide_eq_true h)
  rbr := R.rbr

@[simp] theorem toClaimProof_claim (R : ClaimReduction P Ctx ε) (c : Ctx) :
    R.toClaimProof.claim c ↔ R.claim c :=
  Iff.rfl

open Classical in
/-- **A conditional claim.** For a fact `Q` about the context, the reduction of `claim` to
`claimOut` reduces `Q → claim` to `Q → claimOut` with the same errors: when `Q` fails the state is
true throughout, and when it holds the state is `R`'s. -/
def imp (R : ClaimReduction P Ctx ε) (Q : Ctx → Prop) : ClaimReduction P Ctx ε where
  claim c := Q c → R.claim c
  claimOut c tr := Q c → R.claimOut c tr
  S m c tr := Q c → R.S m c tr
  start c tr hc hS := by
    by_cases hq : Q c
    · exact R.start c tr (fun h => hc fun _ => h) (hS hq)
    · exact hc fun h => absurd h hq
  next m hdir c tr msg hnot hS := by
    by_cases hq : Q c
    · exact R.next m hdir c tr msg (fun h => hnot fun _ => h) (hS hq)
    · exact hnot fun h => absurd h hq
  full c tr h hq := R.full c tr (h hq)
  rbr c i tr := by
    by_cases hq : Q c
    · refine le_trans (Nat.cast_le.mpr (Finset.card_le_card ?_)) (R.rbr c i tr)
      intro ch hch
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hch ⊢
      exact ⟨fun h => hch.1 fun _ => h, hch.2 hq⟩
    · refine le_trans (Nat.cast_le.mpr (Finset.card_le_card (t := ∅) ?_)) (by simp)
      intro ch hch
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hch
      exact absurd (fun h => absurd h hq) hch.1

@[simp] theorem imp_claim (R : ClaimReduction P Ctx ε) (Q : Ctx → Prop) (c : Ctx) :
    (R.imp Q).claim c ↔ (Q c → R.claim c) :=
  Iff.rfl

@[simp] theorem imp_claimOut (R : ClaimReduction P Ctx ε) (Q : Ctx → Prop) (c : Ctx)
    (tr : P.Transcript (Fin.last n)) : (R.imp Q).claimOut c tr ↔ (Q c → R.claimOut c tr) :=
  Iff.rfl

variable {P₁ : ProtocolSpec n₁} {P₂ : ProtocolSpec n₂} [∀ i, Fintype (P₁.Challenge i)]
  [∀ i, Fintype (P₂.Challenge i)] {ε₁ : P₁.ChallengeIdx → ℝ≥0} {ε₂ : P₂.ChallengeIdx → ℝ≥0}

open ProtocolSpec

open Classical in
/-- **Two reductions in sequence.** `R₁` reduces its claim to its output claim; `R₂` reduces a claim
about `R₁`'s context and transcript that implies `R₁`'s output claim (`h`) to its own output claim.
In sequence they reduce `R₁`'s claim to `R₂`'s output claim on `R₁`'s transcript, and each round
keeps its error (`ClaimReduction.append` with `R₂.toClaimProof`). -/
noncomputable def seq (R₁ : ClaimReduction P₁ Ctx ε₁)
    (R₂ : ClaimReduction P₂ (AppendContext Ctx P₁) ε₂)
    (h : ∀ c tr, R₂.claim ⟨c, tr⟩ → R₁.claimOut c tr) :
    ClaimReduction (P₁ ++ P₂) Ctx (appendError ε₁ ε₂) where
  claim := R₁.claim
  claimOut c tr := R₂.claimOut ⟨c, tr.left⟩ tr.right
  S := (R₁.append R₂.toClaimProof h).S
  start := (R₁.append R₂.toClaimProof h).start
  next := (R₁.append R₂.toClaimProof h).next
  full c tr hc := (R₁.append R₂.toClaimProof h).full c tr (decide_eq_true hc)
  rbr := (R₁.append R₂.toClaimProof h).rbr

@[simp] theorem seq_claim (R₁ : ClaimReduction P₁ Ctx ε₁)
    (R₂ : ClaimReduction P₂ (AppendContext Ctx P₁) ε₂)
    (h : ∀ c tr, R₂.claim ⟨c, tr⟩ → R₁.claimOut c tr) (c : Ctx) :
    (R₁.seq R₂ h).claim c ↔ R₁.claim c :=
  Iff.rfl

@[simp] theorem seq_claimOut (R₁ : ClaimReduction P₁ Ctx ε₁)
    (R₂ : ClaimReduction P₂ (AppendContext Ctx P₁) ε₂)
    (h : ∀ c tr, R₂.claim ⟨c, tr⟩ → R₁.claimOut c tr) (c : Ctx)
    (tr : (P₁ ++ P₂).Transcript (Fin.last (n₁ + n₂))) :
    (R₁.seq R₂ h).claimOut c tr ↔ R₂.claimOut ⟨c, tr.left⟩ tr.right :=
  Iff.rfl

end ClaimReduction

end GordieHowe.IOP
