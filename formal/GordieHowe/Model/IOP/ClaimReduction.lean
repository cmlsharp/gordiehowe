-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.IOP.Append

@[expose] public section

/-!
# Claim-reducing phases

A `ClaimReduction` is a phase that reduces a claim about its context to an
output claim about the context and its own transcript, round-by-round: its state
is false at the start when the input claim is false, is not made true by prover
messages, is true at the end when the output claim holds, and at every prefix at
most `ε i · |C_i|` challenges make it true from false. A `ClaimProof` is the case
where the output claim is the verifier's acceptance.

`ClaimReduction.append`: a reduction followed by a proof of a claim that implies
the reduction's output claim is a proof of the reduction's input claim, and each
round keeps its error. In the packed H proof, GKR reduces circuit satisfaction
on the decoded input to an input claim at its own challenge points, and Ligero
with the subfield check proves that input claim.

`ClaimReduction.andConst` conjoins a fact about the context that no round
changes, such as subfield membership of the committed packed values.
`ClaimReduction.and` runs two reductions on the same context in sequence and
reduces the conjunction of their claims.
-/

namespace GordieHowe.IOP

open scoped NNReal

variable {n n₁ n₂ : ℕ}

open Classical in
/-- A phase reducing a claim about a context to an output claim about the context
and the phase's transcript, round-by-round. -/
structure ClaimReduction (P : ProtocolSpec n) (Ctx : Type) [∀ i, Fintype (P.Challenge i)]
    (ε : P.ChallengeIdx → ℝ≥0) where
  /-- The input claim. -/
  claim : Ctx → Prop
  /-- The output claim. -/
  claimOut : Ctx → P.Transcript (Fin.last n) → Prop
  /-- The state function. -/
  S : (m : Fin (n + 1)) → Ctx → P.Transcript m → Prop
  /-- The state is false on the empty transcript when the input claim is false. -/
  start : ∀ c tr, ¬ claim c → ¬ S 0 c tr
  /-- A prover message does not make the state true. -/
  next : ∀ (m : Fin n), P.dir m = .P_to_V → ∀ c (tr : P.Transcript m.castSucc) msg,
    ¬ S m.castSucc c tr → ¬ S m.succ c (P.concat tr msg)
  /-- The state is true on a full transcript whose output claim holds. -/
  full : ∀ c tr, claimOut c tr → S (Fin.last n) c tr
  /-- At every prefix before a verifier round, at most `ε i · |C_i|` challenges make the state
  true from false. -/
  rbr : ∀ (c : Ctx) (i : P.ChallengeIdx) (tr : P.Transcript i.1.castSucc),
    ((Finset.univ.filter fun ch : P.Challenge i =>
        ¬ S i.1.castSucc c tr ∧ S i.1.succ c (P.concat tr ch)).card : ℝ≥0) ≤
      ε i * Fintype.card (P.Challenge i)

namespace ClaimReduction

variable {P : ProtocolSpec n} {Ctx : Type} [∀ i, Fintype (P.Challenge i)]
  {ε : P.ChallengeIdx → ℝ≥0}

/-- Instantiate a proved reduction on context data computed by its caller. -/
def comap {Ctx' : Type} (R : ClaimReduction P Ctx ε) (f : Ctx' → Ctx) :
    ClaimReduction P Ctx' ε where
  claim c := R.claim (f c)
  claimOut c tr := R.claimOut (f c) tr
  S m c tr := R.S m (f c) tr
  start c tr h := R.start (f c) tr h
  next m hm c tr msg h := R.next m hm (f c) tr msg h
  full c tr h := R.full (f c) tr h
  rbr c i tr := R.rbr (f c) i tr

/-- A functional compiler soundness theorem can identify the proved circuit
relation with a caller's source relation, without replacing the RBR proof. -/
def weakenClaim (R : ClaimReduction P Ctx ε) (claim : Ctx → Prop)
    (h : ∀ c, R.claim c → claim c) : ClaimReduction P Ctx ε where
  claim := claim
  claimOut := R.claimOut
  S := R.S
  start c tr hn := R.start c tr (fun hc => hn (h c hc))
  next := R.next
  full := R.full
  rbr := R.rbr

/-- Replace the output claim by a stronger one, `T`, without changing the input claim, the
state or the errors. -/
def strengthenOut (R : ClaimReduction P Ctx ε) (T : Ctx → P.Transcript (Fin.last n) → Prop)
    (h : ∀ c tr, T c tr → R.claimOut c tr) : ClaimReduction P Ctx ε where
  claim := R.claim
  claimOut := T
  S := R.S
  start := R.start
  next := R.next
  full c tr hT := R.full c tr (h c tr hT)
  rbr := R.rbr

/-- A state that is true at the start of a reduction implies its input claim. -/
theorem claim_of_S (R : ClaimReduction P Ctx ε) {c : Ctx} {tr : P.Transcript 0} (h : R.S 0 c tr) :
    R.claim c := by
  by_contra hc
  exact R.start c tr hc h

/-- Conjoin a fact `Q` about the context to the input claim, the output claim and the
state. No round changes `Q`, so the errors are unchanged. -/
def andConst (R : ClaimReduction P Ctx ε) (Q : Ctx → Prop) : ClaimReduction P Ctx ε where
  claim c := R.claim c ∧ Q c
  claimOut c tr := R.claimOut c tr ∧ Q c
  S m c tr := R.S m c tr ∧ Q c
  start c tr hc h := hc ⟨R.claim_of_S h.1, h.2⟩
  next m hdir c tr msg hnot h := R.next m hdir c tr msg (fun h' => hnot ⟨h', h.2⟩) h.1
  full c tr h := ⟨R.full c tr h.1, h.2⟩
  rbr c i tr := by
    refine le_trans (Nat.cast_le.mpr (Finset.card_le_card ?_)) (R.rbr c i tr)
    intro ch hch
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hch ⊢
    exact ⟨fun h' => hch.1 ⟨h', hch.2.2⟩, hch.2.1⟩

@[simp]
theorem andConst_claim (R : ClaimReduction P Ctx ε) (Q : Ctx → Prop) (c : Ctx) :
    (R.andConst Q).claim c ↔ R.claim c ∧ Q c :=
  Iff.rfl

variable {P₁ : ProtocolSpec n₁} {P₂ : ProtocolSpec n₂} [∀ i, Fintype (P₁.Challenge i)]
  [∀ i, Fintype (P₂.Challenge i)] {ε₁ : P₁.ChallengeIdx → ℝ≥0} {ε₂ : P₂.ChallengeIdx → ℝ≥0}

open ProtocolSpec

/-- At the start of part 2, the appended state gives the reduction's final state. -/
theorem appendStart (R : ClaimReduction P₁ Ctx ε₁) (B : ClaimProof P₂ (AppendContext Ctx P₁) ε₂)
    (h : ∀ c tr, B.claim ⟨c, tr⟩ → R.claimOut c tr) (c : Ctx) (tr₁ : P₁.Transcript (Fin.last n₁))
    (tr₂ : P₂.Transcript 0) (hS : R.S (Fin.last n₁) c tr₁ ∨ B.S 0 ⟨c, tr₁⟩ tr₂) :
    R.S (Fin.last n₁) c tr₁ :=
  hS.elim id fun hB => R.full c tr₁ (h c tr₁ (B.claim_of_S hB))

/-- **Append.** A reduction followed by a proof of a claim that implies its output claim
proves the reduction's input claim, and each round keeps its error. The state is `R.S`
during part 1, and `R.S` on the whole part-1 transcript or `B.S` on the part-2 transcript
during part 2. -/
def append (R : ClaimReduction P₁ Ctx ε₁) (B : ClaimProof P₂ (AppendContext Ctx P₁) ε₂)
    (h : ∀ c tr, B.claim ⟨c, tr⟩ → R.claimOut c tr) :
    ClaimProof (P₁ ++ P₂) Ctx (appendError ε₁ ε₂) where
  claim := R.claim
  V c tr := B.V ⟨c, tr.left⟩ tr.right
  S m c := appendState (fun k => R.S k c) (fun tr₁ k tr₂ => R.S (Fin.last n₁) c tr₁ ∨ B.S k ⟨c, tr₁⟩ tr₂) m
  start c tr hc hS := hc (R.claim_of_S (appendState_of_le (appendStart R B h c) (k₁ := 0) rfl hS))
  next m hdir c tr msg hnot := by
    induction m using Fin.addCases with
    | left j =>
      intro hS
      have hflip := appendState_flip_castAdd (appendStart R B h c) j tr msg hnot hS
      exact R.next j (by simpa using hdir) c (tr.fst j.castSucc (by simp))
        (cast (append_Type_castAdd j) msg) hflip.1 hflip.2
    | right j =>
      intro hS
      obtain ⟨hn, hs⟩ := (appendState_flip_natAdd j tr msg).mp ⟨hnot, hS⟩
      exact B.next j (by simpa using hdir) ⟨c, tr.fst (Fin.last n₁) (by simp)⟩
        (tr.snd j.castSucc (by simp)) (cast (append_Type_natAdd j) msg) (fun h' => hn (.inr h'))
        (hs.resolve_left fun h' => hn (.inl h'))
  full c tr hV :=
    (appendState_iff_of_eq_add (k₂ := Fin.last n₂) (by simp) tr).mpr
      (.inr (B.full ⟨c, tr.left⟩ tr.right hV))
  rbr c i tr := by
    rcases ChallengeIdx.inl_or_inr i with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [appendError_inl]
      refine card_le_of_mapsTo_cast (append_Challenge_inl j) (fun ch hch => ?_)
        (R.rbr c j (tr.fst j.1.castSucc (by simp)))
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hch ⊢
      exact appendState_flip_castAdd (appendStart R B h c) j.1 tr ch hch.1 hch.2
    · rw [appendError_inr]
      refine card_le_of_mapsTo_cast (append_Challenge_inr j) (fun ch hch => ?_)
        (B.rbr ⟨c, tr.fst (Fin.last n₁) (by simp)⟩ j (tr.snd j.1.castSucc (by simp)))
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hch ⊢
      obtain ⟨hn, hs⟩ := (appendState_flip_natAdd j.1 tr ch).mp hch
      exact ⟨fun h' => hn (.inr h'), hs.resolve_left fun h' => hn (.inl h')⟩

/-- **Two reductions in sequence on the same context** reduce the conjunction of their input
claims to the conjunction of their output claims, and each round keeps its error. The state is
`R₁`'s state on the part-1 transcript with `R₂`'s initial state, then `R₁`'s final state with
`R₂`'s state on the part-2 transcript. The same construction as `ClaimProof.and`. -/
def and (R₁ : ClaimReduction P₁ Ctx ε₁) (R₂ : ClaimReduction P₂ Ctx ε₂) :
    ClaimReduction (P₁ ++ P₂) Ctx (appendError ε₁ ε₂) where
  claim c := R₁.claim c ∧ R₂.claim c
  claimOut c tr := R₁.claimOut c tr.left ∧ R₂.claimOut c tr.right
  S m c := appendState (fun k tr₁ => R₁.S k c tr₁ ∧ R₂.claim c)
    (fun tr₁ k tr₂ => R₁.S (Fin.last n₁) c tr₁ ∧ R₂.S k c tr₂) m
  start c tr hc h := by
    have h0 := appendState_of_le (fun tr₁ tr₂ h => ⟨h.1, R₂.claim_of_S h.2⟩) (k₁ := 0) rfl h
    exact hc ⟨R₁.claim_of_S h0.1, h0.2⟩
  next m hdir c tr msg hnot := by
    induction m using Fin.addCases with
    | left j =>
      intro h
      have hflip := appendState_flip_castAdd (fun tr₁ tr₂ h => ⟨h.1, R₂.claim_of_S h.2⟩) j tr msg
        hnot h
      exact R₁.next j (by simpa using hdir) c (tr.fst j.castSucc (by simp))
        (cast (append_Type_castAdd j) msg) (fun h' => hflip.1 ⟨h', hflip.2.2⟩) hflip.2.1
    | right j =>
      intro h
      obtain ⟨hn, hs⟩ := (appendState_flip_natAdd j tr msg).mp ⟨hnot, h⟩
      exact R₂.next j (by simpa using hdir) c (tr.snd j.castSucc (by simp))
        (cast (append_Type_natAdd j) msg) (fun h' => hn ⟨hs.1, h'⟩) hs.2
  full c tr h :=
    (appendState_iff_of_eq_add (k₂ := Fin.last n₂) (by simp) tr).mpr
      ⟨R₁.full c _ h.1, R₂.full c _ h.2⟩
  rbr c i tr := by
    rcases ChallengeIdx.inl_or_inr i with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [appendError_inl]
      refine card_le_of_mapsTo_cast (append_Challenge_inl j) (fun ch hch => ?_)
        (R₁.rbr c j (tr.fst j.1.castSucc (by simp)))
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hch ⊢
      have hflip := appendState_flip_castAdd (fun tr₁ tr₂ h => ⟨h.1, R₂.claim_of_S h.2⟩) j.1 tr ch
        hch.1 hch.2
      exact ⟨fun h' => hflip.1 ⟨h', hflip.2.2⟩, hflip.2.1⟩
    · rw [appendError_inr]
      refine card_le_of_mapsTo_cast (append_Challenge_inr j) (fun ch hch => ?_)
        (R₂.rbr c j (tr.snd j.1.castSucc (by simp)))
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hch ⊢
      obtain ⟨hn, hs⟩ := (appendState_flip_natAdd j.1 tr ch).mp hch
      exact ⟨fun h' => hn ⟨hs.1, h'⟩, hs.2⟩

@[simp]
theorem and_claim (R₁ : ClaimReduction P₁ Ctx ε₁) (R₂ : ClaimReduction P₂ Ctx ε₂) (c : Ctx) :
    (R₁.and R₂).claim c ↔ R₁.claim c ∧ R₂.claim c :=
  Iff.rfl

@[simp]
theorem and_claimOut (R₁ : ClaimReduction P₁ Ctx ε₁) (R₂ : ClaimReduction P₂ Ctx ε₂) (c : Ctx)
    (tr : (P₁ ++ P₂).Transcript (Fin.last (n₁ + n₂))) :
    (R₁.and R₂).claimOut c tr ↔ R₁.claimOut c tr.left ∧ R₂.claimOut c tr.right :=
  Iff.rfl

@[simp]
theorem append_claim (R : ClaimReduction P₁ Ctx ε₁)
    (B : ClaimProof P₂ (AppendContext Ctx P₁) ε₂)
    (h : ∀ c tr, B.claim ⟨c, tr⟩ → R.claimOut c tr) (c : Ctx) :
    (R.append B h).claim c ↔ R.claim c :=
  Iff.rfl

end ClaimReduction

end GordieHowe.IOP
