-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.IOP.RBR

@[expose] public section

/-!
# Extractors composed with a statement-dependent map of witnesses

An extractor `E` for a relation `rel` composed with a map `f : Stmt → W → W'` that sends the
witnesses of `rel` to witnesses of `rel'` (`(x, w) ∈ rel → (x, f x w) ∈ rel'`) is an extractor for
`rel'` (`Extractor.mapWit`), and round-by-round knowledge soundness transfers at the same state
function and errors (`rbrKnowledgeSoundness.mapWit`): the event "the extractor fails" only shrinks.

Used where a system's extraction cannot read the statement (a GordieHowe lowering's projection
reads only the assignment) and the witness of the target relation needs a statement value, for
example the salt of a Falcon ring signature (`PQ/GordieHowe/FalconRingNative/`).
-/

namespace GordieHowe.IOP

open scoped NNReal

variable {n : ℕ} {P : ProtocolSpec n} {StmtIn W W' : Type}

/-- **An extractor followed by a statement-dependent map of witnesses**: at every prefix, `f x`
applied to `E`'s candidate.

Running time: `E`'s, then one evaluation of `f`. This running time is argued here, not proved in
Lean. -/
def Extractor.mapWit (E : Extractor P StmtIn W) (f : StmtIn → W → W') : Extractor P StmtIn W' where
  extract m x tr := f x (E m x tr)

open Classical in
/-- **Round-by-round knowledge soundness transfers along a map of witnesses**: if `f` sends the
witnesses of `rel` to witnesses of `rel'`, the extractor `E.mapWit f` is round-by-round knowledge
sound for `rel'` at the same state function and errors. -/
theorem rbrKnowledgeSoundness.mapWit [∀ i, Fintype (P.Challenge i)]
    [∀ i, Nonempty (P.Challenge i)] {rel : Set (StmtIn × W)} {rel' : Set (StmtIn × W')}
    {V : Verifier P StmtIn} {E : Extractor P StmtIn W} {S : KnowledgeStateFunction V}
    {ε : P.ChallengeIdx → ℝ≥0} (h : rbrKnowledgeSoundness rel V E S ε) {f : StmtIn → W → W'}
    (hf : ∀ x w, (x, w) ∈ rel → (x, f x w) ∈ rel') :
    rbrKnowledgeSoundness rel' V (E.mapWit f) S ε := by
  rw [rbrKnowledgeSoundness_iff_count] at h ⊢
  refine fun x i tr => le_trans ?_ (h x i tr)
  exact_mod_cast Finset.card_le_card fun c hc => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    exact ⟨fun hrel => hc.1 (hf _ _ hrel), hc.2⟩

end GordieHowe.IOP
