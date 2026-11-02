-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Knowledge
public import GordieHowe.SPBCS.Extractor
public import GordieHowe.SPBCS.Extraction.KnowledgeError
public import GordieHowe.Model.QROM.QueryBits
public import GordieHowe.Model.QROM.QueryCount
public import GordieHowe.Model.ROM.Model

@[expose] public section

/-!
# Knowledge soundness of the spBCS compiler in the ROM

The classical counterpart of `GordieHowe/SPBCS/Knowledge.lean` (paper `thm:bcs-ks`(2)): a classical
`t`-query algorithm followed by the query expansion of the spBCS verifier; the log lies in
`bad ∪ P_col` with probability at most `knowledgeErrorROM k (t + kq) c nJ κ`, which is
`(t + kq)(κ + (max 2 c + nJ + 1)(t + kq) / 2^(8k))` (the classical union bound over the steps at the
flip bound read through the final digests), and every accepted claim whose log the database
extractor fails on lies there (`mem_of_game`). The joint form (`knowledge_of_causalRBR_rom_joint`,
CY24 Definition 5.1.1); online extractability against the lazily sampled oracle is in
`GordieHowe/SPBCS/Online.lean`.
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm
open scoped ENNReal NNReal BigOperators

variable {ι : Type} {t : SPTerm ι} {Mg : Merges t} {k kN kS L e : ℕ} {n : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (n j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] {X : Type}

section

variable [∀ j i, Nonempty ((P j).Challenge i)] {Wit : Type} (M : SPBCS Mg P X k kN kS L e)
  {V : X → FullTr P t → Bool} (rel : Set (X × Wit)) (E : CausalExtractor P t X Wit)
  (St : CausalStateFn P t X) {ε : ChIdx P t → ℝ≥0}

/-- **The log of a classical `tq`-query algorithm lies in `bad ∪ P_col`** with probability at
most `knowledgeErrorROM k tq c_in nJ (max_c ε c)`. -/
theorem prob_log_bad_union_le (hrbr : CausalRBRKnowledgeSound rel V E St ε) {C : Type}
    {tq : ℕ} (𝒜 : ROM.Alg (Query k kN kS L) (Out k e) C tq) :
    Pr[h ← (Query k kN kS L → Out k e) : 𝒜.log h tq ∈ M.bad rel E St ∪ digestCollision] ≤
      knowledgeErrorROM k tq M.senc.digestsPerInput Mg.nJ (maxError ε) := by
  have h0 : (∅ : ODB k kN kS L e) ∉ M.bad rel E St ∪ digestCollision := fun h =>
    h.elim (M.empty_notMem_bad rel E St) empty_notMem_collisionOn
  refine (𝒜.prob_log_mem_le h0).trans ?_
  rw [knowledgeErrorROM]
  gcongr
  calc flipProb (M.bad rel E St ∪ digestCollision)ᶜ (M.bad rel E St ∪ digestCollision) tq
      ≤ condFlip (M.bad rel E St) digestCollisionᶜ tq +
          flipProb digestCollisionᶜ digestCollision tq :=
        ROM.flipProb_compl_union_le
    _ ≤ (maxError ε + (((max 2 M.senc.digestsPerInput + Mg.nJ) * tq : ℕ) : ℝ≥0∞) /
          2 ^ (8 * k)) + (tq : ℝ≥0∞) / 2 ^ (8 * k) :=
        add_le_add (M.condFlip_bad_le rel E St hrbr)
          (flipProb_compl_le_instab.trans instab_digestCollision_le)
    _ = _ := by
        rw [add_assoc, ENNReal.div_add_div_same, ← Nat.cast_add, add_mul _ 1, one_mul]

/-- **Knowledge soundness of the spBCS argument in the ROM, joint form** (CY24 Definition
5.1.1, p. 48): the probability that the spBCS verifier accepts the claim of `𝒜` and the
database extractor at `E` returns no witness from the log of `𝒜` followed by the verifier's `kq`
queries is at most `knowledgeErrorROM k (t + kq) c_in nJ κ`. -/
theorem knowledge_of_causalRBR_rom_joint [DecidableEq X] (Qs : ∀ x, M.IOPQueries V x)
    (hrbr : CausalRBRKnowledgeSound rel V E St ε) {κ : ℝ≥0} (hκ : ∀ c, ε c ≤ κ) {kq : ℕ}
    (hkq : ∀ x h π, M.Accepts h x π (Qs x) → (M.queries x π h (Qs x)).length ≤ kq) {tq : ℕ}
    (𝒜 : ROM.Alg (Query k kN kS L) (Out k e) (Claim X M.NIProof) tq) :
    Pr[h ← (Query k kN kS L → Out k e) :
        M.Accepts h (𝒜.output h).stmt (𝒜.output h).proof (Qs (𝒜.output h).stmt) ∧
        (𝒜.append (M.expansion Qs) kq).log h (tq + kq) ∉ M.extracts rel E (𝒜.output h).stmt] ≤
      knowledgeErrorROM k (tq + kq) M.senc.digestsPerInput Mg.nJ κ := by
  set Xp := M.expansion Qs
  calc Pr[h ← (Query k kN kS L → Out k e) :
        M.Accepts h (𝒜.output h).stmt (𝒜.output h).proof (Qs (𝒜.output h).stmt) ∧
        (𝒜.append Xp kq).log h (tq + kq) ∉ M.extracts rel E (𝒜.output h).stmt]
      ≤ Pr[h ← (Query k kN kS L → Out k e) :
          (𝒜.append Xp kq).log h (tq + kq) ∈ M.bad rel E St ∪ digestCollision] := by
        refine QROM.probUniform_mono fun h ⟨hv, hn⟩ => ?_
        have ho := M.mem_game_of_verify Qs (Xs := Set.univ) (Set.mem_univ _) hv (hkq _ h _ hv)
        have hD : ((M.expansion Qs).expand h ⟨(𝒜.output h).stmt, (𝒜.output h).proof⟩ :
            BaseGame.Tuple _ _ _ kq).InDB ((𝒜.append Xp kq).log h (tq + kq)) := fun i =>
          𝒜.lookup_log_append_of_mem Xp kq h (List.getElem_mem _)
        obtain ⟨-, h1 | h2⟩ := M.mem_of_game rel E St hrbr Qs ho hD
        · exact absurd h1 hn
        · exact h2
    _ ≤ _ :=
        (M.prob_log_bad_union_le rel E St hrbr _).trans
          (knowledgeErrorROM_mono_error (maxError_le_iff.2 hκ))

end

end GordieHowe.SPBCS
