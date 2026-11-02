-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Cover
public import GordieHowe.SPBCS.Extraction.KnowledgeError
public import GordieHowe.Model.QROM.QueryBits
public import GordieHowe.Model.QROM.QueryCount

@[expose] public section

/-!
# Knowledge soundness of the spBCS compiler in the QROM

CMS19 section 8.5.2 (pp. 43–44, knowledge) for the spBCS compiler
(`GordieHowe/SPBCS/Basic.lean`, paper `thm:bcs-ks`(1)), from the instability bound read through the final digests
(`condInstab_bad_le`) and Proposition 8.12 for the spBCS verifier (`mem_of_verify`).

* `game`: CMS19's base game for the spBCS verifier; `expansion` its query expansion, with
  `mem_game_of_verify` (Proposition 8.11).
* `mem_of_game`: Proposition 8.12 for the base game, with the database extractor `dbExtract`
  (paper `prot:bcs-db-extractor`, `GordieHowe/SPBCS/Extractor.lean`).
* `dbProb_bad_union_le_of_queryCount`: the measured database of an algorithm with per-branch
  query count `b` lies in `bad ∪ P_col` with probability at most
  `6b² (max_c ε c + (max 2 c_in + nJ + 1) b / 2^(8k))`; the error is
  `knowledgeError k e kq t c_in nJ κ`, the knowledge error with `nJ` extra digests per input.
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm
open scoped ENNReal NNReal

variable {ι : Type} {t : SPTerm ι} {Mg : Merges t} {k kN kS L e : ℕ} {n : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (n j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] {X : Type}

section

variable (M : SPBCS Mg P X k kN kS L e)

/-! ### The base game -/

section Game

variable [∀ j i, Nonempty ((P j).Challenge i)] {V : X → FullTr P t → Bool}

/-- **The spBCS verifier's query expansion** (`BCSExpand`, CMS19 p. 39) for claims:
`queryProg` at the query phase of the claim's statement, padded with `.xof 0 0`. -/
noncomputable def expansion (Qs : ∀ x, M.IOPQueries V x) :
    Expansion (Query k kN kS L) (Out k e) (Claim X M.NIProof) :=
  GordieHowe.OracleProg.toExpansion (fun c => M.queryProg c.stmt c.proof (Qs c.stmt))
    (.xof (fun _ => 0) fun _ => 0)

theorem queries_expansion (Qs : ∀ x, M.IOPQueries V x) (h : Query k kN kS L → Out k e)
    (c : Claim X M.NIProof) {kq : ℕ} (i : Fin kq) :
    (M.expansion Qs).queries h c i =
      ((M.queries c.stmt c.proof h (Qs c.stmt))[i.1]?).getD (.xof (fun _ => 0) fun _ => 0) := by
  rw [expansion, GordieHowe.OracleProg.queries_toExpansion]
  rfl

/-- **The base game of the spBCS verifier** with `kq` queries at the statements `Xs` (CMS19
Definition 8.1, p. 39, with the statement output with the proof). -/
def game (Qs : ∀ x, M.IOPQueries V x) (Xs : Set X) (kq : ℕ) :
    BaseGame (Query k kN kS L) (Out k e) (Claim X M.NIProof) kq :=
  {o | o.out.stmt ∈ Xs ∧ ∃ h, M.Accepts h o.out.stmt o.out.proof (Qs o.out.stmt) ∧
    (∀ q ∈ M.queries o.out.stmt o.out.proof h (Qs o.out.stmt), ∃ i, o.queries i = q) ∧
      o.AnsweredBy h}

/-- **CMS19 Proposition 8.11** (p. 42), classical half, for the spBCS verifier. -/
theorem mem_game_of_verify (Qs : ∀ x, M.IOPQueries V x) {Xs : Set X} {kq : ℕ}
    {h : Query k kN kS L → Out k e} {x : X} {π : M.NIProof} (hx : x ∈ Xs)
    (hv : M.Accepts h x π (Qs x)) (hk : (M.queries x π h (Qs x)).length ≤ kq) :
    (M.expansion Qs).expand h ⟨x, π⟩ ∈ M.game Qs Xs kq := by
  refine ⟨hx, h, hv, fun q hq => ?_, fun _ => rfl⟩
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hq
  simp only [Expansion.expand] at hj ⊢
  exact ⟨⟨j, hj.trans_le hk⟩, by
    rw [queries_expansion, List.getElem?_eq_getElem hj, Option.getD_some]⟩

end Game

/-! ### Proposition 8.12 for the base game -/

section Prop812

variable [∀ j i, Nonempty ((P j).Challenge i)] {V : X → FullTr P t → Bool} {Wit : Type}
  (rel : Set (X × Wit)) (E : CausalExtractor P t X Wit) (St : CausalStateFn P t X)
  {ε : ChIdx P t → ℝ≥0}

/-- **CMS19 Proposition 8.12** for the base game of the spBCS verifier: a database recording
a winning tuple extracts a witness, or lies in `bad` or has a digest collision. -/
theorem mem_of_game [DecidableEq X] (hrbr : CausalRBRKnowledgeSound rel V E St ε)
    (Qs : ∀ x, M.IOPQueries V x) {Xs : Set X} {kq : ℕ}
    {o : BaseGame.Tuple (Query k kN kS L) (Out k e) (Claim X M.NIProof) kq}
    (ho : o ∈ M.game Qs Xs kq) {D : ODB k kN kS L e} (hD : o.InDB D) :
    o.out.stmt ∈ Xs ∧
      (D ∈ M.extracts rel E o.out.stmt ∨ D ∈ M.bad rel E St ∪ digestCollision) := by
  obtain ⟨hx, h, hv, hcov, hb⟩ := ho
  refine ⟨hx, ?_⟩
  have hrec : RecordsQueries D h o.out.stmt o.out.proof (Qs o.out.stmt) := fun q hq => by
    obtain ⟨i, rfl⟩ := hcov q hq
    rw [Recorded, hD i, hb i]
  rcases mem_of_verify rel E St hrbr hv hrec with hc | he | hb'
  · exact Or.inr (Or.inr hc)
  · exact Or.inl he
  · exact Or.inr (Or.inl hb')

end Prop812

section QueryCount

variable {M} [∀ j i, Nonempty ((P j).Challenge i)] {V : X → FullTr P t → Bool}

/-- The measured-database bound for the spBCS compiler at a per-branch query count `b`:
`6b² (max_c ε c + (max 2 c_in + maxNb + 1) b / 2^(8k))`. -/
theorem dbProb_bad_union_le_of_queryCount {Wit : Type} {rel : Set (X × Wit)}
    {E : CausalExtractor P t X Wit} {St : CausalStateFn P t X} {ε : ChIdx P t → ℝ≥0}
    (hrbr : CausalRBRKnowledgeSound rel V E St ε) {C : Type} {K tq b : ℕ}
    (𝒜 : Adv (Bits (queryBits k kN kS L)) (XOut k e) (Out k e) C K tq)
    (h : QueryCount (outEquiv k e) 𝒜 b) :
    dbProb (outEquiv k e) 𝒜 (DB.restrict Query.toBits ⁻¹' (M.bad rel E St ∪ digestCollision)) ≤
      6 * (b : ℝ≥0∞) ^ 2 * (maxError ε +
        (((max 2 M.senc.digestsPerInput + Mg.nJ + 1) * b : ℕ) : ℝ≥0∞) / 2 ^ (8 * k)) := by
  rw [Set.preimage_union]
  refine (Lifting.dbProb_union_le_of_queryCount (outEquiv k e) 𝒜 h
    (empty_notMem_preimage_restrict (M.empty_notMem_bad rel E St))
    (empty_notMem_preimage_restrict empty_notMem_collisionOn)).trans ?_
  rw [mul_comm ((b : ℝ≥0∞) ^ 2) 6, ← Set.preimage_compl]
  refine mul_le_mul_right ?_ _
  calc condInstab (DB.restrict Query.toBits ⁻¹' M.bad rel E St)
          (DB.restrict Query.toBits ⁻¹' digestCollisionᶜ) b
        + instab (DB.restrict Query.toBits ⁻¹' digestCollision) b
      ≤ condInstab (M.bad rel E St) digestCollisionᶜ b + instab digestCollision b :=
        add_le_add condInstab_preimage_restrict_le instab_preimage_restrict_le
    _ ≤ (maxError ε + (((max 2 M.senc.digestsPerInput + Mg.nJ) * b : ℕ) : ℝ≥0∞) /
          2 ^ (8 * k)) + (b : ℝ≥0∞) / 2 ^ (8 * k) :=
        add_le_add (M.condInstab_bad_le rel E St hrbr) instab_digestCollision_le
    _ = _ := by
        rw [add_assoc, ENNReal.div_add_div_same, ← Nat.cast_add, add_mul _ 1, one_mul]

end QueryCount

end

end GordieHowe.SPBCS
