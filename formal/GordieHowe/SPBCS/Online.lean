-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.KnowledgeROM
public import GordieHowe.Headline
public import GordieHowe.SPBCS.Extractor
public import GordieHowe.SPBCS.Extraction.KnowledgeError
public import GordieHowe.Model.QROM.QueryBits
public import GordieHowe.Model.QROM.QueryCount
public import GordieHowe.SPBCS.Extraction.OnlineExtract
public import GordieHowe.SPBCS.Extraction.OnlineExtractROM
public import GordieHowe.Model.ROM.Model
public import GordieHowe.SPBCS.ZeroKnowledge

@[expose] public section

/-!
# Online extractability of the spBCS compiler

The spBCS verifier (`Accepts`, `queries`) as a `GordieHowe.NARG.QROM.Verifier` and as a
`GordieHowe.NARG.ROM.Verifier`, with the
database extractor `dbExtract` and its knowledge bounds, so that the generic online-extractability
and soundness theorems of `GordieHowe/SPBCS/Extraction/OnlineExtract.lean` apply against the query-bounded
adversaries of `def:adversary` without proof queries (paper `thm:bcs-ks` and `thm:bcs-main`(2)).

- `accepts_of_eqOn_queries`: the verifier reads the oracle only at its queries.
- `queries_length_le_of_accepts`, `kqOf`: an accepting run makes at most
  `2 · t.size n + |Site| + NQ · (1 + ⌊log₂ 2N⌋)` queries (two per round, one final input per
  branch, the openings of the trees) under the format bounds `NQ`, `N` (`GordieHowe.SPBCS.FormatBounds`); this is
  the paper's `k_q` (`def:bcs-quantities`), with `n_B = |Site|`.
- `toQVerifier`, `knowledgeBound`: the instance; its knowledge error is
  `knowledgeError k e kq b c nJ (maxError ε)` (`knowledgeError_toQVerifier`).
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm
open scoped ENNReal NNReal BigOperators

variable {ι : Type} {t : SPTerm ι} {Mg : Merges t} {k kN kS L e : ℕ} {n : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (n j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] {X : Type}

omit [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)] in
variable (t P) in
/-- **A composite has at most `t.size n` challenges**: one per challenge round of each leaf. -/
theorem card_chIdx_le_size : Fintype.card (ChIdx P t) ≤ t.size n := by
  rw [Fintype.card_congr ChIdx.equivSigma, Fintype.card_sigma, size_eq_sum]
  exact Finset.sum_le_sum fun p _ =>
    (Fintype.card_subtype_le _).trans_eq (Fintype.card_fin _)

section

variable [∀ j i, Nonempty ((P j).Challenge i)] (M : SPBCS Mg P X k kN kS L e)
  {V : X → FullTr P t → Bool}

/-! ### The verifier reads the oracle only at its queries -/

section Congr

variable {M} {h h' : Query k kN kS L → Out k e} {x : X} {π : M.NIProof} {Q : M.IOPQueries V x}

/-- **The spBCS verifier's challenges depend on the oracle only at its queries**: if `h'`
agrees with `h` on the queries of `V^h(x, π)`, the challenges `chV` are the same. -/
theorem chV_eq_of_eqOn_queries (hh : ∀ q ∈ M.queries x π h Q, h' q = h q) :
    M.chV h' (M.ssOf x π) π.writes = M.chV h (M.ssOf x π) π.writes := by
  have hrounds : ∀ q ∈ (M.roundsProg x π).trace h, h q = h' q := fun q hq =>
    (hh q (by rw [queries_eq]; exact List.mem_append_left _ hq)).symm
  have hrun := GordieHowe.OracleProg.run_congr _ hrounds
  have hans : M.xofAnswers h' (M.ssOf x π) π.writes = M.xofAnswers h (M.ssOf x π) π.writes :=
    by rw [← answers_roundsProg M x π h, ← answers_roundsProg M x π h', hrun]
  have hch : ∀ c, M.chal h' (M.ssOf x π) π.writes c = M.chal h (M.ssOf x π) π.writes c := fun c => by
    rw [chal_eq_xofAnswers, chal_eq_xofAnswers, hans]
  exact funext fun c => by simp only [chV, hch]

/-- **The spBCS verifier's decision depends on the oracle only at its queries**: if `h'`
agrees with `h` on the queries of `V^h(x, π)`, then `V^{h'}` accepts `π` when `V^h` does. -/
theorem accepts_of_eqOn_queries (hh : ∀ q ∈ M.queries x π h Q, h' q = h q)
    (hv : M.Accepts h x π Q) : M.Accepts h' x π Q := by
  have hrounds : ∀ q ∈ (M.roundsProg x π).trace h, h q = h' q := fun q hq =>
    (hh q (by rw [queries_eq]; exact List.mem_append_left _ hq)).symm
  have hrun := GordieHowe.OracleProg.run_congr _ hrounds
  have hc : M.chains h' (M.ssOf x π) π.writes = M.chains h (M.ssOf x π) π.writes :=
    by rw [← chains_roundsProg M x π h, ← chains_roundsProg M x π h', hrun]
  have hans : M.xofAnswers h' (M.ssOf x π) π.writes = M.xofAnswers h (M.ssOf x π) π.writes :=
    by rw [← answers_roundsProg M x π h, ← answers_roundsProg M x π h', hrun]
  have hch : ∀ c, M.chal h' (M.ssOf x π) π.writes c = M.chal h (M.ssOf x π) π.writes c := fun c => by
    rw [chal_eq_xofAnswers, chal_eq_xofAnswers, hans]
  have hV : M.chV h' (M.ssOf x π) π.writes = M.chV h (M.ssOf x π) π.writes :=
    funext fun c => by simp only [chV, hch]
  refine ⟨fun c => (hch c).symm ▸ hv.sampled c, ?_, ?_, ?_⟩
  · rw [hc, hV]
    exact hv.leaves_length
  · rw [hc, hV]
    intro τ hτ
    obtain ⟨h1, h2, h3, h4, hrun'⟩ := hv.paths τ hτ
    refine ⟨h1, h2, h3, h4, ?_⟩
    have hq : ∀ q ∈ (M.treeProg π (Q.pos (M.chains h (M.ssOf x π) π.writes)
        (M.chV h (M.ssOf x π) π.writes)) τ).trace h, h q = h' q := fun q hq =>
      (hh q (by
        rw [queries_eq]
        exact List.mem_append_right _ (List.mem_flatMap.2 ⟨τ, hτ, hq⟩))).symm
    exact (GordieHowe.OracleProg.run_congr _ hq).symm.trans hrun'
  · rw [hc, hV]
    exact hv.decides

end Congr

/-! ### The verifier's query count -/

section QueryCount

variable (h : Query k kN kS L → Out k e) (x : X) (π : M.NIProof)

/-- **The query count of an accepting run** of the spBCS verifier: the rounds program
(`length_trace_roundsProg`) and at most `1 + ⌊log₂ 2N⌋` per queried position. -/
theorem queries_length_le_of_accepts {Q : M.IOPQueries V x} {N : ℕ}
    (hN : ∀ (p : t.Leaf) i τ, (M.comp p.label).nLeaves i τ ≤ N) (hv : M.Accepts h x π Q) :
    (M.queries x π h Q).length ≤ 2 * t.size n + Fintype.card Mg.Site +
      (Q.pos (M.chains h (M.ssOf x π) π.writes) (M.chV h (M.ssOf x π) π.writes)).length *
        (1 + Nat.log 2 (2 * N)) := by
  set ps := Q.pos (M.chains h (M.ssOf x π) π.writes) (M.chV h (M.ssOf x π) π.writes)
  rw [queries_eq, List.length_append, List.length_flatMap]
  refine Nat.add_le_add (by rw [M.length_trace_roundsProg x π h, ← size_eq_sum]) ?_
  calc ((M.trees ps).map fun τ => ((M.treeProg π ps τ).trace h).length).sum
      ≤ ((M.trees ps).map fun τ =>
          (M.openedIn τ ps π.leaves).length * (1 + Nat.log 2 (2 * N))).sum := by
        refine List.sum_le_sum fun τ hτ => ?_
        obtain ⟨-, hjs, hlv, -, -⟩ := hv.paths τ hτ
        refine (M.opening.length_trace_le h _ hjs hlv).trans ?_
        rw [List.length_map]
        exact Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.log_mono_right (by
          have := hN τ.leaf τ.tree.msg τ.tree.tree; omega)) _)
    _ = ps.length * (1 + Nat.log 2 (2 * N)) := by
        rw [List.sum_map_mul_right, SPBCS.sum_length_openedIn _ hv.leaves_length]

end QueryCount

variable (Mg) in
/-- **The query budget of the spBCS verifier** for query phases opening at most `NQ` positions
and trees of at most `N` leaves: `2 · t.size n + |Site| + NQ · (1 + ⌊log₂ 2N⌋)`. -/
def kqOf (n : ι → ℕ) (NQ N : ℕ) : ℕ :=
  2 * t.size n + Fintype.card Mg.Site + NQ * (1 + Nat.log 2 (2 * N))

variable {M} in
/-- **An accepting run of the spBCS verifier makes at most `kqOf Mg n NQ N` queries.** -/
theorem queries_length_le_of_formatBounds {Qs : ∀ x, M.IOPQueries V x} {NQ N : ℕ}
    (hb : M.FormatBounds Qs NQ N) {x : X} {h : Query k kN kS L → Out k e} {π : M.NIProof}
    (hv : M.Accepts h x π (Qs x)) : (M.queries x π h (Qs x)).length ≤ kqOf Mg n NQ N :=
  (M.queries_length_le_of_accepts h x π hb.nLeaves_le hv).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_right _ (hb.pos_le _ _ _)) _)

variable {M} in
/-- **The format bounds bound the verifier's queries by `kqOf Mg n NQ N`**
(`queries_length_le_of_formatBounds`). -/
theorem FormatBounds.queriesAtMost {Qs : ∀ x, M.IOPQueries V x} {NQ N : ℕ}
    (hb : M.FormatBounds Qs NQ N) : M.QueriesAtMost Qs (kqOf Mg n NQ N) :=
  fun _ _ _ hv => queries_length_le_of_formatBounds hb hv

omit [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] in
variable (Mg P) in
/-- **The verifier's query budget exceeds the number of challenges** when the composite has a
round. -/
theorem card_chIdx_add_one_le_kqOf (NQ N : ℕ) (h : 1 ≤ t.size n) :
    Fintype.card (ChIdx P t) + 1 ≤ kqOf Mg n NQ N := by
  have := card_chIdx_le_size t P
  unfold kqOf
  omega

omit [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] in
variable (Mg) in
/-- **The round errors and one largest error together are at most `kqOf` largest errors** when
the composite has a round. -/
theorem sum_add_maxError_le_kqOf (NQ N : ℕ) (h : 1 ≤ t.size n) (ε : ChIdx P t → ℝ≥0) :
    ∑ c, ε c + maxError ε ≤ kqOf Mg n NQ N * maxError ε := by
  calc ∑ c, ε c + maxError ε ≤ Fintype.card (ChIdx P t) * maxError ε + maxError ε :=
        add_le_add (sum_le_card_mul_max ε) le_rfl
    _ = ((Fintype.card (ChIdx P t) + 1 : ℕ) : ℝ≥0) * maxError ε := by push_cast; ring
    _ ≤ kqOf Mg n NQ N * maxError ε := by
        gcongr
        exact_mod_cast card_chIdx_add_one_le_kqOf Mg P NQ N h

/-! ### The instance -/

/-- **The spBCS verifier as a `NARG.QROM.Verifier`**: its query expansion with `kq` queries encoded
into `{0,1}^m` by `Query.toBits`; on the answers to these queries it accepts when an oracle with
these answers at its queries is accepted, read through `Query.toBits`
(`NARG.Verifier.ofOracle`). -/
def toQVerifier (Qs : ∀ x, M.IOPQueries V x) (kq : ℕ) :
    NARG.QROM.Verifier (queryBits k kN kS L) k e (Claim X M.NIProof) X :=
  NARG.Verifier.ofOracle kq ((M.expansion Qs).map Query.toBits)
    (fun h c => M.Accepts (h ∘ Query.toBits) c.stmt c.proof (Qs c.stmt)) Claim.stmt

/-- **The database extractor of the spBCS argument on databases over `{0,1}^m`**:
`dbExtract` on the restriction to the encoded queries.

The restriction is computed by decoding each entry's input (`DB.restrictBy` at `Query.ofBits`,
equal to `DB.restrict Query.toBits` by `dbExtractBits_eq`).

Running time: the restriction decodes and re-encodes each entry's input once, `O(|D| · m)`, then
`dbExtract` (polynomial by its own Running time paragraph). This running time is argued here, not
proved in Lean. -/
def dbExtractBits [DecidableEq X] {Wit : Type} (E : CausalExtractor P t X Wit)
    (x : X) (D : DB (Bits (queryBits k kN kS L)) (Out k e)) : Multiset Wit :=
  M.dbExtract E x (D.restrictBy Query.toBits Query.ofBits fun _ _ => Query.ofBits_eq_some_iff)

/-- **`dbExtractBits` is `dbExtract` on the restriction to the encoded queries.** -/
theorem dbExtractBits_eq [DecidableEq X] {Wit : Type} (E : CausalExtractor P t X Wit)
    (x : X) (D : DB (Bits (queryBits k kN kS L)) (Out k e)) :
    M.dbExtractBits E x D = M.dbExtract E x (D.restrict Query.toBits) := by
  rw [dbExtractBits, DB.restrictBy_eq]

/-- **The lexicographic order of bit strings**: `a ≤ b` when the list of the bits of `a` is at most
that of `b` in the lexicographic order of lists (`List.ofFn`). A relation, not an instance: the
pointwise order of `Fin m → Bool` is Mathlib's. -/
def bitsLexLE {m : ℕ} (a b : Bits m) : Prop :=
  List.ofFn a ≤ List.ofFn b

/-- The lexicographic order of bit strings is decided by comparing the lists of bits. -/
instance {m : ℕ} : DecidableRel (bitsLexLE (m := m)) := fun a b =>
  inferInstanceAs (Decidable (List.ofFn a ≤ List.ofFn b))

/-- The lexicographic order of bit strings is transitive. -/
instance {m : ℕ} : IsTrans (Bits m) bitsLexLE :=
  ⟨fun _ _ _ => le_trans (a := List.ofFn _)⟩

/-- The lexicographic order of bit strings is antisymmetric (`List.ofFn` is injective). -/
instance {m : ℕ} : Std.Antisymm (bitsLexLE (m := m)) :=
  ⟨fun _ _ h h' => List.ofFn_injective (le_antisymm h h')⟩

/-- The lexicographic order of bit strings is total. -/
instance {m : ℕ} : Std.Total (bitsLexLE (m := m)) :=
  ⟨fun a b => le_total (List.ofFn a) (List.ofFn b)⟩

/-- **The database extractor of the spBCS argument as a list**: `dbExtractBits` with the entries of
`D` read in the lexicographic order of their inputs (`bitsLexLE`), so that the witnesses come in an
order (`coe_dbExtractBitsList`).

Running time: sorting the inputs of `D`, `O(|D| log |D| · m)`, then the work of `dbExtractBits`
(its paragraph). This running time is argued here, not proved in Lean. -/
def dbExtractBitsList [DecidableEq X] {Wit : Type} (E : CausalExtractor P t X Wit)
    (x : X) (D : DB (Bits (queryBits k kN kS L)) (Out k e)) : List Wit :=
  (D.keys.sort bitsLexLE).filterMap fun w => (Query.ofBits w).bind
    (M.candidate E x (D.restrictBy Query.toBits Query.ofBits fun _ _ => Query.ofBits_eq_some_iff))

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- **The list extractor has the witnesses of `dbExtractBits`.** -/
theorem coe_dbExtractBitsList [DecidableEq X] {Wit : Type} (E : CausalExtractor P t X Wit)
    (x : X) (D : DB (Bits (queryBits k kN kS L)) (Out k e)) :
    (M.dbExtractBitsList E x D : Multiset Wit) = M.dbExtractBits E x D := by
  have hk : (D.restrictBy Query.toBits Query.ofBits fun _ _ => Query.ofBits_eq_some_iff).keys.val =
      D.keys.val.filterMap Query.ofBits := by
    rw [DB.restrictBy, Finmap.keysLookupEquiv_symm_apply_keys, Finset.filterMap_val]
  rw [dbExtractBitsList, ← Multiset.filterMap_coe, Finset.sort_eq, dbExtractBits, dbExtract, hk,
    Multiset.filterMap_filterMap]

/-- **The list extractor read as multisets is `dbExtractBits`.** -/
theorem coe_comp_dbExtractBitsList [DecidableEq X] {Wit : Type} (E : CausalExtractor P t X Wit) :
    (fun x D => (M.dbExtractBitsList E x D : Multiset Wit)) = M.dbExtractBits E :=
  funext fun x => funext fun D => M.coe_dbExtractBitsList E x D

/-- **The database bound of the spBCS argument** at `b` queries:
`6b² (maxError ε + (max 2 c + nJ + 1) b / 2^(8k))`. -/
noncomputable def dbBound (ε : ChIdx P t → ℝ≥0) (b : ℕ) : ℝ≥0∞ :=
  6 * (b : ℝ≥0∞) ^ 2 * (maxError ε +
    (((max 2 M.senc.digestsPerInput + Mg.nJ + 1) * b : ℕ) : ℝ≥0∞) / 2 ^ (8 * k))

omit [∀ j i, Nonempty ((P j).Challenge i)] in
theorem dbBound_mono (ε : ChIdx P t → ℝ≥0) : Monotone (M.dbBound ε) := fun _ _ h => by
  unfold dbBound
  gcongr

variable {Wit : Type} (rel : Set (X × Wit)) (E : CausalExtractor P t X Wit)
  (St : CausalStateFn P t X) {ε : ChIdx P t → ℝ≥0}

/-- **`dbExtractBits` extracts at `D` exactly when the restriction of `D` to the encoded queries is
in `extracts`.** -/
theorem extractsAt_dbExtractBits_iff [DecidableEq X] {x : X}
    {D : DB (Bits (queryBits k kN kS L)) (Out k e)} :
    NARG.ExtractsAt rel (M.dbExtractBits E) x D ↔ D.restrict Query.toBits ∈ M.extracts rel E x := by
  rw [NARG.ExtractsAt, dbExtractBits_eq]
  rfl

/-- **The knowledge bound of the spBCS argument** (CMS19 Proposition 8.12 for its base
game, `mem_of_game`, and the database bound `dbProb_bad_union_le_of_queryCount`), from causal
round-by-round knowledge soundness of the composite. -/
noncomputable def knowledgeBound [DecidableEq X] (hrbr : CausalRBRKnowledgeSound rel V E St ε)
    (Qs : ∀ x, M.IOPQueries V x) (kq : ℕ)
    (hkq : M.QueriesAtMost Qs kq) :
    (M.toQVerifier Qs kq).KnowledgeBound rel (M.dbExtractBits E) (M.dbBound ε) where
  bad := DB.restrict Query.toBits ⁻¹' (M.bad rel E St ∪ digestCollision)
  mem_of_game o ho D hD := by
    obtain ⟨h, he, hv⟩ := NARG.Verifier.mem_game_ofOracle.1 ho
    have hm : o ∈ (M.game Qs Set.univ kq).map Query.toBits := by
      rw [← he, Expansion.expand_map]
      exact BaseGame.mem_map (M.mem_game_of_verify Qs (Set.mem_univ _) hv (hkq _ _ _ hv))
    obtain ⟨o', ho', rfl⟩ := hm
    have hD' : o'.InDB (D.restrict Query.toBits) :=
      fun i => (DB.lookup_restrict _).trans (hD i)
    obtain ⟨-, h | h⟩ := M.mem_of_game rel E St hrbr Qs ho' hD'
    · exact Or.inl ((M.extractsAt_dbExtractBits_iff rel E).2 h)
    · exact Or.inr h
  dbProb_le 𝒜 hb := dbProb_bad_union_le_of_queryCount hrbr 𝒜 hb
  mono := M.dbBound_mono ε

/-- **The knowledge error of the instance is the spBCS knowledge error**
`knowledgeError k e kq b c nJ (maxError ε)`. -/
theorem knowledgeError_toQVerifier (Qs : ∀ x, M.IOPQueries V x) (kq : ℕ) (b : ℕ) :
    (M.toQVerifier Qs kq).knowledgeError (M.dbBound ε) b =
      knowledgeError k e kq b M.senc.digestsPerInput Mg.nJ (maxError ε) :=
  rfl

/-- **The knowledge bound of the spBCS argument at an instability bound**: `knowledgeBound`'s bad
databases and Proposition 8.12, with the database bound
`6b² (maxError ε + (max 2 c + cP + 1) b / 2^(8k))` for every bound
`maxError ε + (max 2 c + cP) b / 2^(8k)` on the conditional instability (`hI`,
`dbProb_bad_union_le_of_queryCount_of`). -/
noncomputable def knowledgeBoundOf [DecidableEq X] (hrbr : CausalRBRKnowledgeSound rel V E St ε)
    (Qs : ∀ x, M.IOPQueries V x) (kq : ℕ) (hkq : M.QueriesAtMost Qs kq) (c cP : ℕ)
    (hI : ∀ b, condInstab (M.bad rel E St) digestCollisionᶜ b ≤
      maxError ε + (((max 2 c + cP) * b : ℕ) : ℝ≥0∞) / 2 ^ (8 * k)) :
    (M.toQVerifier Qs kq).KnowledgeBound rel (M.dbExtractBits E) fun b =>
      6 * (b : ℝ≥0∞) ^ 2 * (maxError ε + (((max 2 c + cP + 1) * b : ℕ) : ℝ≥0∞) / 2 ^ (8 * k)) :=
  { M.knowledgeBound rel E St hrbr Qs kq hkq with
    dbProb_le := fun 𝒜 hb => dbProb_bad_union_le_of_queryCount_of c cP hI 𝒜 hb
    mono := fun _ _ h => by dsimp only; gcongr }

/-- **The knowledge bound of the spBCS argument at the slot constant** (`knowledgeBoundOf` at
`condInstab_bad_le_slot`): the database bound `6b² (maxError ε + (max 2 T + 1) b / 2^(8k))`,
`T` the Merkle trees. -/
noncomputable def knowledgeBoundSlot [DecidableEq X] (hrbr : CausalRBRKnowledgeSound rel V E St ε)
    (Qs : ∀ x, M.IOPQueries V x) (kq : ℕ) (hkq : M.QueriesAtMost Qs kq) :
    (M.toQVerifier Qs kq).KnowledgeBound rel (M.dbExtractBits E) fun b =>
      6 * (b : ℝ≥0∞) ^ 2 * (maxError ε +
        (((max 2 (Fintype.card M.TreeSig) + 0 + 1) * b : ℕ) : ℝ≥0∞) / 2 ^ (8 * k)) :=
  M.knowledgeBoundOf rel E St hrbr Qs kq hkq _ 0 fun b => by
    simpa only [Nat.add_zero] using M.condInstab_bad_le_slot rel E St hrbr (tq := b)

/-! ### The classical random-oracle model -/

/-- **The spBCS verifier as a `NARG.ROM.Verifier`**: its query expansion with `kq` queries; on the
answers to these queries it accepts when an oracle with these answers at its queries is accepted
(`NARG.Verifier.ofOracle`). -/
def toRVerifier (Qs : ∀ x, M.IOPQueries V x) (kq : ℕ) :
    NARG.ROM.Verifier (Query k kN kS L) (Out k e) (Claim X M.NIProof) X :=
  NARG.Verifier.ofOracle kq (M.expansion Qs) (fun h c => M.Accepts h c.stmt c.proof (Qs c.stmt))
    Claim.stmt

/-- **The spBCS verifier reads the oracle only at its first `kq` expansion queries**: an oracle
that agrees with an accepting oracle `h'` at them is accepted, for a query budget `kq` of every
accepting run (`hkq`). -/
theorem accepts_of_agree (Qs : ∀ x, M.IOPQueries V x) {kq : ℕ}
    (hkq : M.QueriesAtMost Qs kq)
    {h h' : Query k kN kS L → Out k e} {c : Claim X M.NIProof}
    (hag : ∀ i : Fin kq, h' ((M.expansion Qs).queries h' c i) = h ((M.expansion Qs).queries h' c i))
    (hv : M.Accepts h' c.stmt c.proof (Qs c.stmt)) : M.Accepts h c.stmt c.proof (Qs c.stmt) := by
  refine accepts_of_eqOn_queries (h := h') (fun q hq => ?_) hv
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hq
  have := hag ⟨j, hj.trans_le (hkq _ _ _ hv)⟩
  rw [queries_expansion, List.getElem?_eq_getElem hj, Option.getD_some] at this
  exact this.symm

/-- **The decision of the classical instance is the spBCS verifier's acceptance**, for a query
budget `kq` of every accepting run (`hkq`). -/
theorem accepted_toRVerifier_iff (Qs : ∀ x, M.IOPQueries V x) {kq : ℕ}
    (hkq : M.QueriesAtMost Qs kq)
    {h : Query k kN kS L → Out k e} {c : Claim X M.NIProof} :
    (M.toRVerifier Qs kq).Accepted h c ↔ M.Accepts h c.stmt c.proof (Qs c.stmt) :=
  NARG.Verifier.ofOracle_accepted_iff fun _ _ _ hag hv => M.accepts_of_agree Qs hkq hag hv

/-- **The joint knowledge bound of the spBCS argument in the ROM**
(`knowledge_of_causalRBR_rom_joint`) at the database extractor `dbExtract`, with error
`knowledgeErrorROM k b c nJ (maxError ε)` at `b` queries. -/
@[headline]
theorem jointBound [DecidableEq X] (hrbr : CausalRBRKnowledgeSound rel V E St ε)
    (Qs : ∀ x, M.IOPQueries V x) {kq : ℕ}
    (hkq : M.QueriesAtMost Qs kq) :
    (M.toRVerifier Qs kq).JointBound rel (M.dbExtract E)
      fun b => knowledgeErrorROM k b M.senc.digestsPerInput Mg.nJ (maxError ε) := fun 𝒜 =>
  (QROM.probUniform_mono fun _ hh => ⟨(M.accepted_toRVerifier_iff Qs hkq).1 hh.1, hh.2⟩).trans
    (M.knowledge_of_causalRBR_rom_joint rel E St Qs hrbr (le_maxError ε) hkq 𝒜)

/-- **The joint knowledge bound of the spBCS argument in the ROM with the round errors and the
collisions charged by entry class** (`knowledge_of_causalRBR_rom_joint_typed`) at the database
extractor `dbExtract`, with error `knowledgeErrorROMTyped k (b - kq) kq T (maxError ε) (∑ c, ε c)`
at `b` queries in all, `T` the number of Merkle trees. -/
theorem jointBound_typed [DecidableEq X] (hrbr : CausalRBRKnowledgeSound rel V E St ε)
    (Qs : ∀ x, M.IOPQueries V x) {kq : ℕ}
    (hkq : M.QueriesAtMost Qs kq) :
    (M.toRVerifier Qs kq).JointBound rel (M.dbExtract E)
      fun b => knowledgeErrorROMTyped k (b - kq) kq (Fintype.card M.TreeSig) (maxError ε)
        (∑ c, ε c) := fun 𝒜 =>
  (QROM.probUniform_mono fun _ hh => ⟨(M.accepted_toRVerifier_iff Qs hkq).1 hh.1, hh.2⟩).trans
    ((M.knowledge_of_causalRBR_rom_joint_typed rel E St Qs hrbr (le_maxError ε) hkq 𝒜).trans_eq
      (by simp only [show (M.toRVerifier Qs kq).kq = kq from rfl, Nat.add_sub_cancel]))

/-! ### The instances at the verifier's query budget -/

/-- **The spBCS verifier at its query budget** under format bounds `NQ`, `N` (`toQVerifier` at
`kqOf Mg n NQ N`). -/
def qVerifier (Qs : ∀ x, M.IOPQueries V x) (NQ N : ℕ) :
    NARG.QROM.Verifier (queryBits k kN kS L) k e (Claim X M.NIProof) X :=
  M.toQVerifier Qs (kqOf Mg n NQ N)

/-- **The spBCS verifier at its query budget, classically** (`toRVerifier` at
`kqOf Mg n NQ N`). -/
def rVerifier (Qs : ∀ x, M.IOPQueries V x) (NQ N : ℕ) :
    NARG.ROM.Verifier (Query k kN kS L) (Out k e) (Claim X M.NIProof) X :=
  M.toRVerifier Qs (kqOf Mg n NQ N)

/-- **The compiled verifier at its query budget accepts exactly the claims the spBCS verifier
accepts** under the oracle read through `Query.toBits`, for format bounds `NQ`, `N` (`hb`). -/
theorem accepted_qVerifier_iff {Qs : ∀ x, M.IOPQueries V x} {NQ N : ℕ}
    (hb : M.FormatBounds Qs NQ N) {h : Bits (queryBits k kN kS L) → Out k e}
    {c : Claim X M.NIProof} :
    (M.qVerifier Qs NQ N).Accepted h c ↔ M.Accepts (h ∘ Query.toBits) c.stmt c.proof (Qs c.stmt) :=
  NARG.Verifier.ofOracle_accepted_iff fun _ _ c' hag hv =>
    M.accepts_of_agree Qs (c := c') (fun _ _ _ hv => queries_length_le_of_formatBounds hb hv)
      (fun i => by
        have := hag i
        rw [QROM.Expansion.queries_map] at this
        exact this) hv

/-- **The compiled verifier's acceptance is decidable** under format bounds `hb`: by
`accepted_qVerifier_iff`, from the decision of the spBCS verifier (`Accepts`). -/
def decAcceptedQ {Qs : ∀ x, M.IOPQueries V x} {NQ N : ℕ} (hb : M.FormatBounds Qs NQ N)
    (h : Bits (queryBits k kN kS L) → Out k e) : DecidablePred ((M.qVerifier Qs NQ N).Accepted h) :=
  fun _ => decidable_of_iff _ (M.accepted_qVerifier_iff hb).symm

variable {M rel E St}

/-- **Online extractability of the spBCS verifier** with a query budget `kq` of its accepting
runs (`hkq`) against query-bounded adversaries without proof queries, at
`knowledgeError k e kq (t + kq) c nJ (maxError ε)`. -/
theorem onlineExtracts_toQVerifier [DecidableEq X] (hrbr : CausalRBRKnowledgeSound rel V E St ε)
    {Qs : ∀ x, M.IOPQueries V x} {kq : ℕ}
    (hkq : M.QueriesAtMost Qs kq) {Z : Type}
    {t : ℕ} (𝒢 : NARG.QROM.Adversary (queryBits k kN kS L) k e (Claim X M.NIProof × Z) t) :
    𝒢.OnlineExtracts (M.toQVerifier Qs kq) NARG.QROM.compressedSim rel
      (NARG.QROM.compressedExt (M.dbExtractBits E)) 0
      (knowledgeError k e kq (t + kq) M.senc.digestsPerInput Mg.nJ (maxError ε)) :=
  QROM.onlineExtracts _ (M.knowledgeBound rel E St hrbr Qs kq hkq) 𝒢

/-- **Soundness of the spBCS verifier** with a query budget `kq` (`hkq`) against query-bounded
adversaries without proof queries, at the error of `onlineExtracts_toQVerifier`. -/
theorem soundness_toQVerifier [DecidableEq X] (hrbr : CausalRBRKnowledgeSound rel V E St ε)
    {Qs : ∀ x, M.IOPQueries V x} {kq : ℕ}
    (hkq : M.QueriesAtMost Qs kq) {t : ℕ}
    (𝒜 : NARG.QROM.Adversary (queryBits k kN kS L) k e (Claim X M.NIProof) t) :
    𝒜.acceptsFalse (M.toQVerifier Qs kq) rel ≤
      knowledgeError k e kq (t + kq) M.senc.digestsPerInput Mg.nJ (maxError ε) :=
  QROM.soundness _ (M.knowledgeBound rel E St hrbr Qs kq hkq) 𝒜

/-- **Online extractability of the spBCS verifier at the slot constant**
(`onlineExtracts_toQVerifier` with `knowledgeBoundSlot`): at
`knowledgeError k e kq (t + kq) T 0 (maxError ε)`, `T` the Merkle trees. -/
theorem onlineExtracts_toQVerifier_slot [DecidableEq X]
    (hrbr : CausalRBRKnowledgeSound rel V E St ε) {Qs : ∀ x, M.IOPQueries V x} {kq : ℕ}
    (hkq : M.QueriesAtMost Qs kq) {Z : Type}
    {t : ℕ} (𝒢 : NARG.QROM.Adversary (queryBits k kN kS L) k e (Claim X M.NIProof × Z) t) :
    𝒢.OnlineExtracts (M.toQVerifier Qs kq) NARG.QROM.compressedSim rel
      (NARG.QROM.compressedExt (M.dbExtractBits E)) 0
      (knowledgeError k e kq (t + kq) (Fintype.card M.TreeSig) 0 (maxError ε)) :=
  QROM.onlineExtracts _ (M.knowledgeBoundSlot rel E St hrbr Qs kq hkq) 𝒢

/-- **Soundness of the spBCS verifier at the slot constant**, at the error of
`onlineExtracts_toQVerifier_slot`. -/
theorem soundness_toQVerifier_slot [DecidableEq X] (hrbr : CausalRBRKnowledgeSound rel V E St ε)
    {Qs : ∀ x, M.IOPQueries V x} {kq : ℕ}
    (hkq : M.QueriesAtMost Qs kq) {t : ℕ}
    (𝒜 : NARG.QROM.Adversary (queryBits k kN kS L) k e (Claim X M.NIProof) t) :
    𝒜.acceptsFalse (M.toQVerifier Qs kq) rel ≤
      knowledgeError k e kq (t + kq) (Fintype.card M.TreeSig) 0 (maxError ε) :=
  QROM.soundness _ (M.knowledgeBoundSlot rel E St hrbr Qs kq hkq) 𝒜

/-- **Online extractability of the spBCS verifier in the ROM** with a query budget `kq`
(`hkq`) against classical query-bounded adversaries without proof queries, at
`knowledgeErrorROM k (t + kq) c nJ (maxError ε)`. -/
theorem onlineExtracts_toRVerifier [DecidableEq X] (hrbr : CausalRBRKnowledgeSound rel V E St ε)
    {Qs : ∀ x, M.IOPQueries V x} {kq : ℕ}
    (hkq : M.QueriesAtMost Qs kq) {Z : Type}
    {t : ℕ} (𝒢 : NARG.ROM.Adversary (Query k kN kS L) (Out k e) (Claim X M.NIProof × Z) t) :
    𝒢.OnlineExtracts (M.toRVerifier Qs kq) NARG.ROM.OracleSampler.lazy.law rel (M.dbExtract E) 0
      (knowledgeErrorROM k (t + kq) M.senc.digestsPerInput Mg.nJ (maxError ε)) :=
  ROM.onlineExtracts (V := M.toRVerifier Qs kq) (rel := rel) (ext := M.dbExtract E)
    (β := fun b => knowledgeErrorROM k b M.senc.digestsPerInput Mg.nJ (maxError ε))
    (M.jointBound rel E St hrbr Qs hkq) 𝒢

/-- **Soundness of the spBCS verifier in the ROM** with a query budget `kq` (`hkq`). -/
theorem soundness_toRVerifier [DecidableEq X] (hrbr : CausalRBRKnowledgeSound rel V E St ε)
    {Qs : ∀ x, M.IOPQueries V x} {kq : ℕ}
    (hkq : M.QueriesAtMost Qs kq) {t : ℕ}
    (𝒜 : NARG.ROM.Adversary (Query k kN kS L) (Out k e) (Claim X M.NIProof) t) :
    𝒜.acceptsFalse (M.toRVerifier Qs kq) rel ≤
      knowledgeErrorROM k (t + kq) M.senc.digestsPerInput Mg.nJ (maxError ε) :=
  ROM.soundness (V := M.toRVerifier Qs kq) (ext := M.dbExtract E)
    (β := fun b => knowledgeErrorROM k b M.senc.digestsPerInput Mg.nJ (maxError ε))
    (M.jointBound rel E St hrbr Qs hkq) 𝒜

/-- **Online extractability at the query budget of the format bounds**
(`onlineExtracts_toQVerifier` at `kqOf Mg n NQ N`). -/
@[headline]
theorem onlineExtracts_qrom [DecidableEq X] (hrbr : CausalRBRKnowledgeSound rel V E St ε)
    {Qs : ∀ x, M.IOPQueries V x} {NQ N : ℕ} (hb : M.FormatBounds Qs NQ N) {Z : Type} {t : ℕ}
    (𝒢 : NARG.QROM.Adversary (queryBits k kN kS L) k e (Claim X M.NIProof × Z) t) :
    𝒢.OnlineExtracts (M.qVerifier Qs NQ N) NARG.QROM.compressedSim rel
      (NARG.QROM.compressedExt (M.dbExtractBits E)) 0
      (knowledgeError k e (kqOf Mg n NQ N) (t + kqOf Mg n NQ N) M.senc.digestsPerInput Mg.nJ
        (maxError ε)) :=
  onlineExtracts_toQVerifier hrbr (fun _ _ _ hv => queries_length_le_of_formatBounds hb hv) 𝒢

/-- **Soundness at the query budget of the format bounds.** -/
@[headline]
theorem soundness_qrom [DecidableEq X] (hrbr : CausalRBRKnowledgeSound rel V E St ε)
    {Qs : ∀ x, M.IOPQueries V x} {NQ N : ℕ} (hb : M.FormatBounds Qs NQ N) {t : ℕ}
    (𝒜 : NARG.QROM.Adversary (queryBits k kN kS L) k e (Claim X M.NIProof) t) :
    𝒜.acceptsFalse (M.qVerifier Qs NQ N) rel ≤
      knowledgeError k e (kqOf Mg n NQ N) (t + kqOf Mg n NQ N) M.senc.digestsPerInput Mg.nJ
        (maxError ε) :=
  soundness_toQVerifier hrbr (fun _ _ _ hv => queries_length_le_of_formatBounds hb hv) 𝒜

/-- **Online extractability in the ROM at the query budget of the format bounds.** -/
@[headline]
theorem onlineExtracts_rom [DecidableEq X] (hrbr : CausalRBRKnowledgeSound rel V E St ε)
    {Qs : ∀ x, M.IOPQueries V x} {NQ N : ℕ} (hb : M.FormatBounds Qs NQ N) {Z : Type} {t : ℕ}
    (𝒢 : NARG.ROM.Adversary (Query k kN kS L) (Out k e) (Claim X M.NIProof × Z) t) :
    𝒢.OnlineExtracts (M.rVerifier Qs NQ N) NARG.ROM.OracleSampler.lazy.law rel (M.dbExtract E) 0
      (knowledgeErrorROM k (t + kqOf Mg n NQ N) M.senc.digestsPerInput Mg.nJ (maxError ε)) :=
  onlineExtracts_toRVerifier hrbr (fun _ _ _ hv => queries_length_le_of_formatBounds hb hv) 𝒢

/-- **Soundness in the ROM at the query budget of the format bounds.** -/
@[headline]
theorem soundness_rom [DecidableEq X] (hrbr : CausalRBRKnowledgeSound rel V E St ε)
    {Qs : ∀ x, M.IOPQueries V x} {NQ N : ℕ} (hb : M.FormatBounds Qs NQ N) {t : ℕ}
    (𝒜 : NARG.ROM.Adversary (Query k kN kS L) (Out k e) (Claim X M.NIProof) t) :
    𝒜.acceptsFalse (M.rVerifier Qs NQ N) rel ≤
      knowledgeErrorROM k (t + kqOf Mg n NQ N) M.senc.digestsPerInput Mg.nJ (maxError ε) :=
  soundness_toRVerifier hrbr (fun _ _ _ hv => queries_length_le_of_formatBounds hb hv) 𝒜

/-- **Online extractability of the spBCS verifier in the ROM, with the round errors and the
collisions charged by entry class**, with a query budget `kq` (`hkq`), at
`knowledgeErrorROMTyped k t kq T (maxError ε) (∑ c, ε c)`, `T` the number of Merkle trees. -/
theorem onlineExtracts_toRVerifier_typed [DecidableEq X]
    (hrbr : CausalRBRKnowledgeSound rel V E St ε) {Qs : ∀ x, M.IOPQueries V x} {kq : ℕ}
    (hkq : M.QueriesAtMost Qs kq) {Z : Type}
    {t : ℕ} (𝒢 : NARG.ROM.Adversary (Query k kN kS L) (Out k e) (Claim X M.NIProof × Z) t) :
    𝒢.OnlineExtracts (M.toRVerifier Qs kq) NARG.ROM.OracleSampler.lazy.law rel (M.dbExtract E) 0
      (knowledgeErrorROMTyped k t kq (Fintype.card M.TreeSig) (maxError ε) (∑ c, ε c)) := by
  have := ROM.onlineExtracts (V := M.toRVerifier Qs kq) (rel := rel) (ext := M.dbExtract E)
    (β := fun b => knowledgeErrorROMTyped k (b - kq) kq (Fintype.card M.TreeSig) (maxError ε)
      (∑ c, ε c))
    (M.jointBound_typed rel E St hrbr Qs hkq) 𝒢
  simpa only [show (M.toRVerifier Qs kq).kq = kq from rfl, Nat.add_sub_cancel] using this

/-- **Soundness of the spBCS verifier in the ROM, with the round errors and the collisions
charged by entry class**, at the error of `onlineExtracts_toRVerifier_typed`. -/
theorem soundness_toRVerifier_typed [DecidableEq X]
    (hrbr : CausalRBRKnowledgeSound rel V E St ε) {Qs : ∀ x, M.IOPQueries V x} {kq : ℕ}
    (hkq : M.QueriesAtMost Qs kq) {t : ℕ}
    (𝒜 : NARG.ROM.Adversary (Query k kN kS L) (Out k e) (Claim X M.NIProof) t) :
    𝒜.acceptsFalse (M.toRVerifier Qs kq) rel ≤
      knowledgeErrorROMTyped k t kq (Fintype.card M.TreeSig) (maxError ε) (∑ c, ε c) := by
  have := ROM.soundness (V := M.toRVerifier Qs kq) (ext := M.dbExtract E)
    (β := fun b => knowledgeErrorROMTyped k (b - kq) kq (Fintype.card M.TreeSig) (maxError ε)
      (∑ c, ε c))
    (M.jointBound_typed rel E St hrbr Qs hkq) 𝒜
  simpa only [show (M.toRVerifier Qs kq).kq = kq from rfl, Nat.add_sub_cancel] using this

/-- **Online extractability in the ROM at the query budget of the format bounds, with the round
errors and the collisions charged by entry class** (`onlineExtracts_toRVerifier_typed` at
`kqOf Mg n NQ N`): `t · maxError ε + ∑ c, ε c + maxError ε +
(t + kq)(max 2 T + 1)(t + kq) / 2^(8k)`. -/
theorem onlineExtracts_rom_typed [DecidableEq X] (hrbr : CausalRBRKnowledgeSound rel V E St ε)
    {Qs : ∀ x, M.IOPQueries V x} {NQ N : ℕ} (hb : M.FormatBounds Qs NQ N) {Z : Type} {t : ℕ}
    (𝒢 : NARG.ROM.Adversary (Query k kN kS L) (Out k e) (Claim X M.NIProof × Z) t) :
    𝒢.OnlineExtracts (M.rVerifier Qs NQ N) NARG.ROM.OracleSampler.lazy.law rel (M.dbExtract E) 0
      (knowledgeErrorROMTyped k t (kqOf Mg n NQ N) (Fintype.card M.TreeSig) (maxError ε)
        (∑ c, ε c)) :=
  onlineExtracts_toRVerifier_typed hrbr (fun _ _ _ hv => queries_length_le_of_formatBounds hb hv) 𝒢

/-- **Soundness in the ROM at the query budget of the format bounds, with the round errors and
the collisions charged by entry class**, at the error of `onlineExtracts_rom_typed`. -/
theorem soundness_rom_typed [DecidableEq X] (hrbr : CausalRBRKnowledgeSound rel V E St ε)
    {Qs : ∀ x, M.IOPQueries V x} {NQ N : ℕ} (hb : M.FormatBounds Qs NQ N) {t : ℕ}
    (𝒜 : NARG.ROM.Adversary (Query k kN kS L) (Out k e) (Claim X M.NIProof) t) :
    𝒜.acceptsFalse (M.rVerifier Qs NQ N) rel ≤
      knowledgeErrorROMTyped k t (kqOf Mg n NQ N) (Fintype.card M.TreeSig) (maxError ε)
        (∑ c, ε c) :=
  soundness_toRVerifier_typed hrbr (fun _ _ _ hv => queries_length_le_of_formatBounds hb hv) 𝒜

end

end GordieHowe.SPBCS
