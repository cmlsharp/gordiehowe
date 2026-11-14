-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Knowledge
public import GordieHowe.SPBCS.StabilitySlots
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
With the round errors charged by entry class (`prob_log_append_bad_union_le`,
`knowledge_of_causalRBR_rom_joint_typed`): for the algorithm followed by the verifier's queries,
the weighted union bound (`ROM.Alg.prob_log_mem_le_of_weight`) charges every step the collision
bound of its class (`slotCollisionBound`) and one answer collision, each of the algorithm's `t`
steps the largest round error, each verifier stream point of a
round that round's error (its key query precedes it, `inputsBefore_queries`), and the padding
point the largest round error once (`ROM.Alg.sum_fresh_eq`): `knowledgeErrorROMTyped`,
`t κ + ∑ ε + κ + (t + kq)(max 2 T + 1)(t + kq) / 2^(8k)` with `T` the number of Merkle trees.
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

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- **The log of a classical `tq`-query algorithm lies in `bad ∪ P_col` at a flip bound**: for
every bound `maxError ε + (max 2 c + cP) t / 2^(8k)` on the flip into `bad` given no digest
collision (`hF`), with probability at most `knowledgeErrorROM k tq c cP (maxError ε)`. -/
theorem prob_log_bad_union_le_of (c cP : ℕ)
    (hF : ∀ tq, condFlip (M.bad rel E St) digestCollisionᶜ tq ≤
      maxError ε + (((max 2 c + cP) * tq : ℕ) : ℝ≥0∞) / 2 ^ (8 * k)) {C : Type}
    {tq : ℕ} (𝒜 : ROM.Alg (Query k kN kS L) (Out k e) C tq) :
    Pr[h ← (Query k kN kS L → Out k e) : 𝒜.log h tq ∈ M.bad rel E St ∪ digestCollision] ≤
      knowledgeErrorROM k tq c cP (maxError ε) := by
  have h0 : (∅ : ODB k kN kS L e) ∉ M.bad rel E St ∪ digestCollision := fun h =>
    h.elim (M.empty_notMem_bad rel E St) empty_notMem_collisionOn
  refine (𝒜.prob_log_mem_le h0).trans ?_
  rw [knowledgeErrorROM]
  gcongr
  calc flipProb (M.bad rel E St ∪ digestCollision)ᶜ (M.bad rel E St ∪ digestCollision) tq
      ≤ condFlip (M.bad rel E St) digestCollisionᶜ tq +
          flipProb digestCollisionᶜ digestCollision tq :=
        ROM.flipProb_compl_union_le
    _ ≤ (maxError ε + (((max 2 c + cP) * tq : ℕ) : ℝ≥0∞) /
          2 ^ (8 * k)) + (tq : ℝ≥0∞) / 2 ^ (8 * k) :=
        add_le_add (hF tq) (flipProb_compl_le_instab.trans instab_digestCollision_le)
    _ = _ := by
        rw [add_assoc, ENNReal.div_add_div_same, ← Nat.cast_add, add_mul _ 1, one_mul]

/-- **The log of a classical `tq`-query algorithm lies in `bad ∪ P_col`** with probability at
most `knowledgeErrorROM k tq c nJ (maxError ε)`. -/
theorem prob_log_bad_union_le (hrbr : CausalRBRKnowledgeSound rel V E St ε) {C : Type}
    {tq : ℕ} (𝒜 : ROM.Alg (Query k kN kS L) (Out k e) C tq) :
    Pr[h ← (Query k kN kS L → Out k e) : 𝒜.log h tq ∈ M.bad rel E St ∪ digestCollision] ≤
      knowledgeErrorROM k tq M.senc.digestsPerInput Mg.nJ (maxError ε) :=
  M.prob_log_bad_union_le_of rel E St _ _ (fun _ => M.condFlip_bad_le rel E St hrbr) 𝒜

/-- **The log of a classical `tq`-query algorithm lies in `bad ∪ P_col` at the slot constant**:
with probability at most `knowledgeErrorROM k tq T 0 (maxError ε)`, that is
`tq (maxError ε + (max 2 T + 1) tq / 2^(8k))`, `T` the Merkle trees (`condFlip_bad_le_slot`). -/
theorem prob_log_bad_union_le_slot (hrbr : CausalRBRKnowledgeSound rel V E St ε) {C : Type}
    {tq : ℕ} (𝒜 : ROM.Alg (Query k kN kS L) (Out k e) C tq) :
    Pr[h ← (Query k kN kS L → Out k e) : 𝒜.log h tq ∈ M.bad rel E St ∪ digestCollision] ≤
      knowledgeErrorROM k tq (Fintype.card M.TreeSig) 0 (maxError ε) :=
  M.prob_log_bad_union_le_of rel E St (Fintype.card M.TreeSig) 0 (fun tq => by
    simpa only [Nat.add_zero] using M.condFlip_bad_le_slot rel E St hrbr (tq := tq)) 𝒜

/-- **Knowledge soundness of the spBCS argument in the ROM, joint form** (CY24 Definition
5.1.1, p. 48): the probability that the spBCS verifier accepts the claim of `𝒜` and the
database extractor at `E` returns no witness from the log of `𝒜` followed by the verifier's `kq`
queries is at most `knowledgeErrorROM k (t + kq) c nJ κ`. -/
theorem knowledge_of_causalRBR_rom_joint [DecidableEq X] (Qs : ∀ x, M.IOPQueries V x)
    (hrbr : CausalRBRKnowledgeSound rel V E St ε) {κ : ℝ≥0} (hκ : ∀ c, ε c ≤ κ) {kq : ℕ}
    (hkq : M.QueriesAtMost Qs kq) {tq : ℕ}
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

/-- **The log of an algorithm followed by the spBCS verifier's queries lies in `bad ∪ P_col`**
with probability at most `knowledgeErrorROMTyped`: each step is charged the collision bound of
its class (`slotCollisionBound`) and one answer collision, each step of the algorithm the
largest round error, the verifier's stream point of a round that
round's error, and its padding point the largest round error once. -/
theorem prob_log_append_bad_union_le (Qs : ∀ x, M.IOPQueries V x)
    (hrbr : CausalRBRKnowledgeSound rel V E St ε) {tq kq : ℕ}
    (𝒜 : ROM.Alg (Query k kN kS L) (Out k e) (Claim X M.NIProof) tq) :
    Pr[h ← (Query k kN kS L → Out k e) :
        (𝒜.append (M.expansion Qs) kq).log h (tq + kq) ∈ M.bad rel E St ∪ digestCollision] ≤
      knowledgeErrorROMTyped k tq kq (Fintype.card M.TreeSig) (maxError ε) (∑ c, ε c) := by
  classical
  have h0 : (∅ : ODB k kN kS L e) ∉ M.bad rel E St ∪ digestCollision := fun h =>
    h.elim (M.empty_notMem_bad rel E St) empty_notMem_collisionOn
  let Xp := M.expansion Qs
  let 𝒜' := 𝒜.append Xp kq
  let T := tq + kq
  let pad : Query k kN kS L := .xof (fun _ => 0) fun _ => 0
  let κ : ℝ≥0∞ := (maxError ε : ℝ≥0∞)
  -- the verifier's queries on the algorithm's claim
  let Q : (Query k kN kS L → Out k e) → List (Query k kN kS L) := fun h =>
    M.queries (𝒜.output h).stmt (𝒜.output h).proof h (Qs (𝒜.output h).stmt)
  let xp : (Query k kN kS L → Out k e) → (Σ p : t.Leaf, Fin (n p.label)) → Query k kN kS L :=
    fun h s => M.slotPoint (𝒜.output h).stmt (𝒜.output h).proof h s.1 s.2 s.2.2.le
  let extra : (Query k kN kS L → Out k e) → Query k kN kS L → ℝ≥0∞ := fun h a =>
    (∑ s, if a = xp h s then (slotError ε s.1 s.2 : ℝ≥0∞) else 0) + if a = pad then κ else 0
  let base : ℝ≥0∞ := M.slotCollisionBound T + (T : ℝ≥0∞) / 2 ^ (8 * k)
  let w : ℕ → (Query k kN kS L → Out k e) → ℝ≥0∞ := fun j h =>
    base + if j < tq then κ else if 𝒜'.queryAt h j ∈ 𝒜'.queries h j then 0
      else extra h (𝒜'.queryAt h j)
  -- the run of the expansion and the queries of the appended algorithm after `tq`
  have hrun : ∀ h i, Xp.run h (𝒜.output h) i =
      (List.range i).map fun j => ((Q h)[j]?).getD pad := fun h i =>
    Expansion.run_eq_of_next Xp h (𝒜.output h)
      ((M.queryProg (𝒜.output h).stmt (𝒜.output h).proof (Qs (𝒜.output h).stmt)).paddedTrace_eq_next
        h pad) i
  have hqa : ∀ h i, 𝒜'.queryAt h (tq + i) = ((Q h)[i]?).getD pad := by
    intro h i
    have h1 : 𝒜'.queries h (tq + i + 1) = _ := 𝒜.queries_append_add Xp kq h (i + 1)
    have h3 : 𝒜'.queries h (tq + i) = _ := 𝒜.queries_append_add Xp kq h i
    rw [ROM.Alg.queries_succ, h3, Expansion.run_succ, ← List.append_assoc] at h1
    have h2 := List.singleton_inj.1 (List.append_cancel_left h1)
    rw [h2, hrun, List.map_map]
    exact ((M.queryProg (𝒜.output h).stmt (𝒜.output h).proof
      (Qs (𝒜.output h).stmt)).paddedTrace_eq_next h pad i).symm
  have hlog : ∀ h i j' (hj' : j' < (Q h).length), j' < i →
      (𝒜'.log h (tq + i)).lookup (Q h)[j'] = some (h (Q h)[j']) := by
    intro h i j' hj' hji
    have h3 : 𝒜'.queries h (tq + i) = _ := 𝒜.queries_append_add Xp kq h i
    rw [ROM.Alg.log, h3]
    refine ROM.lookup_logOf_of_mem (List.mem_append_right _ ?_)
    rw [hrun]
    exact List.mem_map.2 ⟨j', List.mem_range.2 hji, by simp [List.getElem?_eq_getElem hj']⟩
  refine (𝒜'.prob_log_mem_le_of_weight h0 w ?_ (β := T * base + (tq * κ + ((∑ c, ε c : ℝ≥0) + κ)))
    ?_).trans ?_
  · -- the flip of each fresh step
    intro j hj h hq hD
    set D := 𝒜'.log h j
    have hDb : D ∉ M.bad rel E St := fun hb => hD (Or.inl hb)
    have hDc : D ∉ digestCollision := fun hc => hD (Or.inr hc)
    have hs : D.size < T := (𝒜'.size_log_le h j).trans_lt hj
    have hqD : 𝒜'.queryAt h j ∉ D := by
      change _ ∉ ROM.logOf h _; rw [ROM.mem_logOf]; exact hq
    have hcol : Pr[y ← Out k e : D.extend (𝒜'.queryAt h j) y ∈ digestCollision] ≤
        (T : ℝ≥0∞) / 2 ^ (8 * k) :=
      (le_flipProb hDc hs hqD).trans (flipProb_compl_le_instab.trans instab_digestCollision_le)
    suffices hbad : Pr[y ← Out k e : D.extend (𝒜'.queryAt h j) y ∈
        M.bad rel E St ∩ digestCollisionᶜ] ≤ (if j < tq then κ else if 𝒜'.queryAt h j ∈
          𝒜'.queries h j then 0 else extra h (𝒜'.queryAt h j)) + M.slotCollisionBound T by
      calc Pr[y ← Out k e : D.extend (𝒜'.queryAt h j) y ∈ M.bad rel E St ∪ digestCollision]
          ≤ Pr[y ← Out k e : D.extend (𝒜'.queryAt h j) y ∈ M.bad rel E St ∩ digestCollisionᶜ ∨
              D.extend (𝒜'.queryAt h j) y ∈ digestCollision] :=
            QROM.probUniform_mono fun y hy => by
              by_cases hc : D.extend (𝒜'.queryAt h j) y ∈ digestCollision
              · exact Or.inr hc
              · exact Or.inl ⟨hy.resolve_right hc, hc⟩
        _ ≤ _ := probUniform_or_le _ _
        _ ≤ _ := add_le_add hbad hcol
        _ = w j h := by simp only [w, base]; ring
    by_cases hjt : j < tq
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hjt)]
      exact flip_bad_le_slot hDb hDc hs hqD (prob_nextBad_le hDc hrbr)
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hjt), ite_eq_right_of_eq_false _ _ (eq_false hq)]
      obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 hjt)
      have hq' := hqa h i
      cases hQi : (Q h)[i]? with
      | none =>
        rw [hQi, Option.getD_none] at hq'
        rw [hq'] at hqD ⊢
        refine (flip_bad_le_slot hDb hDc hs hqD (prob_nextBad_le hDc hrbr)).trans
          (add_le_add ?_ le_rfl)
        simp only [extra, ite_true]
        exact le_add_self
      | some q₀ =>
        rw [hQi, Option.getD_some] at hq'
        rw [hq'] at hqD ⊢
        have hi : i < (Q h).length := (List.getElem?_eq_some_iff.1 hQi).1
        have hq₀ : (Q h)[i] = q₀ := (List.getElem?_eq_some_iff.1 hQi).2
        by_cases hx : q₀.IsXof
        · obtain ⟨a, ha, p, r, hr, rfl, hb⟩ := M.inputsBefore_queries (𝒜.output h).stmt
            (𝒜.output h).proof h (Qs (𝒜.output h).stmt) i hi (hq₀ ▸ hx)
          rw [hq₀] at hb
          obtain ⟨j', hj', hja⟩ := List.getElem_of_mem ha
          rw [List.getElem_take] at hja
          have hj'i : j' < i := by simp at hj'; omega
          have hrec := hlog h i j' (by simp at hj'; omega) hj'i
          rw [hja] at hrec
          rw [hb]
          have hnb := prob_nextBad_recorded_le hDc hrbr
            (hwf := fun q _ => ⟨chainWF_chains _ q, length_chains _ q⟩)
            (hl := ComponentModel.chainWF_chainWith _ _ _ _ _ _ _)
            (hlen := by rw [ComponentModel.length_chainWith]; exact hr) hrec
            (𝒜.output h).proof.salt
          have := flip_bad_le_slot hDb hDc hs (by rw [hb] at hqD; exact hqD)
            (β := (slotError ε p _ : ℝ≥0∞)) (by exact_mod_cast hnb)
          rw [ComponentModel.length_chainWith] at this
          refine this.trans (add_le_add ?_ le_rfl)
          refine le_add_right ((Finset.single_le_sum (f := fun s =>
            if M.slotPoint (𝒜.output h).stmt (𝒜.output h).proof h p r hr.le = xp h s then
              (slotError ε s.1 s.2 : ℝ≥0∞) else 0) (fun _ _ => zero_le)
              (Finset.mem_univ ⟨p, ⟨r, hr⟩⟩)).trans_eq' ?_)
          simp [xp]
        · refine (flip_bad_le_slot hDb hDc hs hqD (prob_nextBad_eq_zero
            fun _ _ _ _ he => hx ⟨_, _, he⟩).le).trans ?_
          exact add_le_add zero_le le_rfl
  · -- the weights of one oracle
    intro h
    have hsplit : ∀ j : Fin T, w j h ≤ base + ((if (j : ℕ) < tq then κ else 0) +
        if 𝒜'.queryAt h j ∈ 𝒜'.queries h j then 0 else extra h (𝒜'.queryAt h j)) := by
      intro j
      simp only [w]
      gcongr
      split_ifs <;> simp
    have hfresh : ∑ j : Fin T, (if 𝒜'.queryAt h j ∈ 𝒜'.queries h j then 0
        else extra h (𝒜'.queryAt h j)) = ∑ a ∈ (𝒜'.queries h T).toFinset, extra h a := by
      rw [Fin.sum_univ_eq_sum_range (fun j => if 𝒜'.queryAt h j ∈ 𝒜'.queries h j then 0
        else extra h (𝒜'.queryAt h j)), 𝒜'.sum_fresh_eq h (extra h) T]
    have hadv : ∑ j : Fin T, (if (j : ℕ) < tq then κ else 0) = tq * κ := by
      rw [Fin.sum_univ_eq_sum_range (fun j => if j < tq then κ else 0), Finset.sum_range_add]
      have h1 : ∑ x ∈ Finset.range tq, (if x < tq then κ else 0) = tq * κ := by
        rw [Finset.sum_congr rfl fun x hx =>
          ite_eq_left_of_eq_true _ _ (eq_true (Finset.mem_range.1 hx))]
        simp
      have h2 : ∑ x ∈ Finset.range kq, (if tq + x < tq then κ else 0) = 0 :=
        Finset.sum_eq_zero fun x _ => ite_eq_right_of_eq_false _ _ (eq_false (by omega))
      rw [h1, h2, add_zero]
    have hextra : ∑ a ∈ (𝒜'.queries h T).toFinset, extra h a ≤ (∑ c, ε c : ℝ≥0) + κ := by
      simp only [extra, Finset.sum_add_distrib]
      gcongr
      · rw [Finset.sum_comm]
        calc ∑ s, ∑ a ∈ (𝒜'.queries h T).toFinset,
              (if a = xp h s then (slotError ε s.1 s.2 : ℝ≥0∞) else 0)
            ≤ ∑ s : (Σ p : t.Leaf, Fin (n p.label)), (slotError ε s.1 s.2 : ℝ≥0∞) :=
              Finset.sum_le_sum fun s _ => by
                rw [Finset.sum_ite_eq']
                split_ifs <;> simp
          _ = (∑ c, ε c : ℝ≥0) := by rw [← sum_slotError ε]; push_cast; rfl
      · rw [Finset.sum_ite_eq']
        split_ifs <;> simp
    calc ∑ j : Fin T, w j h
        ≤ ∑ j : Fin T, (base + ((if (j : ℕ) < tq then κ else 0) +
            if 𝒜'.queryAt h j ∈ 𝒜'.queries h j then 0 else extra h (𝒜'.queryAt h j))) :=
          Finset.sum_le_sum fun j _ => hsplit j
      _ = T * base + (tq * κ + ∑ a ∈ (𝒜'.queries h T).toFinset, extra h a) := by
          rw [Finset.sum_add_distrib (f := fun _ => base),
            Finset.sum_add_distrib (f := fun j : Fin T => if (j : ℕ) < tq then κ else 0),
            hfresh, hadv]
          simp
      _ ≤ _ := by gcongr
  · -- the total
    rw [knowledgeErrorROMTyped]
    simp only [base, slotCollisionBound]
    rw [ENNReal.div_add_div_same, ← Nat.cast_add, add_mul _ 1, one_mul]
    apply le_of_eq
    simp only [κ, T]
    push_cast
    ring

/-- **Knowledge soundness of the spBCS argument in the ROM, joint form, with the round errors
charged by entry class**: as `knowledge_of_causalRBR_rom_joint`, at
`knowledgeErrorROMTyped k t kq T κ (∑ c, ε c)` with `T` the number of Merkle trees:
`t κ + ∑ c, ε c + κ + (t + kq)(max 2 T + 1)(t + kq) / 2^(8k)`. -/
theorem knowledge_of_causalRBR_rom_joint_typed [DecidableEq X] (Qs : ∀ x, M.IOPQueries V x)
    (hrbr : CausalRBRKnowledgeSound rel V E St ε) {κ : ℝ≥0} (hκ : ∀ c, ε c ≤ κ) {kq : ℕ}
    (hkq : M.QueriesAtMost Qs kq) {tq : ℕ}
    (𝒜 : ROM.Alg (Query k kN kS L) (Out k e) (Claim X M.NIProof) tq) :
    Pr[h ← (Query k kN kS L → Out k e) :
        M.Accepts h (𝒜.output h).stmt (𝒜.output h).proof (Qs (𝒜.output h).stmt) ∧
        (𝒜.append (M.expansion Qs) kq).log h (tq + kq) ∉ M.extracts rel E (𝒜.output h).stmt] ≤
      knowledgeErrorROMTyped k tq kq (Fintype.card M.TreeSig) κ (∑ c, ε c) := by
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
    _ ≤ _ := (M.prob_log_append_bad_union_le rel E St Qs hrbr 𝒜).trans
        (knowledgeErrorROMTyped_mono le_rfl (maxError_le_iff.2 hκ) le_rfl)

end

end GordieHowe.SPBCS
