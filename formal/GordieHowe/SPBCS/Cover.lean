-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Verifier

@[expose] public section

/-!
# An accepted spBCS proof is an accepted proof of the compiler over the term

A database `D` that records the spBCS verifier's queries on an accepted proof with the
answers of `h` translates (`GordieHowe.SPBCS.trans`, `GordieHowe/SPBCS/Translate.lean`) into a database that
records the queries of the compiler over the term (`GordieHowe.SPBCS.FullPast`) on the same proof, under the
oracle `transOracle D h` that answers each translated query as `D` answered its preimage. Under
that oracle the keys, chains and challenges of the compiler over the term are those of the
spBCS verifier (`chains_transOracle`, `chalOf_transOracle`), the Merkle queries are answered
as by `h`, and the proof is accepted (`accepts_transOracle`). So CMS19 Proposition 8.12 for the
compiler over the term applies to the translated database (`mem_of_verify`).
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm

variable {ι : Type} {t : SPTerm ι} {Mg : Merges t} {k kN kS L e : ℕ} {n : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (n j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] {X : Type}

section

variable (M : SPBCS Mg P X k kN kS L e)

/-- **The oracle of the translated database**: its answer at a translated query, `h` elsewhere. -/
def transOracle (D : ODB k kN kS L e) (h : Query k kN kS L → Out k e) : Query k kN kS L → Out k e :=
  fun q => ((M.trans D).lookup q).getD (h q)

/-! ### Reading the translated database -/

section Lookup

variable {M} {D : ODB k kN kS L e}

theorem trans_lookup_of (hD : D ∉ digestCollision) {q q' : Query k kN kS L} {y : Out k e}
    (hq : D.lookup q = some y) (hφ : M.φ D q = some q') : (M.trans D).lookup q' = some y :=
  DB.lookup_image_of_lookup (injOnKeys_φ hD) hq hφ

theorem transOracle_of (hD : D ∉ digestCollision) (h : Query k kN kS L → Out k e)
    {q q' : Query k kN kS L} {y : Out k e} (hq : D.lookup q = some y) (hφ : M.φ D q = some q') :
    M.transOracle D h q' = y := by
  rw [transOracle, trans_lookup_of hD hq hφ, Option.getD_some]

/-- Only a Merkle query translates to itself. -/
theorem φ_eq_merkle_iff {q q' : Query k kN kS L} (hq' : (∃ a b, q' = .leaf a b) ∨ ∃ l r, q' = .node l r) :
    M.φ D q = some q' ↔ q = q' := by
  constructor
  · intro h
    cases q with
    | leaf a b => exact Option.some_inj.1 h
    | node l r => exact Option.some_inj.1 h
    | transcript c =>
      obtain ⟨_, _, _, _, _, rfl⟩ := φ_transcript_eq_some h
      rcases hq' with ⟨_, _, h'⟩ | ⟨_, _, h'⟩ <;> cases h'
    | xof u s =>
      rw [φ_of_not_transcript (fun b h' => by cases h')] at h
      rcases hq' with ⟨_, _, h'⟩ | ⟨_, _, h'⟩ <;> rw [h'] at h <;> cases h
  · rintro rfl
    rcases hq' with ⟨a, b, rfl⟩ | ⟨l, r, rfl⟩ <;> rfl

/-- **The translated database answers a Merkle query as `D`.** -/
theorem trans_lookup_merkle (hD : D ∉ digestCollision) {q : Query k kN kS L}
    (hq : (∃ a b, q = .leaf a b) ∨ ∃ l r, q = .node l r) : (M.trans D).lookup q = D.lookup q := by
  rcases hl : D.lookup q with _ | y
  · rw [trans, DB.lookup_image]
    refine DB.select_eq_none_of_forall fun q₀ y₀ hq₀ => ?_
    simp only [ite_eq_right_iff, reduceCtorEq, imp_false]
    intro h
    rw [φ_eq_merkle_iff hq] at h
    subst h
    rw [hl] at hq₀
    cases hq₀
  · exact trans_lookup_of hD hl ((φ_eq_merkle_iff hq).2 rfl)

end Lookup

/-! ### The translated oracle computes the chains with merges -/

section Chains

variable {M} [∀ j i, Nonempty ((P j).Challenge i)] {h : Query k kN kS L → Out k e} {x : X}
  {π : M.NIProof} {V : X → FullTr P t → Bool} {Q : M.IOPQueries V x} {D : ODB k kN kS L e}

/-- `D` records every query of the spBCS verifier on `π` with the answer of `h`. -/
def RecordsQueries (D : ODB k kN kS L e) (h : Query k kN kS L → Out k e) (x : X) (π : M.NIProof)
    (Q : M.IOPQueries V x) : Prop :=
  ∀ q ∈ M.queries x π h Q, Recorded h D q

theorem RecordsQueries.of_rounds (hrec : RecordsQueries D h x π Q) {q : Query k kN kS L}
    (hq : q ∈ (M.roundsProg x π).trace h) : Recorded h D q :=
  hrec q (by rw [queries_eq]; exact List.mem_append_left _ hq)

theorem RecordsQueries.finals (hrec : RecordsQueries D h x π Q) :
    M.RecordsFinals h (M.ssOf x π) π.writes D :=
  fun s => hrec.of_rounds (M.mem_roundsProg_final x π h s)

variable (hD : D ∉ digestCollision) (hrec : RecordsQueries D h x π Q)
include hD hrec

/-- **The keys of the compiler over the term under the translated oracle** at the chains of the
proof are the keys with merges. -/
theorem key_transOracle (p : t.Leaf) (r : ℕ) (hr : r < n p.label) :
    M.toFullPast.keyFullPast (M.transOracle D h) x π.salt p (M.ctx h (M.ssOf x π) π.writes p)
        ((M.comp p.label).chainWith (π.writes p)
          (M.key h (M.ssOf x π) (M.chains h (M.ssOf x π) π.writes) (M.finals h (M.ssOf x π) π.writes) p)
          π.salt h r hr.le) =
      M.key h (M.ssOf x π) (M.chains h (M.ssOf x π) π.writes) (M.finals h (M.ssOf x π) π.writes) p
        ((M.comp p.label).chainWith (π.writes p)
          (M.key h (M.ssOf x π) (M.chains h (M.ssOf x π) π.writes) (M.finals h (M.ssOf x π) π.writes) p)
          π.salt h r hr.le) := by
  unfold FullPast.keyFullPast
  rw [transOracle_of hD h (hrec.of_rounds (M.mem_roundsProg_input x π h p r hr).1)
    (φ_transcript_honest hD hrec.finals p ((M.comp p.label).chainWF_chainWith _ _ _ _ r hr.le)
      (by rw [ComponentModel.length_chainWith]; exact hr))]
  rfl

theorem point_transOracle (p : t.Leaf) (r : ℕ) (hr : r < n p.label) :
    M.transOracle D h (.xof (M.key h (M.ssOf x π) (M.chains h (M.ssOf x π) π.writes)
        (M.finals h (M.ssOf x π) π.writes) p
        ((M.comp p.label).chainWith (π.writes p)
          (M.key h (M.ssOf x π) (M.chains h (M.ssOf x π) π.writes) (M.finals h (M.ssOf x π) π.writes) p)
          π.salt h r hr.le)) π.salt) =
      h (.xof (M.key h (M.ssOf x π) (M.chains h (M.ssOf x π) π.writes)
        (M.finals h (M.ssOf x π) π.writes) p
        ((M.comp p.label).chainWith (π.writes p)
          (M.key h (M.ssOf x π) (M.chains h (M.ssOf x π) π.writes) (M.finals h (M.ssOf x π) π.writes) p)
          π.salt h r hr.le)) π.salt) :=
  transOracle_of hD h (hrec.of_rounds (M.mem_roundsProg_input x π h p r hr).2)
    (φ_of_not_transcript fun _ h' => by cases h')

/-- **A leaf's chain under the translated oracle**, in the context of the chains of the proof, is
its chain with merges. -/
theorem leafChain_transOracle (p : t.Leaf) (r : ℕ) (hr : r ≤ n p.label) :
    M.toFullPast.leafChainFullPast (M.transOracle D h) x π.salt π.writes p (M.ctx h (M.ssOf x π) π.writes p) r hr =
      (M.comp p.label).chainWith (π.writes p)
        (M.key h (M.ssOf x π) (M.chains h (M.ssOf x π) π.writes) (M.finals h (M.ssOf x π) π.writes) p)
        π.salt h r hr := by
  rw [FullPast.leafChainFullPast_eq_chainWith]
  refine ((M.comp p.label).chainWith_congr r hr fun j hj => ?_).symm
  have hk := key_transOracle hD hrec p j (by omega)
  have hp := point_transOracle hD hrec p j (by omega)
  rw [hk, hp]

/-- **The chains of the compiler over the term under the translated oracle are the chains with
merges.** -/
theorem chains_transOracle :
    M.toFullPast.chainsFullPast (M.transOracle D h) x π.salt π.writes = M.chains h (M.ssOf x π) π.writes :=
  (solve_unique _ _ fun p => ((leafChain_transOracle hD hrec p _ le_rfl).trans
    (chains_eq_chainWith π.writes p).symm).symm).symm

theorem ctxOf_transOracle (p : t.Leaf) :
    M.toFullPast.ctxOf (M.transOracle D h) x π.salt π.writes p = M.ctx h (M.ssOf x π) π.writes p := by
  funext q
  exact congrFun (chains_transOracle hD hrec) q.1

/-- **The challenges of the compiler over the term under the translated oracle are the challenges
with merges.** -/
theorem chalOf_transOracle (c : ChIdx P t) :
    M.toFullPast.chalOf (M.transOracle D h) x π.salt π.writes c = M.chal h (M.ssOf x π) π.writes c := by
  rw [FullPast.chalOf, ctxOf_transOracle hD hrec, leafChain_transOracle hD hrec,
    key_transOracle hD hrec _ _ c.idx.1.2, point_transOracle hD hrec _ _ c.idx.1.2]
  rfl

theorem chV_transOracle :
    M.toFullPast.chVFullPast (M.transOracle D h) x π.salt π.writes = M.chV h (M.ssOf x π) π.writes := by
  funext c
  simp only [FullPast.chVFullPast, chV, chalOf_transOracle hD hrec]

/-- **The translated oracle answers the verifier's Merkle queries as `h`.** -/
theorem transOracle_tree {τ : M.Tree}
    (hτ : τ ∈ M.trees (Q.pos (M.chains h (M.ssOf x π) π.writes) (M.chV h (M.ssOf x π) π.writes)))
    {q : Query k kN kS L} (hq : q ∈ (M.treeProg π (Q.pos (M.chains h (M.ssOf x π) π.writes)
      (M.chV h (M.ssOf x π) π.writes)) τ).trace h) : M.transOracle D h q = h q := by
  have hrq : Recorded h D q := hrec q (by
    rw [queries_eq]
    exact List.mem_append_right _ (List.mem_flatMap.2 ⟨τ, hτ, hq⟩))
  have hm : (∃ a b, q = .leaf a b) ∨ ∃ l r, q = .node l r := M.opening.merkle_of_mem_trace hq
  rw [transOracle, trans_lookup_merkle hD hm, hrq, Option.getD_some]

/-- **An accepted spBCS proof is accepted by the compiler over the term under the
translated oracle.** -/
theorem accepts_transOracle (hv : M.Accepts h x π Q) : M.toFullPast.AcceptsFullPast (M.transOracle D h) x π Q where
  sampled c := by
    rw [chalOf_transOracle hD hrec]
    exact hv.sampled c
  leaves_length := by
    rw [chains_transOracle hD hrec, chV_transOracle hD hrec]
    exact hv.leaves_length
  paths τ hτ := by
    rw [chains_transOracle hD hrec, chV_transOracle hD hrec] at hτ ⊢
    obtain ⟨h1, h2, h3, h4, h5⟩ := hv.paths τ hτ
    refine ⟨h1, h2, h3, h4, ?_⟩
    rw [← h5]
    exact (GordieHowe.OracleProg.run_congr _ fun a ha => (transOracle_tree hD hrec hτ ha).symm).symm
  decides := by
    rw [chains_transOracle hD hrec, chV_transOracle hD hrec]
    exact hv.decides

/-- **Every query of the compiler over the term under the translated oracle** is recorded in the
translated database with the oracle's answer. -/
theorem mem_trans_of_queries :
    ∀ q ∈ M.toFullPast.queriesFullPast x π (M.transOracle D h) Q,
      (M.trans D).lookup q = some (M.transOracle D h q) := by
  have hfix : ∀ {q : Query k kN kS L} {y : Out k e}, (M.trans D).lookup q = some y →
      (M.trans D).lookup q = some (M.transOracle D h q) := fun hy => by
    rw [transOracle, hy, Option.getD_some]
  intro q hq
  rw [FullPast.queriesFullPast_eq] at hq
  rcases List.mem_append.1 hq with hq | hq
  · rcases M.toFullPast.isChainQuery_of_mem_trace_roundsProgFullPast (M.transOracle D h) x π _ hq with
      ⟨b, rfl⟩ | ⟨d, s, rfl⟩
    · obtain ⟨p, r, rfl⟩ := M.toFullPast.transcript_mem_trace_roundsProgFullPast (M.transOracle D h) x π _ le_rfl hq
      rw [Base.inputAt, chains_transOracle hD hrec]
      have hctx : M.ctxOfChains p (M.chains h (M.ssOf x π) π.writes) = M.ctx h (M.ssOf x π) π.writes p :=
        rfl
      rw [hctx, ctxOf_transOracle hD hrec, leafChain_transOracle hD hrec]
      exact hfix (trans_lookup_of hD (hrec.of_rounds (M.mem_roundsProg_input x π h p r r.2).1)
        (φ_transcript_honest hD hrec.finals p ((M.comp p.label).chainWF_chainWith _ _ _ _ r r.2.le)
          (by rw [ComponentModel.length_chainWith]; exact r.2)))
    · obtain ⟨p, r, rfl, rfl, -⟩ := M.toFullPast.xof_mem_trace_roundsProgFullPast (M.transOracle D h) x π _ le_rfl hq
      rw [ctxOf_transOracle hD hrec, leafChain_transOracle hD hrec,
        key_transOracle hD hrec p r r.2]
      exact hfix (trans_lookup_of hD (hrec.of_rounds (M.mem_roundsProg_input x π h p r r.2).2)
        (φ_of_not_transcript fun _ h' => by cases h'))
  · obtain ⟨τ, hτ, hq⟩ := List.mem_flatMap.1 hq
    rw [chains_transOracle hD hrec, chV_transOracle hD hrec] at hτ hq
    rw [← GordieHowe.OracleProg.trace_congr _ fun a ha => (transOracle_tree hD hrec hτ ha).symm] at hq
    have hrq : Recorded h D q := hrec q (by
      rw [queries_eq]
      exact List.mem_append_right _ (List.mem_flatMap.2 ⟨τ, hτ, hq⟩))
    have hm : (∃ a b, q = .leaf a b) ∨ ∃ l r, q = .node l r := M.opening.merkle_of_mem_trace hq
    exact hfix ((trans_lookup_merkle hD hm).trans hrq)

end Chains

/-! ### Proposition 8.12 for spBCS -/

section Prop812

variable {M} [∀ j i, Nonempty ((P j).Challenge i)] {V : X → FullTr P t → Bool} {Wit : Type}
  (rel : Set (X × Wit)) (E : CausalExtractor P t X Wit) (St : CausalStateFn P t X)
  {ε : ChIdx P t → NNReal}

/-- **CMS19 Proposition 8.12** (p. 42), knowledge form (p. 44), for the spBCS compiler at
one accepted proof: a database that records the verifier's queries on an accepted proof `π` of `x`
with the answers of `h` has a digest collision, or its translation extracts a witness at `x`,
lies in `badAny` of the compiler over the term, or has a digest collision. -/
theorem mem_of_verify [DecidableEq X] (hrbr : CausalRBRKnowledgeSound rel V E St ε)
    {h : Query k kN kS L → Out k e} {x : X} {π : M.NIProof} {Q : M.IOPQueries V x}
    {D : ODB k kN kS L e} (hv : M.Accepts h x π Q) (hrec : RecordsQueries D h x π Q) :
    D ∈ digestCollision ∨
      M.trans D ∈ M.toFullPast.extractsFullPast rel E x ∪ (M.toFullPast.badAny rel E St ∪ digestCollision) := by
  by_cases hD : D ∈ digestCollision
  · exact Or.inl hD
  · exact Or.inr (M.toFullPast.mem_of_verifyFullPast rel E St hrbr (M.transOracle D h) x π Q
      (accepts_transOracle hD hrec hv) (mem_trans_of_queries hD hrec))

end Prop812

end

end GordieHowe.SPBCS
