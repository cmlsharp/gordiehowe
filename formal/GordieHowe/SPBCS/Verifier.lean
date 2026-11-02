-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Basic
public import GordieHowe.SPBCS.Extraction.ChainProg

@[expose] public section

/-!
# The verifier's queries of the spBCS compiler

The compiled verifier of the spBCS compiler (`GordieHowe/SPBCS/Basic.lean`) as a classical
oracle program, for the base game of the knowledge argument. The verifier computes the chains of
the leaves and the final digests of the branches in the prover's step order (`Merges.Obs.rank`):
every step reads only steps of smaller rank (`Merges.Obs.rank_lt_of_reads`), so processing the
observers sorted by rank computes the chains and final digests of the proof.

* `leafProg`, `finalQuery`, `step`: the key and `xof` queries of a leaf's chain, the
  `transcript` query of a branch's final input, one step on a state of chains, final digests and
  `xof` answers.
* `obsOrder`: all observers sorted by rank; `roundsProg`: the steps in that order
  (`agrees_roundsProg`, `trace_roundsProg`: the chains, final digests and answers of the proof, and
  the honest queries of every observer).
* `treeProg`, `queryProg`, `queries`: then each tree's multiproof queries at the positions the
  query phase reads.
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm

variable {ι : Type} {t : SPTerm ι} {Mg : Merges t} {k kN kS L e : ℕ} {n : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (n j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] {X : Type}

section

variable (M : SPBCS Mg P X k kN kS L e)

/-! ### The steps -/

/-- The salted statement of a proof. -/
abbrev ssOf (x : X) (π : M.NIProof) : SaltedStatement kS X := ⟨π.salt, x⟩

/-- **The state of the verifier's steps**: the chains, the final digests and the `xof` answers of
each leaf's rounds. -/
structure RState where
  /-- The chain of each leaf. -/
  chains : M.Chains
  /-- The final digest of each branch. -/
  finals : Mg.Site → Digest k
  /-- The `xof` answers of each leaf's rounds. -/
  answers : t.Leaf → List (Out k e)

/-- **The `xof` answers of each leaf's rounds** in the proof. -/
def xofAnswers (h : Query k kN kS L → Out k e) (ss : SaltedStatement kS X) (wr : M.Writes)
    (p : t.Leaf) : List (Out k e) :=
  (M.comp p.label).answersWith (wr p) ss.salt h
    (M.key h ss (M.chains h ss wr) (M.finals h ss wr) p) (n p.label) le_rfl

variable (x : X) (π : M.NIProof)

/-- **The key and `xof` queries of leaf `p`'s chain** at the chains `chs` and the final digests
`fs`. -/
def leafProg (chs : M.Chains) (fs : Mg.Site → Digest k) (p : t.Leaf) :
    GordieHowe.OracleProg (Query k kN kS L) (Out k e) (M.Items p × List (Out k e)) :=
  (M.comp p.label).chainProg (π.writes p) π.salt
    (fun l => M.senc.encode (roundContent (M.ssOf x π) chs fs p l)) (n p.label) le_rfl

/-- **The `transcript` query of branch `s`'s final input** at the chains `chs` and the final
digests `fs`, returning the final digest. -/
def finalQuery (chs : M.Chains) (fs : Mg.Site → Digest k) (s : Mg.Site) :
    GordieHowe.OracleProg (Query k kN kS L) (Out k e) (Digest k) :=
  .query (.transcript (M.senc.encode (finalContent (M.ssOf x π) chs fs s))) fun a => .pure a.digest

/-- **One step**: the queries of an observer at the state, recording its result. -/
def step : Mg.Obs → M.RState → GordieHowe.OracleProg (Query k kN kS L) (Out k e) M.RState
  | .leaf p, st => (M.leafProg x π st.chains st.finals p).bind fun r =>
      .pure { st with chains := Function.update st.chains p r.1,
                      answers := Function.update st.answers p r.2 }
  | .sink s, st => (M.finalQuery x π st.chains st.finals s).bind fun d =>
      .pure { st with finals := Function.update st.finals s d }

/-- **The steps of a list of observers**, in order. -/
def process : List Mg.Obs → M.RState → GordieHowe.OracleProg (Query k kN kS L) (Out k e) M.RState
  | [], st => .pure st
  | o :: l, st => (M.step x π o st).bind fun st' => process l st'

variable (Mg) in
/-- **All observers sorted by rank** (the prover's step order). -/
def obsOrder : List Mg.Obs :=
  (t.leaves.map Merges.Obs.leaf ++ (Encodable.sortedUniv Mg.Site).map Merges.Obs.sink).mergeSort
    fun a b => decide (a.rank ≤ b.rank)

/-- The initial state. -/
def initState : M.RState := ⟨fun _ => [], 0, fun _ => []⟩

/-- **The key, `xof` and final-input queries of the verifier** (module docstring). -/
def roundsProg : GordieHowe.OracleProg (Query k kN kS L) (Out k e) M.RState :=
  M.process x π (obsOrder Mg) M.initState

/-! ### Running the steps -/

section Run

variable (h : Query k kN kS L → Out k e)

/-- **The state agrees with the proof at an observer**: a leaf's chain and answers, a branch's
final digest. -/
def Agrees (st : M.RState) : Mg.Obs → Prop
  | .leaf p => st.chains p = M.chains h (M.ssOf x π) π.writes p ∧
      st.answers p = M.xofAnswers h (M.ssOf x π) π.writes p
  | .sink s => st.finals s = M.finals h (M.ssOf x π) π.writes s

/-- **The queries of the proof at an observer.** -/
def honestTrace : Mg.Obs → List (Query k kN kS L)
  | .leaf p => (M.leafProg x π (M.chains h (M.ssOf x π) π.writes)
      (M.finals h (M.ssOf x π) π.writes) p).trace h
  | .sink s => [.transcript (M.senc.encode (finalContent (M.ssOf x π)
      (M.chains h (M.ssOf x π) π.writes) (M.finals h (M.ssOf x π) π.writes) s))]

variable {M x π h}

theorem agrees_chains {st : M.RState} {o : Mg.Obs} (hr : ∀ o', o.Reads o' → M.Agrees x π h st o')
    {q : t.Leaf} (hq : o.Visible q) : st.chains q = M.chains h (M.ssOf x π) π.writes q :=
  (hr (.leaf q) (Merges.Obs.reads_leaf.2 hq.1)).1

theorem agrees_finals {st : M.RState} {o : Mg.Obs} (hr : ∀ o', o.Reads o' → M.Agrees x π h st o')
    {s : Mg.Site} (hs : Mg.Hides s o) : st.finals s = M.finals h (M.ssOf x π) π.writes s :=
  hr (.sink s) (Merges.Obs.reads_sink.2 hs)

theorem leafProg_eq {st : M.RState} {p : t.Leaf}
    (hr : ∀ o', (Merges.Obs.leaf p : Mg.Obs).Reads o' → M.Agrees x π h st o') :
    M.leafProg x π st.chains st.finals p = M.leafProg x π (M.chains h (M.ssOf x π) π.writes)
      (M.finals h (M.ssOf x π) π.writes) p := by
  unfold leafProg
  congr 1
  funext l
  rw [roundContent_congr (fun q hq => agrees_chains hr hq) (fun s hs => agrees_finals hr hs)]

theorem finalQuery_eq {st : M.RState} {s : Mg.Site}
    (hr : ∀ o', (Merges.Obs.sink s : Mg.Obs).Reads o' → M.Agrees x π h st o') :
    M.finalQuery x π st.chains st.finals s = M.finalQuery x π (M.chains h (M.ssOf x π) π.writes)
      (M.finals h (M.ssOf x π) π.writes) s := by
  unfold finalQuery
  rw [finalContent_congr (fun q hq => agrees_chains hr hq) (fun s' hs => agrees_finals hr hs)]

variable (M x π h) in
/-- **The run of a leaf's chain program at the proof**: its chain and answers. -/
theorem run_leafProg (p : t.Leaf) :
    (M.leafProg x π (M.chains h (M.ssOf x π) π.writes) (M.finals h (M.ssOf x π) π.writes) p).run h =
      (M.chains h (M.ssOf x π) π.writes p, M.xofAnswers h (M.ssOf x π) π.writes p) := by
  rw [leafProg, ComponentModel.run_chainProg, chains_eq_chainWith]
  rfl

variable (M x π h) in
/-- **The run of a final query at the proof**: the final digest. -/
theorem run_finalQuery (s : Mg.Site) :
    (M.finalQuery x π (M.chains h (M.ssOf x π) π.writes) (M.finals h (M.ssOf x π) π.writes) s).run h =
      M.finals h (M.ssOf x π) π.writes s :=
  (finals_eq π.writes s).symm

/-- **A step at a state agreeing on what the observer reads** records the proof's value at the
observer, keeps the state elsewhere, and makes the observer's honest queries. -/
theorem step_spec {st : M.RState} {o : Mg.Obs} (hr : ∀ o', o.Reads o' → M.Agrees x π h st o') :
    M.Agrees x π h ((M.step x π o st).run h) o ∧
      (∀ o', o' ≠ o → M.Agrees x π h st o' → M.Agrees x π h ((M.step x π o st).run h) o') ∧
      (M.step x π o st).trace h = M.honestTrace x π h o := by
  cases o with
  | leaf p =>
    simp only [step, GordieHowe.OracleProg.run_bind, GordieHowe.OracleProg.run_pure,
      GordieHowe.OracleProg.trace_bind, GordieHowe.OracleProg.trace_pure, List.append_nil]
    rw [leafProg_eq hr, run_leafProg]
    refine ⟨⟨Function.update_self .., Function.update_self ..⟩, fun o' hne ha => ?_, rfl⟩
    cases o' with
    | leaf q =>
      have hq : q ≠ p := fun e => hne (e ▸ rfl)
      exact ⟨(Function.update_of_ne hq _ _).trans ha.1, (Function.update_of_ne hq _ _).trans ha.2⟩
    | sink s => exact ha
  | sink s =>
    simp only [step, GordieHowe.OracleProg.run_bind, GordieHowe.OracleProg.run_pure,
      GordieHowe.OracleProg.trace_bind, GordieHowe.OracleProg.trace_pure, List.append_nil]
    rw [finalQuery_eq hr, run_finalQuery]
    refine ⟨Function.update_self .., fun o' hne ha => ?_, rfl⟩
    cases o' with
    | leaf q => exact ha
    | sink s' =>
      have hs : s' ≠ s := fun e => hne (e ▸ rfl)
      exact (Function.update_of_ne hs _ _).trans ha

/-- **The steps of a list sorted by rank** from a state agreeing off the list: the final state
agrees everywhere, and the queries are the honest queries of the list. -/
theorem process_spec : ∀ (l : List Mg.Obs) (st : M.RState),
    l.Pairwise (fun a b => decide (a.rank ≤ b.rank) = true) →
    (∀ o, o ∉ l → M.Agrees x π h st o) →
    (∀ o, M.Agrees x π h ((M.process x π l st).run h) o) ∧
      (M.process x π l st).trace h = l.flatMap (M.honestTrace x π h)
  | [], st, _, hst => ⟨fun o => hst o List.not_mem_nil, rfl⟩
  | o :: l, st, hl, hst => by
    rw [List.pairwise_cons] at hl
    have hr : ∀ o', o.Reads o' → M.Agrees x π h st o' := fun o' ho' => by
      refine hst o' fun hm => ?_
      have hlt := Merges.Obs.rank_lt_of_reads ho'
      rcases List.mem_cons.1 hm with rfl | hm
      · exact absurd hlt (lt_irrefl _)
      · have := hl.1 o' hm
        simp only [decide_eq_true_eq] at this
        omega
    obtain ⟨h1, h2, h3⟩ := step_spec hr
    obtain ⟨ih1, ih2⟩ := process_spec l ((M.step x π o st).run h) hl.2 fun o' ho' => by
      by_cases he : o' = o
      · exact he ▸ h1
      · exact h2 o' he (hst o' fun hm => (List.mem_cons.1 hm).elim he ho')
    refine ⟨fun o' => ?_, ?_⟩
    · simp only [process, GordieHowe.OracleProg.run_bind]
      exact ih1 o'
    · simp only [process, GordieHowe.OracleProg.trace_bind, List.flatMap_cons]
      rw [h3, ih2]

theorem mem_obsOrder (o : Mg.Obs) : o ∈ obsOrder Mg := by
  rw [obsOrder, List.mem_mergeSort]
  cases o with
  | leaf p => exact List.mem_append_left _ (List.mem_map_of_mem (SPTerm.mem_leaves p))
  | sink s => exact List.mem_append_right _ (List.mem_map_of_mem (Encodable.mem_sortedUniv s))

theorem pairwise_obsOrder :
    (obsOrder Mg).Pairwise (fun a b => decide (a.rank ≤ b.rank) = true) :=
  List.pairwise_mergeSort (fun a b c hab hbc => by
      simp only [decide_eq_true_eq] at hab hbc ⊢
      omega)
    (fun a b => by
      by_cases hab : a.rank ≤ b.rank
      · simp [hab]
      · simp only [decide_eq_true_eq, Bool.or_eq_true]
        omega) _

variable (M x π h) in
/-- **The rounds program computes the proof**: its final state agrees with the chains, the final
digests and the answers of the proof at every observer. -/
theorem agrees_roundsProg (o : Mg.Obs) : M.Agrees x π h ((M.roundsProg x π).run h) o :=
  (process_spec _ _ pairwise_obsOrder fun o' ho' => absurd (mem_obsOrder o') ho').1 o

variable (M x π h) in
/-- **The queries of the rounds program** are the honest queries of every observer in rank
order. -/
theorem trace_roundsProg :
    (M.roundsProg x π).trace h = (obsOrder Mg).flatMap (M.honestTrace x π h) :=
  (process_spec _ _ pairwise_obsOrder fun o' ho' => absurd (mem_obsOrder o') ho').2

variable (M x π h) in
theorem chains_roundsProg :
    ((M.roundsProg x π).run h).chains = M.chains h (M.ssOf x π) π.writes :=
  funext fun p => (agrees_roundsProg M x π h (.leaf p)).1

variable (M x π h) in
theorem answers_roundsProg :
    ((M.roundsProg x π).run h).answers = M.xofAnswers h (M.ssOf x π) π.writes :=
  funext fun p => (agrees_roundsProg M x π h (.leaf p)).2

variable (M x π h) in
/-- **A query of the rounds program** is an honest query of some observer. -/
theorem mem_roundsProg_iff {q : Query k kN kS L} :
    q ∈ (M.roundsProg x π).trace h ↔ ∃ o, q ∈ M.honestTrace x π h o := by
  rw [trace_roundsProg, List.mem_flatMap]
  exact ⟨fun ⟨o, _, hq⟩ => ⟨o, hq⟩, fun ⟨o, hq⟩ => ⟨o, mem_obsOrder o, hq⟩⟩

variable (M x π h) in
/-- **Every branch's final input of the proof** is a verifier query. -/
theorem mem_roundsProg_final (s : Mg.Site) :
    Query.transcript (M.senc.encode (finalContent (M.ssOf x π) (M.chains h (M.ssOf x π) π.writes)
      (M.finals h (M.ssOf x π) π.writes) s)) ∈ (M.roundsProg x π).trace h :=
  (mem_roundsProg_iff M x π h).2 ⟨.sink s, List.mem_singleton_self _⟩

variable (M x π h) in
/-- **The input and the point of every round of every leaf** are verifier queries. -/
theorem mem_roundsProg_input (p : t.Leaf) (r : ℕ) (hr : r < n p.label) :
    Query.transcript (M.senc.encode (roundContent (M.ssOf x π) (M.chains h (M.ssOf x π) π.writes)
        (M.finals h (M.ssOf x π) π.writes) p
        ((M.comp p.label).chainWith (π.writes p)
          (M.key h (M.ssOf x π) (M.chains h (M.ssOf x π) π.writes) (M.finals h (M.ssOf x π) π.writes) p)
          π.salt h r hr.le))) ∈ (M.roundsProg x π).trace h ∧
      Query.xof (M.key h (M.ssOf x π) (M.chains h (M.ssOf x π) π.writes)
        (M.finals h (M.ssOf x π) π.writes) p
        ((M.comp p.label).chainWith (π.writes p)
          (M.key h (M.ssOf x π) (M.chains h (M.ssOf x π) π.writes) (M.finals h (M.ssOf x π) π.writes) p)
          π.salt h r hr.le)) π.salt ∈ (M.roundsProg x π).trace h := by
  obtain ⟨h1, h2⟩ := ComponentModel.mem_trace_chainProg (M.comp p.label) (π.writes p) π.salt
    (fun l => M.senc.encode (roundContent (M.ssOf x π) (M.chains h (M.ssOf x π) π.writes)
      (M.finals h (M.ssOf x π) π.writes) p l)) h _ le_rfl r hr
  exact ⟨(mem_roundsProg_iff M x π h).2 ⟨.leaf p, h1⟩, (mem_roundsProg_iff M x π h).2 ⟨.leaf p, h2⟩⟩

variable (M x π h) in
/-- **The rounds program makes two queries per round of every leaf and one per branch.** -/
theorem length_trace_roundsProg :
    ((M.roundsProg x π).trace h).length = 2 * ∑ q : t.Leaf, n q.label + Fintype.card Mg.Site := by
  classical
  have hlen : ∀ o, (M.honestTrace x π h o).length =
      match o with
      | .leaf p => 2 * n p.label
      | .sink _ => 1 := fun o => by
    cases o with
    | leaf p => exact ComponentModel.length_trace_chainProg _ _ _ _ h _ _
    | sink s => rfl
  rw [trace_roundsProg, List.length_flatMap, obsOrder,
    ((List.mergeSort_perm _ _).map _).sum_eq, List.map_append, List.sum_append, List.map_map,
    List.map_map]
  simp only [Function.comp_def, hlen]
  rw [List.map_const', List.sum_replicate, Encodable.length_sortedUniv,
    smul_eq_mul, mul_one, ← List.sum_toFinset _ (SPTerm.nodup_leaves t)]
  have hF : t.leaves.toFinset = Finset.univ := Finset.eq_univ_of_forall fun p =>
    List.mem_toFinset.2 (SPTerm.mem_leaves p)
  rw [hF, Finset.mul_sum]

end Run

/-! ### The verifier's queries -/

section Queries

/-- The challenges read from the `xof` answers of each leaf's rounds. -/
def chVOfAns (ans : t.Leaf → List (Out k e)) : Chs P t := fun c =>
  (((ans c.leaf)[c.idx.1.1]?).bind fun s =>
    ((M.comp c.leaf.label).sampler c.idx).sample s.stream).getD
      ((M.comp c.leaf.label).sampler c.idx).default

/-- **The challenge of a leaf read from its `xof` answers.** -/
theorem chal_eq_xofAnswers (h : Query k kN kS L → Out k e) (ss : SaltedStatement kS X)
    (wr : M.Writes) (c : ChIdx P t) :
    M.chal h ss wr c = ((M.xofAnswers h ss wr c.leaf)[c.idx.1.1]?).bind
      fun s => ((M.comp c.leaf.label).sampler c.idx).sample s.stream := by
  rw [chal, ComponentModel.chalWith_eq_answers]
  rfl

/-- **The challenges read from the answers of the proof are its challenges.** -/
theorem chVOfAns_xofAnswers [∀ j i, Nonempty ((P j).Challenge i)] (h : Query k kN kS L → Out k e)
    (ss : SaltedStatement kS X) (wr : M.Writes) : M.chVOfAns (M.xofAnswers h ss wr) = M.chV h ss wr := by
  funext c
  simp only [chVOfAns, chV, chal_eq_xofAnswers]

/-- **The opening program of tree `τ`** (`MerkleFormat.treeProg`) at the positions `ps` and the
leaves of `π`. -/
def treeProg (π : M.NIProof) (ps : List M.Pos) (τ : M.Tree) :
    GordieHowe.OracleProg (Query k kN kS L) (Out k e) (Option (Digest k)) :=
  M.opening.treeProg ((M.comp τ.leaf.label).nLeaves τ.tree.msg τ.tree.tree)
    ((M.openedIn τ ps π.leaves).map Prod.fst) ((M.openedIn τ ps π.leaves).map Prod.snd) (π.paths τ)

variable [∀ j i, Nonempty ((P j).Challenge i)] (x : X) (π : M.NIProof)

/-- **The verifier's queries as a classical oracle program**: the rounds program, then each
tree's multiproof queries at the positions the query phase reads. -/
def queryProg {V : X → FullTr P t → Bool} (Q : M.IOPQueries V x) :
    GordieHowe.OracleProg (Query k kN kS L) (Out k e) Unit :=
  (M.roundsProg x π).bind fun st =>
    GordieHowe.OracleProg.forEach (M.trees (Q.pos st.chains (M.chVOfAns st.answers))) fun τ =>
      M.treeProg π (Q.pos st.chains (M.chVOfAns st.answers)) τ

/-- **The oracle queries of the spBCS verifier**: the trace of `queryProg`. -/
noncomputable def queries (h : Query k kN kS L → Out k e) {V : X → FullTr P t → Bool}
    (Q : M.IOPQueries V x) : List (Query k kN kS L) :=
  (M.queryProg x π Q).trace h

theorem queries_eq (h : Query k kN kS L → Out k e) {V : X → FullTr P t → Bool}
    (Q : M.IOPQueries V x) : M.queries x π h Q = (M.roundsProg x π).trace h ++
    (M.trees (Q.pos (M.chains h (M.ssOf x π) π.writes) (M.chV h (M.ssOf x π) π.writes))).flatMap
      fun τ => (M.treeProg π (Q.pos (M.chains h (M.ssOf x π) π.writes)
        (M.chV h (M.ssOf x π) π.writes)) τ).trace h := by
  rw [queries, queryProg, GordieHowe.OracleProg.trace_bind, chains_roundsProg, answers_roundsProg,
    GordieHowe.OracleProg.trace_forEach, chVOfAns_xofAnswers]

end Queries

end

end GordieHowe.SPBCS
