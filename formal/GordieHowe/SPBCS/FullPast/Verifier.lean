-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.FullPast.Stability
public import GordieHowe.SPBCS.Extraction.Transcript
public import GordieHowe.Model.QROM.Lifting
public import GordieHowe.Model.QROM.Expansion

@[expose] public section

/-!
# The verifier's queries, the base game and Proposition 8.12 for compositions

The verifier of the series–parallel base model (`GordieHowe.SPBCS.FullPast`).

* `roundsProgFullPast`: the verifier's key and `xof` queries as a classical oracle program, the rounds of
  all leaves in term order (global round `g` is round `g - p.off` of the leaf `p` it lies in);
  each leaf's chain input reads the chains of the leaves before it, which are complete by then
  (`run_roundsProgFullPast_fst`, `run_roundsProgFullPast_snd`). `queryProgFullPast` adds each tree's opening queries;
  `queriesFullPast` is its trace.
* CMS19's base game (Definition 8.1, p. 39) is the spBCS compiler's (`GordieHowe.SPBCS.game`,
  `GordieHowe/SPBCS/Knowledge.lean`, with `GordieHowe.SPBCS.mem_game_of_verify`, Proposition 8.11, p. 42).
* `dbExtract`: the database extractor at a statement: for each recorded salt and each recorded
  `transcript` input that decodes to the salt, the statement and the content of a challenge's
  causal past, the causal extractor on the past read from `D`.
* `mem_of_verifyFullPast` (Proposition 8.12, p. 42, knowledge form, p. 44; at the base game,
  `GordieHowe.SPBCS.mem_of_game`): a database recording the verifier's queries on an accepted proof has a
  digest collision, extracts a witness, or is in `badAny`. The flip comes from
  `CausalRBR.exists_flip` on the composite transcript read from the database.
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm
open scoped ENNReal NNReal

variable {k kN kS L e : ℕ}

namespace Base

variable {ι : Type} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)] {t : SPTerm ι}
  {X : Type} (M : Base P t X k kN kS L e)

/-! ### The verifier's queries as a classical program -/

section Program

variable (x : X) (π : M.NIProof)

variable [∀ j i, Nonempty ((P j).Challenge i)]

/-- The opening program of tree `τ` (`MerkleFormat.treeProg`) at the positions `ps` and the
leaves of `π`. -/
def treeProg (ps : List M.Pos) (τ : M.Tree) :
    GordieHowe.OracleProg (Query k kN kS L) (Out k e) (Option (Digest k)) :=
  M.opening.treeProg ((M.comp τ.leaf.label).nLeaves τ.tree.msg τ.tree.tree)
    ((M.openedIn τ ps π.leaves).map Prod.fst) ((M.openedIn τ ps π.leaves).map Prod.snd) (π.paths τ)

end Program

/-! ### The run of the rounds program -/

section Run

variable (h : Query k kN kS L → Out k e) (x : X) (π : M.NIProof)

omit [∀ j i, DecidableEq ((P j).Challenge i)] in
/-- A global round in the range of leaf `q`'s rounds is a round of `q`. -/
theorem leaf_eq_of_slots {g : ℕ} {s : SPTerm.Slot n t} (hs : (t.slots n)[g]? = some s) {q : t.Leaf}
    (h1 : q.off n ≤ g) (h2 : g < q.off n + n q.label) : q = s.leaf := by
  have := slots_getElem n q ⟨g - q.off n, by omega⟩
  rw [show q.off n + (⟨g - q.off n, by omega⟩ : Fin (n q.label)).1 = g by simp; omega, hs] at this
  exact (congrArg Slot.leaf (Option.some_inj.1 this)).symm

end Run

/-! ### Extraction reads off prefixes -/

/-- **An extraction of a chain at `m` rounds restricts to `r ≤ m` rounds.** -/
theorem extLeaf_of_le (D : ODB k kN kS L e) (x : X) (σ : FiatShamirSalt kS)
    (chs : (r : t.Leaf) → M.Items r) (q : t.Leaf) (l : M.Items q) {m : ℕ} (hm : m ≤ n q.label)
    {tr : (P q.label).Transcript ⟨m, by omega⟩} (h : M.extLeaf D x σ chs q l m hm = some tr)
    (r : ℕ) (hr : r ≤ m) :
    M.extLeaf D x σ chs q l r (hr.trans hm) = some (tr.take ⟨r, by omega⟩ hr) := by
  have hsteps := M.step_of_extLeaf D x σ chs q l m hm h
  have hall : ∀ j (hj : j < r), (M.step D x σ chs q l j (by omega)).isSome := fun j hj => by
    rw [hsteps j (by omega)]
    rfl
  have hstep_r : ∀ j (hj : j < n q.label), j < r → (M.step D x σ chs q l j hj).isSome :=
    fun j hj hjr => hall j hjr
  obtain ⟨tr', htr'⟩ : ∃ tr', M.extLeaf D x σ chs q l r (hr.trans hm) = some tr' := by
    suffices H : ∀ r' (hr' : r' ≤ r), (M.extLeaf D x σ chs q l r' (hr'.trans (hr.trans hm))).isSome from
      Option.isSome_iff_exists.1 (H r le_rfl)
    intro r'
    induction r' with
    | zero => intro _; rfl
    | succ r' ih =>
      intro hr'
      obtain ⟨tr₀, h₀⟩ := Option.isSome_iff_exists.1 (ih (by omega))
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (hall r' (by omega))
      rw [extLeaf_succ, h₀, Option.bind_some, hv, Option.map_some]
      rfl
  rw [htr']
  congr 1
  funext i
  have h1 := M.step_of_extLeaf D x σ chs q l r (hr.trans hm) htr' i.1 i.2
  have h2 := hsteps i.1 (by have hi : i.1 < r := i.2; omega)
  exact Option.some_inj.1 (h1.symm.trans h2)

/-! ### The verifier's queries -/

section Queries

variable (h : Query k kN kS L → Out k e) (x : X) (π : M.NIProof)

variable [∀ j i, Nonempty ((P j).Challenge i)]

variable {V : X → FullTr P t → Bool} (Q : M.IOPQueries V x)

omit [∀ j i, Nonempty ((P j).Challenge i)] in
theorem mem_trees {ps : List M.Pos} {q : M.Pos} (hq : q ∈ ps) : q.treeOf ∈ M.trees ps :=
  List.mem_dedup.2 (List.mem_map.2 ⟨q, hq, rfl⟩)

omit [∀ j i, Nonempty ((P j).Challenge i)] in
theorem mem_openedIn {ps : List M.Pos} {as : List (MerkleLeaf kN L)} {q : M.Pos}
    {a : MerkleLeaf kN L} (hqa : (q, a) ∈ ps.zip as) :
    (q.pos.leaf.1, a) ∈ M.openedIn q.treeOf ps as :=
  List.mem_filterMap.2 ⟨(q, a), hqa, by simp⟩

end Queries

/-! ### The database extractor -/

section Extractor

variable {Wit : Type} (rel : Set (X × Wit)) (E : CausalExtractor P t X Wit)

/-- The challenge at round `r` of leaf `p`, if `r` is a challenge round. -/
def chAt (p : t.Leaf) (r : ℕ) : Option (P p.label).ChallengeIdx :=
  if h : r < n p.label then
    if hd : (P p.label).dir ⟨r, h⟩ = .P_to_V then none else some ((P p.label).chIdx ⟨r, h⟩ hd)
  else none

omit [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)] in
theorem chAt_idx (c : ChIdx P t) : chAt c.leaf c.idx.1.1 = some c.idx := by
  have hd : ¬ (P c.leaf.label).dir c.idx.1 = .P_to_V := by simp [c.idx.2]
  simp only [chAt, c.idx.1.2, ↓reduceDIte, hd]
  rfl

/-- The witness the causal extractor reads at the statement `x` and the salt `σ` from one
recorded query: for a `transcript` input that decodes to `σ`, `x` and the content of a chain
input whose own items end before a challenge round, the extractor on the causal past read from
`D`. -/
def candidate [DecidableEq X] (x : X) (D : ODB k kN kS L e) (σ : FiatShamirSalt kS) :
    Query k kN kS L → Option Wit
  | .transcript b => (M.enc.decode b).bind fun xc =>
      if xc.1 = ⟨σ, x⟩ then (chAt xc.2.leaf xc.2.own.length).bind fun i =>
        (M.extPast D x σ xc.2.chains ⟨xc.2.leaf, i⟩ xc.2.own).map (E ⟨xc.2.leaf, i⟩ x)
      else none
  | _ => none

/-- **The database extractor at the statement `x`** (`LExtract` with the causal extractor `E`,
CMS19 section 8.5.2, p. 44): for each salt of a recorded `xof` query, the witnesses `E` reads at
that salt from the recorded `transcript` inputs of `D` that decode to `x` and the content of a
challenge's causal past.

Running time, in the database size `|D|`, the input length `L`, the number of leaves and their
rounds: one scan of the keys for the recorded salts (at most `|D|`); for each salt and each key,
one run of `enc.decode` on at most `L` bytes (for `CausalEncoding.bytes`, the decoder of the
statement codec, then at most one label comparison and one item parse per item for each leaf),
then `extPast`: at most `t.size n` calls of `step`, each two lookups and one encoding of a chain
input, or one Merkle view per tree of a round; then one call of `E` (polynomial by its own
Running time paragraph). In all `|D|²` decodes and extractions and `|D|²` calls of `E`.
This running time is argued here, not proved in Lean. -/
def dbExtract [DecidableEq X] (x : X) (D : ODB k kN kS L e) : Multiset Wit :=
  (recordedSalts D).bind fun σ => D.keys.val.filterMap (M.candidate E x D σ)

end Extractor

end Base

namespace FullPast

open Base

variable {ι : Type} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)] {t : SPTerm ι}
  {X : Type} (M : FullPast P t X k kN kS L e)

/-! ### The verifier's queries as a classical program -/

section Program

variable (x : X) (π : M.NIProof)

/-- Round `r` of leaf `p` from the `xof` answer `w` at its key: the write of `π`, or `w`'s
digest. -/
def itemOf (p : t.Leaf) (r : Fin (n p.label)) (w : Out k e) : Item k (M.comp p.label).W :=
  if hd : (P p.label).dir r = .P_to_V then .write ⟨⟨r, hd⟩, π.writes p ⟨r, hd⟩⟩
  else .absorb w.digest

/-- **The key and `xof` queries of the first `g` global rounds**, returning the chains so far
and the `xof` answers in order. -/
def roundsProgFullPast : ℕ → GordieHowe.OracleProg (Query k kN kS L) (Out k e)
    (((q : t.Leaf) → M.Items q) × List (Out k e))
  | 0 => .pure (fun _ => [], [])
  | g + 1 => (roundsProgFullPast g).bind fun st =>
      match (t.slots n)[g]? with
      | some s => .query (.transcript (M.inputAt x π.salt st.1 s.leaf (st.1 s.leaf))) fun v =>
          .query (.xof v.digest π.salt) fun w =>
            .pure (Function.update st.1 s.leaf (st.1 s.leaf ++ [M.itemOf π s.leaf s.round w]),
              st.2 ++ [w])
      | none => .pure st

variable [∀ j i, Nonempty ((P j).Challenge i)]

/-- The challenges derived from the `xof` answers `ws` in global round order. -/
def chVOf (ws : List (Out k e)) : Chs P t := fun c =>
  ((ws[gIdx c]?).bind fun w => ((M.comp c.leaf.label).sampler c.idx).sample w.stream).getD
    ((M.comp c.leaf.label).sampler c.idx).default

/-- **The verifier's queries as a classical oracle program**: the key and `xof` queries of all
global rounds, then each tree's opening queries at the positions the query phase reads. -/
noncomputable def queryProgFullPast {V : X → FullTr P t → Bool} (Q : M.IOPQueries V x) :
    GordieHowe.OracleProg (Query k kN kS L) (Out k e) Unit :=
  (M.roundsProgFullPast x π (t.size n)).bind fun st =>
    GordieHowe.OracleProg.forEach (M.trees (Q.pos st.1 (M.chVOf st.2))) fun τ =>
      M.treeProg π (Q.pos st.1 (M.chVOf st.2)) τ

/-- **The oracle queries of `V^h(x, π)`** (`BCSExpand`, CMS19 p. 39): the trace of `queryProgFullPast`. -/
noncomputable def queriesFullPast (h : Query k kN kS L → Out k e) {V : X → FullTr P t → Bool}
    (Q : M.IOPQueries V x) : List (Query k kN kS L) :=
  (M.queryProgFullPast x π Q).trace h

end Program

/-! ### The run of the rounds program -/

section Run

variable (h : Query k kN kS L → Out k e) (x : X) (π : M.NIProof)

/-- The first `r` items of leaf `p`'s verifier chain. -/
theorem take_chainsFullPast (p : t.Leaf) (r : ℕ) (hr : r ≤ n p.label) :
    (M.chainsFullPast h x π.salt π.writes p).take r =
      M.leafChainFullPast h x π.salt π.writes p (M.ctxOf h x π.salt π.writes p) r hr := by
  rw [chainsFullPast_eq]
  suffices H : ∀ m (hm : m ≤ n p.label) r (hr : r ≤ m),
      (M.leafChainFullPast h x π.salt π.writes p (M.ctxOf h x π.salt π.writes p) m hm).take r =
        M.leafChainFullPast h x π.salt π.writes p (M.ctxOf h x π.salt π.writes p) r (hr.trans hm) from
    H _ le_rfl r hr
  intro m
  induction m with
  | zero => intro _ r hr; obtain rfl : r = 0 := by omega
            rfl
  | succ m ih =>
    intro hm r hr
    rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hr) with hr' | rfl
    · rw [leafChainFullPast, List.take_append_of_le_length (by rw [length_leafChainFullPast]; omega),
        ih (by omega) r (by omega)]
    · rw [List.take_of_length_le (by rw [length_leafChainFullPast])]

/-- Item `r` of leaf `p`'s verifier chain is `itemOf` at the `xof` answer of its key. -/
theorem chainsFullPast_getElem? (p : t.Leaf) (r : Fin (n p.label)) :
    (M.chainsFullPast h x π.salt π.writes p)[r.1]? = some (M.itemOf π p r (h (.xof
      (M.keyFullPast h x π.salt p (M.ctxOf h x π.salt π.writes p)
        (M.leafChainFullPast h x π.salt π.writes p (M.ctxOf h x π.salt π.writes p) r r.2.le)) π.salt))) := by
  rw [chainsFullPast_eq, leafChainFullPast_getElem? M h x π.salt π.writes p _ _ le_rfl r.1 r.2]
  unfold itemAt itemOf
  split_ifs <;> rfl

/-- The verifier's chains truncated at the global round `g`. -/
def truncChains (g : ℕ) : (q : t.Leaf) → M.Items q :=
  fun (q : t.Leaf) => (M.chainsFullPast h x π.salt π.writes q).take (g - Leaf.off n q)

/-- **The run of `roundsProgFullPast`**: after `g ≤ t.size n` global rounds the chains are the
verifier's chains truncated at `g`. -/
theorem run_roundsProgFullPast_fst : ∀ g, g ≤ t.size n →
    ((M.roundsProgFullPast x π g).run h).1 = M.truncChains h x π g
  | 0, _ => by
    funext q
    simp [roundsProgFullPast, truncChains]
  | g + 1, hg => by
    obtain ⟨s, hs⟩ := exists_slots_getElem n (t := t) (g := g) (by omega)
    have hgs := eq_off_of_slots_getElem n hs
    have ih := run_roundsProgFullPast_fst g (by omega)
    rw [roundsProgFullPast, GordieHowe.OracleProg.run_bind]
    simp only [hs, GordieHowe.OracleProg.run_query, GordieHowe.OracleProg.run_pure]
    rw [ih]
    funext q
    by_cases hq : q = s.leaf
    · subst hq
      rw [Function.update_self, truncChains, truncChains,
        show g + 1 - s.leaf.off n = s.round + 1 by omega, show g - s.leaf.off n = s.round by omega,
        List.take_add_one, List.getElem?_eq_getElem (by
          rw [chainsFullPast_eq, length_leafChainFullPast]; exact s.round.2)]
      congr 2
      have hc := M.chainsFullPast_getElem? h x π s.leaf s.round
      rw [List.getElem?_eq_getElem (by rw [chainsFullPast_eq, length_leafChainFullPast]; exact s.round.2)] at hc
      rw [Option.some_inj.1 hc]
      have hctx : M.ctxOfChains s.leaf (M.truncChains h x π g) = M.ctxOf h x π.salt π.writes s.leaf := by
        funext r
        have := Leaf.Before.off_add_le n r.2
        show (M.chainsFullPast h x π.salt π.writes r.1).take (g - r.1.off n) = _
        rw [List.take_of_length_le (by rw [chainsFullPast_eq, length_leafChainFullPast]; omega)]
        rfl
      simp only [inputAt, keyFullPast, hctx]
      rw [M.take_chainsFullPast h x π s.leaf s.round s.round.2.le]
    · rw [Function.update_of_ne hq, truncChains, truncChains]
      have hlen := (show (M.chainsFullPast h x π.salt π.writes q).length = n q.label by
        rw [chainsFullPast_eq, length_leafChainFullPast])
      by_cases h1 : q.off n ≤ g
      · by_cases h2 : g < q.off n + n q.label
        · exact absurd (leaf_eq_of_slots hs h1 h2) hq
        · rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
      · rw [show g + 1 - q.off n = 0 by omega, show g - q.off n = 0 by omega]

/-- The `xof` answers of `roundsProgFullPast`: one per global round, at its key. -/
theorem run_roundsProgFullPast_snd : ∀ g, g ≤ t.size n →
    ((M.roundsProgFullPast x π g).run h).2.length = g ∧
      ∀ c : ChIdx P t, gIdx c < g → ((M.roundsProgFullPast x π g).run h).2[gIdx c]? =
        some (h (.xof (M.keyFullPast h x π.salt c.leaf (M.ctxOf h x π.salt π.writes c.leaf)
          (M.leafChainFullPast h x π.salt π.writes c.leaf (M.ctxOf h x π.salt π.writes c.leaf) c.idx.1
            c.idx.1.2.le)) π.salt))
  | 0, _ => ⟨rfl, fun c hc => absurd hc (Nat.not_lt_zero _)⟩
  | g + 1, hg => by
    obtain ⟨s, hs⟩ := exists_slots_getElem n (t := t) (g := g) (by omega)
    have hgs := eq_off_of_slots_getElem n hs
    obtain ⟨ihl, ih⟩ := run_roundsProgFullPast_snd g (by omega)
    have hfst := M.run_roundsProgFullPast_fst h x π g (by omega)
    rw [roundsProgFullPast, GordieHowe.OracleProg.run_bind]
    simp only [hs, GordieHowe.OracleProg.run_query, GordieHowe.OracleProg.run_pure]
    refine ⟨by simp [ihl], fun c hc => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc' | hc'
    · rw [List.getElem?_append_left (by omega), ih c hc']
    · rw [List.getElem?_append_right (by omega), show gIdx c - _ = 0 by omega]
      simp only [List.getElem?_singleton, ↓reduceIte]
      have hcs : (⟨c.leaf, c.idx.1⟩ : SPTerm.Slot n t) = s := by
        have := slots_getElem n c.leaf c.idx.1
        rw [show c.leaf.off n + (c.idx.1 : ℕ) = g from hc', hs] at this
        exact (Option.some_inj.1 this).symm
      subst hcs
      rw [hfst]
      have hcg : c.leaf.off n ≤ g := by unfold gIdx at hc'; omega
      have hctx : M.ctxOfChains c.leaf (M.truncChains h x π g) = M.ctxOf h x π.salt π.writes c.leaf := by
        funext r
        have := Leaf.Before.off_add_le n r.2
        show (M.chainsFullPast h x π.salt π.writes r.1).take (g - r.1.off n) = _
        rw [List.take_of_length_le (by rw [chainsFullPast_eq, length_leafChainFullPast]; omega)]
        rfl
      have hown : M.truncChains h x π g c.leaf =
          M.leafChainFullPast h x π.salt π.writes c.leaf (M.ctxOf h x π.salt π.writes c.leaf) c.idx.1
            c.idx.1.2.le := by
        rw [truncChains, show g - c.leaf.off n = c.idx.1.1 by unfold gIdx at hc'; omega, take_chainsFullPast]
      simp only [inputAt, keyFullPast, hctx, hown]

/-- **The key and `xof` queries of every challenge are queried by `roundsProgFullPast`.** -/
theorem mem_trace_roundsProgFullPast : ∀ g, g ≤ t.size n → ∀ c : ChIdx P t, gIdx c < g →
    Query.transcript (M.inputAt x π.salt (M.chainsFullPast h x π.salt π.writes) c.leaf
        (M.leafChainFullPast h x π.salt π.writes c.leaf (M.ctxOf h x π.salt π.writes c.leaf) c.idx.1
          c.idx.1.2.le)) ∈ (M.roundsProgFullPast x π g).trace h ∧
      Query.xof (M.keyFullPast h x π.salt c.leaf (M.ctxOf h x π.salt π.writes c.leaf)
        (M.leafChainFullPast h x π.salt π.writes c.leaf (M.ctxOf h x π.salt π.writes c.leaf) c.idx.1
          c.idx.1.2.le)) π.salt ∈ (M.roundsProgFullPast x π g).trace h
  | 0, _, c, hc => absurd hc (Nat.not_lt_zero _)
  | g + 1, hg, c, hc => by
    obtain ⟨s, hs⟩ := exists_slots_getElem n (t := t) (g := g) (by omega)
    have hfst := M.run_roundsProgFullPast_fst h x π g (by omega)
    rw [roundsProgFullPast, GordieHowe.OracleProg.trace_bind]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc' | hc'
    · obtain ⟨h1, h2⟩ := mem_trace_roundsProgFullPast g (by omega) c hc'
      exact ⟨List.mem_append_left _ h1, List.mem_append_left _ h2⟩
    · have hcs : (⟨c.leaf, c.idx.1⟩ : SPTerm.Slot n t) = s := by
        have := slots_getElem n c.leaf c.idx.1
        rw [show c.leaf.off n + (c.idx.1 : ℕ) = g from hc', hs] at this
        exact (Option.some_inj.1 this).symm
      subst hcs
      simp only [hs, GordieHowe.OracleProg.trace_query, GordieHowe.OracleProg.trace_pure]
      rw [hfst]
      have hcg : c.leaf.off n ≤ g := by unfold gIdx at hc'; omega
      have hctx : M.ctxOfChains c.leaf (M.truncChains h x π g) = M.ctxOf h x π.salt π.writes c.leaf := by
        funext r
        have := Leaf.Before.off_add_le n r.2
        show (M.chainsFullPast h x π.salt π.writes r.1).take (g - r.1.off n) = _
        rw [List.take_of_length_le (by rw [chainsFullPast_eq, length_leafChainFullPast]; omega)]
        rfl
      have hctx' : M.ctxOfChains c.leaf (M.chainsFullPast h x π.salt π.writes) =
          M.ctxOf h x π.salt π.writes c.leaf := rfl
      have hown : M.truncChains h x π g c.leaf =
          M.leafChainFullPast h x π.salt π.writes c.leaf (M.ctxOf h x π.salt π.writes c.leaf) c.idx.1
            c.idx.1.2.le := by
        rw [truncChains, show g - c.leaf.off n = c.idx.1.1 by unfold gIdx at hc'; omega, take_chainsFullPast]
      simp only [inputAt, keyFullPast, hctx, hctx', hown]
      exact ⟨List.mem_append_right _ (List.mem_cons_self), List.mem_append_right _
        (List.mem_cons_of_mem _ List.mem_cons_self)⟩

/-- The chain input queried at global round `g` is the verifier's chain input of that round. -/
theorem inputAt_truncChains {g : ℕ} {s : SPTerm.Slot n t} (hs : (t.slots n)[g]? = some s) :
    M.inputAt x π.salt (M.truncChains h x π g) s.leaf (M.truncChains h x π g s.leaf) =
      M.inputAt x π.salt (M.chainsFullPast h x π.salt π.writes) s.leaf
        (M.leafChainFullPast h x π.salt π.writes s.leaf (M.ctxOf h x π.salt π.writes s.leaf) s.round
          s.round.2.le) := by
  have hgs := eq_off_of_slots_getElem n hs
  have hctx : M.ctxOfChains s.leaf (M.truncChains h x π g) =
      M.ctxOfChains s.leaf (M.chainsFullPast h x π.salt π.writes) := by
    funext r
    have := Leaf.Before.off_add_le n r.2
    show (M.chainsFullPast h x π.salt π.writes r.1).take (g - r.1.off n) = _
    rw [List.take_of_length_le (by rw [chainsFullPast_eq, length_leafChainFullPast]; omega)]
    rfl
  have hown : M.truncChains h x π g s.leaf =
      M.leafChainFullPast h x π.salt π.writes s.leaf (M.ctxOf h x π.salt π.writes s.leaf) s.round
        s.round.2.le := by
    rw [truncChains, show g - s.leaf.off n = s.round by omega, take_chainsFullPast]
  simp only [inputAt, hctx, hown]

/-- **An `xof` query of `roundsProgFullPast` is the key query of a round**, whose chain input is also
queried. -/
theorem xof_mem_trace_roundsProgFullPast : ∀ g, g ≤ t.size n → ∀ {d : Digest k} {s : FiatShamirSalt kS},
    Query.xof d s ∈ (M.roundsProgFullPast x π g).trace h →
    ∃ (p : t.Leaf) (r : Fin (n p.label)), s = π.salt ∧
      d = M.keyFullPast h x π.salt p (M.ctxOf h x π.salt π.writes p)
        (M.leafChainFullPast h x π.salt π.writes p (M.ctxOf h x π.salt π.writes p) r r.2.le) ∧
      Query.transcript (M.inputAt x π.salt (M.chainsFullPast h x π.salt π.writes) p
        (M.leafChainFullPast h x π.salt π.writes p (M.ctxOf h x π.salt π.writes p) r r.2.le)) ∈
        (M.roundsProgFullPast x π g).trace h
  | 0, _, _, _, hq => by simp [roundsProgFullPast] at hq
  | g + 1, hg, d, σ', hq => by
    obtain ⟨sl, hs⟩ := exists_slots_getElem n (t := t) (g := g) (by omega)
    have hfst := M.run_roundsProgFullPast_fst h x π g (by omega)
    rw [roundsProgFullPast, GordieHowe.OracleProg.trace_bind] at hq ⊢
    simp only [hs, GordieHowe.OracleProg.trace_query, GordieHowe.OracleProg.trace_pure] at hq ⊢
    rw [hfst] at hq ⊢
    rcases List.mem_append.1 hq with hq | hq
    · obtain ⟨p, r, h1, h2, h3⟩ := xof_mem_trace_roundsProgFullPast g (by omega) hq
      exact ⟨p, r, h1, h2, List.mem_append_left _ h3⟩
    · simp only [List.mem_cons, reduceCtorEq, false_or, List.not_mem_nil, or_false] at hq
      obtain ⟨rfl, rfl⟩ := Query.xof.inj hq
      rw [M.inputAt_truncChains h x π hs]
      exact ⟨sl.leaf, sl.round, rfl, rfl, List.mem_append_right _ List.mem_cons_self⟩

/-- **A `transcript` query of `roundsProgFullPast` is the chain input of a round.** -/
theorem transcript_mem_trace_roundsProgFullPast : ∀ g, g ≤ t.size n → ∀ {b : Bytes L},
    Query.transcript b ∈ (M.roundsProgFullPast x π g).trace h →
    ∃ (p : t.Leaf) (r : Fin (n p.label)), b = M.inputAt x π.salt (M.chainsFullPast h x π.salt π.writes) p
      (M.leafChainFullPast h x π.salt π.writes p (M.ctxOf h x π.salt π.writes p) r r.2.le)
  | 0, _, _, hq => by simp [roundsProgFullPast] at hq
  | g + 1, hg, b, hq => by
    obtain ⟨sl, hs⟩ := exists_slots_getElem n (t := t) (g := g) (by omega)
    have hfst := M.run_roundsProgFullPast_fst h x π g (by omega)
    rw [roundsProgFullPast, GordieHowe.OracleProg.trace_bind] at hq
    simp only [hs, GordieHowe.OracleProg.trace_query, GordieHowe.OracleProg.trace_pure] at hq
    rw [hfst] at hq
    rcases List.mem_append.1 hq with hq | hq
    · exact transcript_mem_trace_roundsProgFullPast g (by omega) hq
    · simp only [List.mem_cons, reduceCtorEq, or_false, List.not_mem_nil] at hq
      obtain rfl := Query.transcript.inj hq
      exact ⟨sl.leaf, sl.round, M.inputAt_truncChains h x π hs⟩

/-- `roundsProgFullPast` makes only `transcript` and `xof` queries. -/
theorem isChainQuery_of_mem_trace_roundsProgFullPast : ∀ g, ∀ {q : Query k kN kS L},
    q ∈ (M.roundsProgFullPast x π g).trace h → (∃ b, q = .transcript b) ∨ ∃ d s, q = .xof d s
  | 0, _, hq => by simp [roundsProgFullPast] at hq
  | g + 1, q, hq => by
    rw [roundsProgFullPast, GordieHowe.OracleProg.trace_bind] at hq
    rcases List.mem_append.1 hq with hq | hq
    · exact isChainQuery_of_mem_trace_roundsProgFullPast g hq
    · revert hq
      split
      · simp only [GordieHowe.OracleProg.trace_query, GordieHowe.OracleProg.trace_pure, List.mem_cons,
          List.not_mem_nil, or_false]
        rintro (rfl | rfl)
        · exact Or.inl ⟨_, rfl⟩
        · exact Or.inr ⟨_, _, rfl⟩
      · simp [GordieHowe.OracleProg.trace_pure]

end Run

/-! ### The verifier's queries -/

section Queries

variable (h : Query k kN kS L → Out k e) (x : X) (π : M.NIProof)

theorem run_roundsProgFullPast_size :
    ((M.roundsProgFullPast x π (t.size n)).run h).1 = M.chainsFullPast h x π.salt π.writes := by
  rw [M.run_roundsProgFullPast_fst h x π _ le_rfl]
  funext q
  have := Leaf.off_add_le n q
  rw [truncChains, List.take_of_length_le (by rw [chainsFullPast_eq, length_leafChainFullPast]; omega)]

variable [∀ j i, Nonempty ((P j).Challenge i)]

theorem chVOf_run :
    M.chVOf ((M.roundsProgFullPast x π (t.size n)).run h).2 = M.chVFullPast h x π.salt π.writes := by
  funext c
  rw [chVOf, (M.run_roundsProgFullPast_snd h x π _ le_rfl).2 c (gIdx_lt_size c)]
  rfl

variable {V : X → FullTr P t → Bool} (Q : M.IOPQueries V x)

theorem queriesFullPast_eq :
    M.queriesFullPast x π h Q = (M.roundsProgFullPast x π (t.size n)).trace h ++
      (M.trees (Q.pos (M.chainsFullPast h x π.salt π.writes) (M.chVFullPast h x π.salt π.writes))).flatMap fun τ =>
        (M.treeProg π (Q.pos (M.chainsFullPast h x π.salt π.writes) (M.chVFullPast h x π.salt π.writes)) τ).trace h := by
  rw [queriesFullPast, queryProgFullPast, GordieHowe.OracleProg.trace_bind, run_roundsProgFullPast_size, chVOf_run,
    GordieHowe.OracleProg.trace_forEach]

/-- The chain input and the key query of every challenge are verifier queries. -/
theorem mem_queriesFullPast_challenge (c : ChIdx P t) :
    Query.transcript (M.inputAt x π.salt (M.chainsFullPast h x π.salt π.writes) c.leaf
        (M.leafChainFullPast h x π.salt π.writes c.leaf (M.ctxOf h x π.salt π.writes c.leaf) c.idx.1
          c.idx.1.2.le)) ∈ M.queriesFullPast x π h Q ∧
      Query.xof (M.keyFullPast h x π.salt c.leaf (M.ctxOf h x π.salt π.writes c.leaf)
        (M.leafChainFullPast h x π.salt π.writes c.leaf (M.ctxOf h x π.salt π.writes c.leaf) c.idx.1
          c.idx.1.2.le)) π.salt ∈ M.queriesFullPast x π h Q := by
  obtain ⟨h1, h2⟩ := M.mem_trace_roundsProgFullPast h x π _ le_rfl c (gIdx_lt_size c)
  rw [queriesFullPast_eq]
  exact ⟨List.mem_append_left _ h1, List.mem_append_left _ h2⟩

theorem mem_queriesFullPast_tree {τ : M.Tree}
    (hτ : τ ∈ M.trees (Q.pos (M.chainsFullPast h x π.salt π.writes) (M.chVFullPast h x π.salt π.writes))) {q : Query k kN kS L}
    (hq : q ∈ (M.treeProg π (Q.pos (M.chainsFullPast h x π.salt π.writes) (M.chVFullPast h x π.salt π.writes)) τ).trace h) :
    q ∈ M.queriesFullPast x π h Q := by
  rw [queriesFullPast_eq]
  exact List.mem_append_right _ (List.mem_flatMap.2 ⟨τ, hτ, hq⟩)

/-- The leaves of an accepted proof, at a database recording the verifier's queries without a
digest collision, are the extracted leaves at the queried positions. -/
theorem forall₂_leafAt {D : ODB k kN kS L e} (hcol : D ∉ digestCollision) (hv : AcceptsFullPast h x π Q)
    (hQ : ∀ q ∈ M.queriesFullPast x π h Q, D.lookup q = some (h q)) :
    List.Forall₂ (fun q a => ((M.comp q.leaf.label).views D q.pos.msg (π.writes q.leaf q.pos.msg)
        q.pos.tree).leaves q.pos.leaf = some a)
      (Q.pos (M.chainsFullPast h x π.salt π.writes) (M.chVFullPast h x π.salt π.writes)) π.leaves := by
  refine List.forall₂_iff_zip.2 ⟨hv.leaves_length, fun {q a} hqa => ?_⟩
  have hτ := M.mem_trees (List.of_mem_zip hqa).1
  set ps := Q.pos (M.chainsFullPast h x π.salt π.writes) (M.chVFullPast h x π.salt π.writes)
  have hmem : (q.pos.leaf.1, a) ∈ ((M.openedIn q.treeOf ps π.leaves).map Prod.fst).zip
      ((M.openedIn q.treeOf ps π.leaves).map Prod.snd) := by
    rw [← List.zip_of_prod rfl rfl]
    exact M.mem_openedIn hqa
  exact M.opening.leafAt_of_check hcol
    (fun q' hq' => hQ q' (M.mem_queriesFullPast_tree h x π Q hτ hq')) (hv.paths _ hτ) hmem q.pos.leaf.2

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- A prover round of the verifier's chain reads the write of `π` and the Merkle views at its
roots. -/
theorem stepFullPast_chainsFullPast_message (D : ODB k kN kS L e) (p : t.Leaf) (i : (P p.label).MessageIdx) :
    M.step D x π.salt (M.chainsFullPast h x π.salt π.writes) p (M.chainsFullPast h x π.salt π.writes p) i.1 i.1.2 =
      some ((M.comp p.label).msg i (π.writes p i) ((M.comp p.label).views D i (π.writes p i))) := by
  rw [Base.step_message, M.chainsFullPast_getElem?_message h x π.salt π.writes p i, Option.bind_some,
    (M.comp p.label).writeAt_write]
  rfl

/-- A challenge round of the verifier's chain, read from a database that answers the verifier's
queries as `h`, reads the verifier's challenge. -/
theorem stepFullPast_chainsFullPast_challenge {D : ODB k kN kS L e} (hv : AcceptsFullPast h x π Q)
    (hQ : ∀ q ∈ M.queriesFullPast x π h Q, D.lookup q = some (h q)) (c : ChIdx P t) :
    M.step D x π.salt (M.chainsFullPast h x π.salt π.writes) c.leaf (M.chainsFullPast h x π.salt π.writes c.leaf)
      c.idx.1 c.idx.1.2 = some (M.chVFullPast h x π.salt π.writes c) := by
  obtain ⟨hm1, hm2⟩ := M.mem_queriesFullPast_challenge h x π Q c
  have hd : ¬ (P c.leaf.label).dir c.idx.1 = .P_to_V := by simp [c.idx.2]
  have hget := M.chainsFullPast_getElem? h x π c.leaf c.idx.1
  rw [Base.step_challenge, hget, M.take_chainsFullPast h x π c.leaf c.idx.1 c.idx.1.2.le]
  simp only [itemOf, hd, ↓reduceDIte, Option.bind_some, Item.getAbsorb, Base.chal]
  rw [hQ _ hm1, Option.bind_some]
  rw [show (h (Query.transcript (M.inputAt x π.salt (M.chainsFullPast h x π.salt π.writes) c.leaf
    (M.leafChainFullPast h x π.salt π.writes c.leaf (M.ctxOf h x π.salt π.writes c.leaf) c.idx.1
      c.idx.1.2.le)))).digest = M.keyFullPast h x π.salt c.leaf (M.ctxOf h x π.salt π.writes c.leaf)
    (M.leafChainFullPast h x π.salt π.writes c.leaf (M.ctxOf h x π.salt π.writes c.leaf) c.idx.1
      c.idx.1.2.le) from rfl, hQ _ hm2, Option.bind_some, ite_eq_left rfl]
  obtain ⟨ch, hch⟩ := Option.isSome_iff_exists.1 (hv.sampled c)
  simp only [chalOf] at hch
  rw [hch]
  simp [chVFullPast, chalOf, hch]

end Queries

/-! ### The database extractor -/

section Extractor

variable {Wit : Type} (rel : Set (X × Wit)) (E : CausalExtractor P t X Wit)

/-- The databases from which the extractor succeeds at `x`. -/
def extractsFullPast [DecidableEq X] (x : X) : Set (ODB k kN kS L e) :=
  {D | ∃ w ∈ M.dbExtract E x D, (x, w) ∈ rel}

/-- **A recorded chain input from which a witness is extracted puts `D` in `extractsFullPast`.** -/
theorem mem_extractsFullPast_of [DecidableEq X] {x : X} {D : ODB k kN kS L e} {σ : FiatShamirSalt kS}
    {c : ChIdx P t} {chs : (r : t.Leaf) → M.Items r} {l : M.Items c.leaf} {past : CausalPast P c}
    (hσ : ∃ κ, Query.xof κ σ ∈ D) (hfull : M.ChainsFull chs c.leaf) (hl : l.length = c.idx.1)
    (hmem : Query.transcript (M.inputAt x σ chs c.leaf l) ∈ D)
    (hp : M.extPast D x σ chs c l = some past) (hrel : (x, E c x past) ∈ rel) :
    D ∈ M.extractsFullPast rel E x := by
  have hwf := M.wf_content_of_extPast hfull hl hp
  refine ⟨E c x past, Multiset.mem_bind.2 ⟨σ, mem_recordedSalts.2 hσ,
    (Multiset.mem_filterMap _ _).2 ⟨_, Finmap.mem_keys.2 hmem, ?_⟩⟩, hrel⟩
  have hagree : ∀ r, r.Before c.leaf → M.chainsOf (M.ctxOfChains c.leaf chs) r = chs r :=
    fun r hr => chainsOf_of_before M _ hr
  simp only [candidate, inputAt, M.enc.decode_encode _ _ hwf, Option.bind_some, ite_true]
  simp only [content]
  rw [hl, chAt_idx, Option.bind_some, M.extPast_congr D x σ hagree, hp, Option.map_some]

end Extractor

/-! ### Proposition 8.12 -/

section Prop812

variable [∀ j i, Nonempty ((P j).Challenge i)] {V : X → FullTr P t → Bool} {Wit : Type}
  (rel : Set (X × Wit)) (E : CausalExtractor P t X Wit) (S : CausalStateFn P t X)
  {ε : ChIdx P t → ℝ≥0}

/-- **CMS19 Proposition 8.12** (p. 42), knowledge form (p. 44), for the composite at one accepted
proof: a database that records the verifier's queries on an accepted proof `π` of `x` with the
answers of `h` has a digest collision, extracts a witness at `x`, or lies in `badAny`. The flip
comes from `CausalRBR.exists_flip` on the composite transcript read from `D`. -/
theorem mem_of_verifyFullPast [DecidableEq X] (hrbr : CausalRBRKnowledgeSound rel V E S ε)
    (h : Query k kN kS L → Out k e) (x : X) (π : M.NIProof) (Q : M.IOPQueries V x)
    {D : ODB k kN kS L e} (hv : AcceptsFullPast h x π Q)
    (hQ : ∀ q ∈ M.queriesFullPast x π h Q, D.lookup q = some (h q)) :
    D ∈ M.extractsFullPast rel E x ∪ (M.badAny rel E S ∪ digestCollision) := by
  by_cases hcol : D ∈ digestCollision
  · exact Or.inr (Or.inr hcol)
  set chs := M.chainsFullPast h x π.salt π.writes
  set ch := M.chVFullPast h x π.salt π.writes
  have hall : ∀ q (r : ℕ) (hr : r < n q.label), (M.step D x π.salt chs q (chs q) r hr).isSome := by
    intro q r hr
    by_cases hd : (P q.label).dir ⟨r, hr⟩ = .P_to_V
    · exact Option.isSome_iff_exists.2 ⟨_, M.stepFullPast_chainsFullPast_message h x π D q ⟨⟨r, hr⟩, hd⟩⟩
    · exact Option.isSome_iff_exists.2
        ⟨_, M.stepFullPast_chainsFullPast_challenge h x π Q hv hQ ⟨q, (P q.label).chIdx ⟨r, hr⟩ hd⟩⟩
  have hext : ∀ q, (M.extLeaf D x π.salt chs q (chs q) (n q.label) le_rfl).isSome := fun q =>
    M.extLeaf_isSome D x π.salt chs q (chs q) (hall q) _ le_rfl
  let trF : FullTr P t := fun q => (M.extLeaf D x π.salt chs q (chs q) (n q.label) le_rfl).get (hext q)
  have htrF : ∀ q, M.extLeaf D x π.salt chs q (chs q) (n q.label) le_rfl = some (trF q) := fun q => by
    simp [trF]
  have hsteps := fun q => M.step_of_extLeaf D x π.salt chs q (chs q) _ le_rfl (htrF q)
  have hchal : trF.challenges = ch := by
    funext c
    have h1 := hsteps c.leaf c.idx.1.1 c.idx.1.2
    rw [M.stepFullPast_chainsFullPast_challenge h x π Q hv hQ c] at h1
    exact (Option.some_inj.1 h1).symm
  have hacc : V x trF = true := by
    refine Q.accept_of_verdict chs ch
      (fun p i => (M.comp p.label).views D i (π.writes p i)) trF _ ?_ hchal ?_ hv.decides
    · intro p i w hw
      have h1 := hsteps p i.1.1 i.1.2
      rw [M.stepFullPast_chainsFullPast_message h x π D p i] at h1
      have hw' : w = π.writes p i := by
        have h2 := M.chainsFullPast_getElem?_message h x π.salt π.writes p i
        rw [hw] at h2
        exact eq_of_heq (Sigma.mk.inj (Item.write.inj (Option.some_inj.1 h2))).2
      subst hw'
      exact (Option.some_inj.1 h1).symm
    · exact M.forall₂_leafAt h x π Q hcol hv hQ
  have hfull : ∀ p, M.ChainsFull chs p := fun p q _ => by
    show (M.chainsFullPast h x π.salt π.writes q).length = _
    rw [chainsFullPast_eq, length_leafChainFullPast]
  -- the causal past of every challenge, read from `D`
  have hpast : ∀ c : ChIdx P t, M.extPast D x π.salt chs c
      ((chs c.leaf).take c.idx.1) = some (trF.past c) := by
    intro c
    have hctx : M.extCtx D x π.salt chs c.leaf = some (trF.ctx c.leaf) :=
      optAll_eq_some.2 fun q => htrF q.1
    rw [extPast, hctx, Option.bind_some, M.extLeaf_take D x π.salt chs c.leaf (chs c.leaf) _ _ le_rfl,
      M.extLeaf_of_le D x π.salt chs c.leaf (chs c.leaf) le_rfl (htrF c.leaf) _ c.idx.1.2.le,
      Option.map_some]
    rfl
  have hlen : ∀ c : ChIdx P t, ((chs c.leaf).take c.idx.1).length = c.idx.1.1 := fun c => by
    rw [List.length_take, show (chs c.leaf).length = n c.leaf.label by
      show (M.chainsFullPast h x π.salt π.writes c.leaf).length = _
      rw [chainsFullPast_eq, length_leafChainFullPast]]
    exact Nat.min_eq_left c.idx.1.2.le
  have hown : ∀ c : ChIdx P t, (chs c.leaf).take c.idx.1 =
      M.leafChainFullPast h x π.salt π.writes c.leaf (M.ctxOf h x π.salt π.writes c.leaf) c.idx.1
        c.idx.1.2.le := fun c => M.take_chainsFullPast h x π c.leaf c.idx.1 c.idx.1.2.le
  by_cases hE : ∃ c, (x, E c x (trF.past c)) ∈ rel
  · obtain ⟨c, hc⟩ := hE
    obtain ⟨hm1, hm2⟩ := M.mem_queriesFullPast_challenge h x π Q c
    refine Or.inl (M.mem_extractsFullPast_of rel E ⟨_, DB.mem_iff_lookup.2 ⟨_, hQ _ hm2⟩⟩ (hfull c.leaf)
      (hlen c) ?_ (hpast c) hc)
    rw [hown c]
    exact DB.mem_iff_lookup.2 ⟨_, hQ _ hm1⟩
  · push Not at hE
    obtain ⟨c, hflip⟩ := hrbr.exists_flip x trF hacc id hE
    obtain ⟨hm1, hm2⟩ := M.mem_queriesFullPast_challenge h x π Q c
    obtain ⟨s, hs⟩ := Option.isSome_iff_exists.1 (hv.sampled c)
    simp only [chalOf] at hs
    have hchc : ch c = s := by simp [ch, chVFullPast, chalOf, hs]
    refine Or.inr (Or.inl ⟨x, π.salt, c, chs, (chs c.leaf).take c.idx.1, trF.past c,
      h (.transcript (M.inputAt x π.salt chs c.leaf (M.leafChainFullPast h x π.salt π.writes c.leaf
        (M.ctxOf h x π.salt π.writes c.leaf) c.idx.1 c.idx.1.2.le))),
      h (.xof (M.keyFullPast h x π.salt c.leaf (M.ctxOf h x π.salt π.writes c.leaf)
        (M.leafChainFullPast h x π.salt π.writes c.leaf (M.ctxOf h x π.salt π.writes c.leaf) c.idx.1
          c.idx.1.2.le)) π.salt),
      trF.challenges c, hfull c.leaf, hlen c, hpast c, ?_, ?_, ?_, ⟨hE c, hflip⟩⟩)
    · rw [hown c]
      exact hQ _ hm1
    · exact hQ _ hm2
    · rw [hchal, hchc]
      exact hs

end Prop812

end FullPast

end GordieHowe.SPBCS
