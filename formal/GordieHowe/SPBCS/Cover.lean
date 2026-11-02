-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Verifier
public import GordieHowe.SPBCS.Stability
public import GordieHowe.SPBCS.Targeted

@[expose] public section

/-!
# An accepted spBCS proof and the database extractor (CMS19 Proposition 8.12)

A database `D` without a digest collision that records the spBCS verifier's queries on an accepted
proof with the answers of `h` records the proof's chains (`RecordsChains`): the chains are full
and hold the proof's writes, and at every challenge the chain input with merges (read from `D` by
`keyD`, with the final digests read from `D`, which are those of `h` since `D` records the final
inputs: `recordsChains_of_verify`) and the stream are recorded, and the sampler reads the
challenge from the stream. The transcript read from such chains is the transcript along the proof
(`RecordsChains.extPast_eq`), so the database extractor, or the targeted extractor, returns a
witness or `D` lies in `bad` (`mem_of_recordsChains`, `mem_of_recordsChains_targeted`; the flip
comes from `CausalRBR.exists_flip`). The proof's leaves are those of `D`'s views
(`openedAs_views_of_check`). `mem_of_verify`, `mem_of_verify_targeted`: CMS19 Proposition 8.12
(p. 42), knowledge form (p. 44), for the spBCS verifier.
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm
open scoped ENNReal NNReal

variable {ι : Type} {t : SPTerm ι} {Mg : Merges t} {k kN kS L e : ℕ} {n : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (n j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] {X : Type}

section

variable (M : SPBCS Mg P X k kN kS L e)

/-! ### Recorded queries -/

/-- `D` records `q` with the answer of `h`. -/
def Recorded (h : Query k kN kS L → Out k e) (D : ODB k kN kS L e) (q : Query k kN kS L) : Prop :=
  D.lookup q = some (h q)

variable (h : Query k kN kS L → Out k e) (ss : SaltedStatement kS X) (wr : M.Writes)

/-- **The database records each branch's final input of the proof** with the answer of `h`. -/
def RecordsFinals (D : ODB k kN kS L e) : Prop :=
  ∀ s, Recorded h D (.transcript (M.senc.encode
    (finalContent ss (M.chains h ss wr) (M.finals h ss wr) s)))

variable {M h ss wr} {D : ODB k kN kS L e}

/-- **The final content of a proof is well formed.** -/
theorem wf_finalContent_chains (s : Mg.Site) :
    (finalContent ss (M.chains h ss wr) (M.finals h ss wr) s).WF n fun j => chainWF (P j) :=
  wf_finalContent_of_sees ss _ fun q _ => ⟨chainWF_chains wr q, length_chains wr q⟩

/-- **The round content of a proof at a proper prefix is well formed.** -/
theorem wf_roundContent_chains (p : t.Leaf) {l : M.Items p} (hl : chainWF (P p.label) l)
    (hlen : l.length < n p.label) :
    (roundContent ss (M.chains h ss wr) (M.finals h ss wr) p l).WF n fun j => chainWF (P j) :=
  wf_roundContent_of_before ss _ (fun q _ => ⟨chainWF_chains wr q, length_chains wr q⟩) hl hlen

/-- **The final digests read from a database that records the proof's final inputs are the
proof's.** -/
theorem finalsD_chains (hr : M.RecordsFinals h ss wr D) :
    M.finalsD D ss (M.chains h ss wr) = M.finals h ss wr :=
  finalsWith_eq_of_agree fun s => by
    show (D.lookup (.transcript (M.senc.encode
      (finalContent ss (M.chains h ss wr) (M.finals h ss wr) s)))).getD defaultOut = _
    rw [hr s]
    rfl

/-- **The key read from a database that records the proof's final inputs and the chain input of a
round of `p`** is the recorded answer of `h` there. -/
theorem keyD_chains (hr : M.RecordsFinals h ss wr D) (p : t.Leaf) (l : M.Items p)
    (hin : Recorded h D (.transcript (M.senc.encode
      (roundContent ss (M.chains h ss wr) (M.finals h ss wr) p l)))) :
    M.keyD D ss (M.chains h ss wr) p l =
      some (h (.transcript (M.senc.encode
        (roundContent ss (M.chains h ss wr) (M.finals h ss wr) p l)))) := by
  have hrec : M.FinalsRecorded D ss (M.chains h ss wr) (.leaf p) := fun s _ => by
    unfold finalInputD
    rw [finalsD_chains hr]
    exact DB.mem_iff_lookup.2 ⟨_, hr s⟩
  unfold keyD inputD
  rw [ite_eq_left hrec, finalsD_chains hr]
  exact hin

end

/-! ### The database records the chains of an accepted proof -/

section Chains

variable {M : SPBCS Mg P X k kN kS L e} [∀ j i, Nonempty ((P j).Challenge i)]
  {h : Query k kN kS L → Out k e} {x : X} {π : M.NIProof} {V : X → FullTr P t → Bool}
  {Q : M.IOPQueries V x} {D : ODB k kN kS L e}

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

variable (M) in
/-- **The database `D` records the chains `chs` of the proof `π` of `x` at the challenges `ch`**:
every chain is full and holds `π`'s write at each prover round; at each challenge `c`, the chain
input of `c` (the chains `chs` and the items of `c`'s leaf before its round, with the final
digests read from `D`) is recorded with its final inputs, with an answer `a` (`keyD`), and the
stream at `a`'s digest and the salt with an answer `s`, whose digest is the item of `c`'s round and
from whose stream the sampler reads `ch c`. -/
structure RecordsChains (D : ODB k kN kS L e) (x : X) (π : M.NIProof) (chs : M.Chains)
    (ch : Chs P t) : Prop where
  /-- Every chain is full. -/
  length_eq : ∀ q, (chs q).length = n q.label
  /-- The item of a prover round is `π`'s write. -/
  write_eq : ∀ (p : t.Leaf) (i : (P p.label).MessageIdx),
    (chs p)[i.1.1]? = some (.write ⟨i, π.writes p i⟩)
  /-- The chain input and the stream of every challenge are recorded and read `ch`. -/
  challenge : ∀ c : ChIdx P t, ∃ a s : Out k e,
    M.keyD D (M.ssOf x π) chs c.leaf ((chs c.leaf).take c.idx.1) = some a ∧
      D.lookup (.xof a.digest π.salt) = some s ∧
      (chs c.leaf)[c.idx.1.1]? = some (.absorb s.digest) ∧
      ((M.comp c.leaf.label).sampler c.idx).sample s.stream = some (ch c)

namespace RecordsChains

variable {chs : M.Chains} {ch : Chs P t} (hR : M.RecordsChains D x π chs ch)
include hR

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- **A prover round read from the recorded chains is the message of `π`'s write.** -/
theorem extStep_message_eq (q : t.Leaf) (i : (P q.label).MessageIdx) :
    M.extStep D (M.ssOf x π) chs q (chs q) i.1 i.1.2 =
      some ((M.comp q.label).msg i (π.writes q i) ((M.comp q.label).views D i (π.writes q i))) := by
  rw [M.extStep_message, hR.write_eq q i, Option.bind_some, (M.comp q.label).writeAt_write]
  rfl

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- **A challenge round read from the recorded chains is the challenge `ch`.** -/
theorem extStep_challenge_eq (c : ChIdx P t) :
    M.extStep D (M.ssOf x π) chs c.leaf (chs c.leaf) c.idx.1 c.idx.1.2 = some (ch c) := by
  obtain ⟨a, s, ha, hs, hit, hsm⟩ := hR.challenge c
  rw [M.extStep_challenge, hit]
  simp only [Option.bind_some, Item.getAbsorb, extChal, ha, hs, ↓reduceIte]
  exact hsm

/-- **Every round read from the recorded chains is the round of the transcript along `π`.** -/
theorem extStep_eq (q : t.Leaf) (r : ℕ) (hr : r < n q.label) :
    M.extStep D (M.ssOf x π) chs q (chs q) r hr = some (M.trT D π ch q ⟨r, hr⟩) := by
  by_cases hd : (P q.label).dir ⟨r, hr⟩ = .P_to_V
  · exact (hR.extStep_message_eq q ⟨⟨r, hr⟩, hd⟩).trans
      (congrArg some (M.trT_message D π ch q ⟨⟨r, hr⟩, hd⟩).symm)
  · exact (hR.extStep_challenge_eq ⟨q, (P q.label).chIdx ⟨r, hr⟩ hd⟩).trans
      (congrArg some (M.trT_challenge D π ch ⟨q, (P q.label).chIdx ⟨r, hr⟩ hd⟩).symm)

/-- **The full transcript of every leaf read from the recorded chains is the transcript along
`π`.** -/
theorem extLeaf_eq (q : t.Leaf) :
    M.extLeaf D (M.ssOf x π) chs q (chs q) (n q.label) le_rfl = some (M.trT D π ch q) := by
  obtain ⟨tr, htr⟩ := Option.isSome_iff_exists.1 (M.extLeaf_isSome D (M.ssOf x π) chs q (chs q)
    (fun r hr => Option.isSome_iff_exists.2 ⟨_, hR.extStep_eq q r hr⟩) _ le_rfl)
  rw [htr]
  congr 1
  funext r
  have h1 := M.extStep_of_extLeaf D (M.ssOf x π) chs q (chs q) _ le_rfl htr r.1 r.2
  rw [hR.extStep_eq q r.1 r.2] at h1
  exact (Option.some_inj.1 h1).symm

/-- **The causal past of every challenge read from the recorded chains is its past in the
transcript along `π`.** -/
theorem extPast_eq (c : ChIdx P t) :
    M.extPast D (M.ssOf x π) chs c ((chs c.leaf).take c.idx.1) = some ((M.trT D π ch).past c) := by
  have hctx : M.extCtx D (M.ssOf x π) chs c.leaf = some ((M.trT D π ch).ctx c.leaf) :=
    optAll_eq_some.2 fun q => hR.extLeaf_eq q.1
  rw [extPast, hctx, Option.bind_some,
    M.extLeaf_take D (M.ssOf x π) chs c.leaf (chs c.leaf) _ _ le_rfl,
    M.extLeaf_of_le D (M.ssOf x π) chs c.leaf (chs c.leaf) le_rfl (hR.extLeaf_eq c.leaf) _
      c.idx.1.2.le,
    Option.map_some]
  rfl

omit [∀ j i, Nonempty ((P j).Challenge i)] in
theorem length_take (c : ChIdx P t) : ((chs c.leaf).take c.idx.1).length = c.idx.1.1 := by
  rw [List.length_take, hR.length_eq]
  exact Nat.min_eq_left c.idx.1.2.le

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- **The composite verifier accepts the transcript along `π`** when the leaves of `π` are those of
the database's views at the positions the query phase reads, and the query phase accepts. -/
theorem accepts (Q : M.IOPQueries V x)
    (hopen : M.OpenedAs (fun p i => (M.comp p.label).views D i (π.writes p i)) (Q.pos chs ch)
      π.leaves) (hdec : Q.verdict chs ch π.leaves = true) : V x (M.trT D π ch) = true := by
  refine Q.accept_of_verdict chs ch (fun p i => (M.comp p.label).views D i (π.writes p i))
    (M.trT D π ch) _ ?_ (M.challenges_trT D π ch) hopen hdec
  intro p i w hw
  have hw' : w = π.writes p i := by
    have h2 := hR.write_eq p i
    rw [hw] at h2
    exact eq_of_heq (Sigma.mk.inj (Item.write.inj (Option.some_inj.1 h2))).2
  subst hw'
  exact M.trT_message D π ch p i

variable {Wit : Type} {rel : Set (X × Wit)} {E : CausalExtractor P t X Wit}
  {S : CausalStateFn P t X}

/-- **A flip at a challenge of the transcript along `π` puts `D` in `bad`.** -/
theorem mem_bad (c : ChIdx P t) (hflip : PastFlip rel E S x c ((M.trT D π ch).past c)
    ((M.trT D π ch).challenges c)) : D ∈ M.bad rel E S := by
  obtain ⟨a, s, ha, hs, -, hsm⟩ := hR.challenge c
  refine ⟨M.ssOf x π, c, chs, (chs c.leaf).take c.idx.1, (M.trT D π ch).past c, a, s,
    (M.trT D π ch).challenges c, fun q _ => hR.length_eq q, hR.length_take c, hR.extPast_eq c, ha,
    hs, ?_, hflip⟩
  rw [M.challenges_trT D π ch]
  exact hsm

end RecordsChains

end Chains

/-! ### Proposition 8.12 -/

section Prop812

variable {M : SPBCS Mg P X k kN kS L e} [∀ j i, Nonempty ((P j).Challenge i)]
  {V : X → FullTr P t → Bool} {Wit : Type} (rel : Set (X × Wit)) (E : CausalExtractor P t X Wit)
  (St : CausalStateFn P t X) {ε : ChIdx P t → ℝ≥0} {D : ODB k kN kS L e} {x : X}
  {π : M.NIProof} {chs : M.Chains} {ch : Chs P t}

/-- **CMS19 Proposition 8.12** (p. 42), knowledge form (p. 44), at chains a database records: when
`D` has no digest collision and records the chains `chs` of the proof `π` of `x` at the challenges
`ch`, the leaves of `π` are those of `D`'s views at the queried positions and the query phase
accepts, the database extractor returns a witness for `x` or `D` lies in `bad`. The flip comes
from `CausalRBR.exists_flip` on the transcript along `π`, which is the transcript read from `D`. -/
theorem mem_of_recordsChains [DecidableEq X] (hrbr : CausalRBRKnowledgeSound rel V E St ε)
    (hD : D ∉ digestCollision) (Q : M.IOPQueries V x) (hR : M.RecordsChains D x π chs ch)
    (hopen : M.OpenedAs (fun p i => (M.comp p.label).views D i (π.writes p i)) (Q.pos chs ch)
      π.leaves) (hdec : Q.verdict chs ch π.leaves = true) :
    D ∈ M.extracts rel E x ∪ M.bad rel E St := by
  by_cases hE : ∃ c, (x, E c x ((M.trT D π ch).past c)) ∈ rel
  · obtain ⟨c, hc⟩ := hE
    obtain ⟨a, s, ha, -, -, -⟩ := hR.challenge c
    exact Or.inl (mem_extracts_of hD rfl (fun q _ => hR.length_eq q) (hR.length_take c) ha
      (hR.extPast_eq c) hc)
  · push Not at hE
    obtain ⟨c, hflip⟩ := hrbr.exists_flip x _ (hR.accepts Q hopen hdec) id hE
    exact Or.inr (hR.mem_bad c ⟨hE c, hflip⟩)

/-- **CMS19 Proposition 8.12 at chains a database records, with the targeted extractor**: under
the hypotheses of `mem_of_recordsChains`, the targeted extractor at the challenges `ch` returns a
witness for `x` or `D` lies in `bad`. -/
theorem mem_of_recordsChains_targeted (hrbr : CausalRBRKnowledgeSound rel V E St ε)
    (Q : M.IOPQueries V x) (hR : M.RecordsChains D x π chs ch)
    (hopen : M.OpenedAs (fun p i => (M.comp p.label).views D i (π.writes p i)) (Q.pos chs ch)
      π.leaves) (hdec : Q.verdict chs ch π.leaves = true) :
    (∃ w ∈ M.targetedExtract D π ch E x, (x, w) ∈ rel) ∨ D ∈ M.bad rel E St := by
  by_cases hE : ∃ c, (x, E c x ((M.trT D π ch).past c)) ∈ rel
  · obtain ⟨c, hc⟩ := hE
    exact Or.inl ⟨_, (M.mem_targetedExtract D π ch E x).2 ⟨c, rfl⟩, hc⟩
  · push Not at hE
    obtain ⟨c, hflip⟩ := hrbr.exists_flip x _ (hR.accepts Q hopen hdec) id hE
    exact Or.inr (hR.mem_bad c ⟨hE c, hflip⟩)

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- **The leaves of a proof whose openings check are the leaves of the database's views**: at a
database without a digest collision that records every opening query of the trees of the
positions `ps` with the answers of `h`, a proof with one leaf per position whose every tree's
opening checks opens the leaves of the Merkle views of the database at the roots of its writes. -/
theorem openedAs_views_of_check (hcol : D ∉ digestCollision) {h : Query k kN kS L → Out k e}
    {ps : List M.Pos} (hlen : ps.length = π.leaves.length)
    (hpaths : ∀ τ ∈ M.trees ps, SPBCS.checkTree h π ps τ)
    (hrec : ∀ τ ∈ M.trees ps, ∀ q ∈ (M.treeProg π ps τ).trace h, D.lookup q = some (h q)) :
    M.OpenedAs (fun p i => (M.comp p.label).views D i (π.writes p i)) ps π.leaves := by
  refine List.forall₂_iff_zip.2 ⟨hlen, fun {q a} hqa => ?_⟩
  have hτ := M.mem_trees (List.of_mem_zip hqa).1
  have hmem : (q.pos.leaf.1, a) ∈ ((M.openedIn q.treeOf ps π.leaves).map Prod.fst).zip
      ((M.openedIn q.treeOf ps π.leaves).map Prod.snd) := by
    rw [← List.zip_of_prod rfl rfl]
    exact M.mem_openedIn hqa
  exact M.opening.leafAt_of_check hcol (fun q' hq' => hrec _ hτ q' hq') (hpaths _ hτ) hmem
    q.pos.leaf.2

variable {h : Query k kN kS L → Out k e} {Q : M.IOPQueries V x}

/-- **A database that records the verifier's queries on an accepted proof records its chains**:
the chains with merges of `π`, at its challenges with merges. -/
theorem recordsChains_of_verify (hrec : RecordsQueries D h x π Q) (hv : M.Accepts h x π Q) :
    M.RecordsChains D x π (M.chains h (M.ssOf x π) π.writes) (M.chV h (M.ssOf x π) π.writes) where
  length_eq := length_chains π.writes
  write_eq := chains_getElem?_message π.writes
  challenge c := by
    have hr := c.idx.1.2
    obtain ⟨h1, h2⟩ := M.mem_roundsProg_input x π h c.leaf c.idx.1 hr
    have htake : (M.chains h (M.ssOf x π) π.writes c.leaf).take c.idx.1 =
        (M.comp c.leaf.label).chainWith (π.writes c.leaf)
          (M.key h (M.ssOf x π) (M.chains h (M.ssOf x π) π.writes)
            (M.finals h (M.ssOf x π) π.writes) c.leaf) π.salt h c.idx.1 hr.le := by
      rw [chains_eq_chainWith]
      exact ComponentModel.take_chainWith _ _ _ _ _ _ _ _ hr.le
    obtain ⟨v, hsv⟩ := Option.isSome_iff_exists.1 (hv.sampled c)
    refine ⟨_, _, ?_, hrec.of_rounds h2, ?_, ?_⟩
    · rw [htake]
      exact keyD_chains hrec.finals c.leaf _ (hrec.of_rounds h1)
    · have hd : ¬ (P c.leaf.label).dir c.idx.1 = .P_to_V := by simp [c.idx.2]
      rw [chains_eq_chainWith, ComponentModel.chainWith_getElem? _ _ _ _ _ _ _ c.idx.1 hr]
      unfold ComponentModel.itemWith
      simp only [hd, ↓reduceDIte]
      rfl
    · have hc : M.chV h (M.ssOf x π) π.writes c = v := by
        simp only [chV]
        rw [hsv]
        rfl
      rw [hc, ← hsv]
      rfl

/-- **The leaves of an accepted proof are those of the database's views.** -/
theorem openedAs_views_of_verify (hD : D ∉ digestCollision) (hrec : RecordsQueries D h x π Q)
    (hv : M.Accepts h x π Q) :
    M.OpenedAs (fun p i => (M.comp p.label).views D i (π.writes p i))
      (Q.pos (M.chains h (M.ssOf x π) π.writes) (M.chV h (M.ssOf x π) π.writes)) π.leaves :=
  openedAs_views_of_check hD hv.leaves_length hv.paths fun τ hτ q hq =>
    hrec q (by
      rw [queries_eq]
      exact List.mem_append_right _ (List.mem_flatMap.2 ⟨τ, hτ, hq⟩))

/-- **CMS19 Proposition 8.12** (p. 42), knowledge form (p. 44), for the spBCS compiler at one
accepted proof: a database that records the verifier's queries on an accepted proof `π` of `x`
with the answers of `h` has a digest collision, or the database extractor returns a witness for
`x`, or it lies in `bad`. -/
theorem mem_of_verify [DecidableEq X] (hrbr : CausalRBRKnowledgeSound rel V E St ε)
    (hv : M.Accepts h x π Q) (hrec : RecordsQueries D h x π Q) :
    D ∈ digestCollision ∨ D ∈ M.extracts rel E x ∪ M.bad rel E St := by
  by_cases hD : D ∈ digestCollision
  · exact Or.inl hD
  · exact Or.inr (mem_of_recordsChains rel E St hrbr hD Q (recordsChains_of_verify hrec hv)
      (openedAs_views_of_verify hD hrec hv) hv.decides)

/-- **CMS19 Proposition 8.12 along one accepted spBCS proof, with the targeted extractor**:
a database that records the spBCS verifier's queries on an accepted proof `π` of `x` with
the answers of `h` has a digest collision, lies in `bad`, or the targeted extractor at the
challenges with merges returns a witness for `x`. -/
theorem mem_of_verify_targeted (hrbr : CausalRBRKnowledgeSound rel V E St ε)
    (hv : M.Accepts h x π Q) (hrec : RecordsQueries D h x π Q) :
    (∃ w ∈ M.targetedExtract D π (M.chV h (M.ssOf x π) π.writes) E x, (x, w) ∈ rel) ∨
      D ∈ M.bad rel E St ∪ digestCollision := by
  by_cases hD : D ∈ digestCollision
  · exact Or.inr (Or.inr hD)
  rcases mem_of_recordsChains_targeted rel E St hrbr Q (recordsChains_of_verify hrec hv)
      (openedAs_views_of_verify hD hrec hv) hv.decides with hE | hbad
  · exact Or.inl hE
  · exact Or.inr (Or.inl hbad)

end Prop812

end GordieHowe.SPBCS
