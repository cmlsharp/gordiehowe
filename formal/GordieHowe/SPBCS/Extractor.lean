-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Extract

@[expose] public section

/-!
# The database extractor of the spBCS compiler

The database extractor (paper `prot:bcs-db-extractor`, CMS19 section 8.5.2, p. 44) of the spBCS
compiler (`GordieHowe/SPBCS/Basic.lean`). A recorded round input of the statement holds its
observer's view: the full chains of the leaves its leaf reads in full, and for every branch hidden
from the leaf, the branch's final digest. The extractor reads each hidden branch back through its
final digest: the sink of a hidden branch reads its branch in full (`Merges.visible_sink_of_mem`)
and reads the leaves before the branch as the observer does (`Merges.visible_sink_iff`,
`Merges.hides_sink_iff`), so the recorded final input whose answer has that digest holds the
branch's chains. With the chains of the whole causal past it extracts the past
(`GordieHowe/SPBCS/Extract.lean`) and applies the causal extractor.

* `Merges.Obs.siteOf`: the hidden branch that contains a leaf an observer does not read in full
  (unique, `Merges.eq_of_hides`).
* `resolveSink D ss chs ds s`: branch `s`'s chains behind its final digest `ds s`, from the
  recorded `transcript` input whose answer has that digest, accepted only when it is the final
  input of `s` whose view is the observer's (chains `chs`, final digests `ds`) on the leaves before
  the branch.
* `fill o chs R`: the chains of the past of `o`: `chs` at the leaves `o` reads in full, the
  resolved chains `R s` at the leaves of each hidden branch `s`; `pastChains`: all hidden branches
  resolved.
* `dbExtract`: for each recorded round input of the statement, the causal extractor on the past
  read from `D`; `extracts`: the databases from which it returns a witness; `mem_extracts_of`: one
  recorded chain input from which a witness is extracted suffices.
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm

variable {ι : Type} {t : SPTerm ι} {Mg : Merges t}

/-! ### Filling the past of an observer -/

section Fill

variable {k : ℕ} {W : ι → Type}

/-- **The chains of the past of `o`** (module docstring): `chs` at the leaves `o` reads in full,
`R s` at the leaves of each hidden branch `s`, empty elsewhere. -/
def Merges.Obs.fill (o : Mg.Obs) (chs : (q : t.Leaf) → List (Item k (W q.label)))
    (R : Mg.Site → (q : t.Leaf) → List (Item k (W q.label))) (q : t.Leaf) :
    List (Item k (W q.label)) :=
  if o.Visible q then chs q else
    if h : ∃ s, Mg.Hides s o ∧ Mg.mem s q then R (o.siteOf h) q else []

namespace Merges.Obs

variable {o : Mg.Obs} {chs : (q : t.Leaf) → List (Item k (W q.label))}
  {R : Mg.Site → (q : t.Leaf) → List (Item k (W q.label))}

theorem fill_of_visible {q : t.Leaf} (hq : o.Visible q) : o.fill chs R q = chs q := by
  simp [fill, hq]

theorem fill_of_hides {s : Mg.Site} (hs : Mg.Hides s o) {q : t.Leaf} (hq : Mg.mem s q) :
    o.fill chs R q = R s q := by
  have hex : ∃ s, Mg.Hides s o ∧ Mg.mem s q := ⟨s, hs, hq⟩
  rw [fill, ite_eq_right fun hv => not_exists_hides_of_visible hv hex, dite_eq_left hex, siteOf_eq hex hs hq]

theorem fill_of_not_sees {q : t.Leaf} (hq : ¬ o.Sees q) : o.fill chs R q = [] := by
  rw [fill, ite_eq_right fun hv => hq hv.1, dite_eq_right fun h => hq (sees_of_exists_hides h)]

/-- **A filled past reads the chains only at the leaves read in full and the resolved chains of
each hidden branch only on the branch.** -/
theorem fill_congr {chs' : (q : t.Leaf) → List (Item k (W q.label))}
    {R' : Mg.Site → (q : t.Leaf) → List (Item k (W q.label))}
    (hc : ∀ q, o.Visible q → chs q = chs' q)
    (hR : ∀ s, Mg.Hides s o → ∀ q, Mg.mem s q → R s q = R' s q) :
    o.fill chs R = o.fill chs' R' := funext fun q => by
  by_cases hv : o.Visible q
  · rw [fill_of_visible hv, fill_of_visible hv, hc q hv]
  · by_cases hex : ∃ s, Mg.Hides s o ∧ Mg.mem s q
    · obtain ⟨s, hs, hm⟩ := hex
      rw [fill_of_hides hs hm, fill_of_hides hs hm, hR s hs q hm]
    · rw [fill, ite_eq_right hv, dite_eq_right hex, fill, ite_eq_right hv, dite_eq_right hex]

end Merges.Obs

/-- **The chains of branch `s` merged into the chains `chs`.** -/
def Merges.merged (s : Mg.Site) (chs chs' : (q : t.Leaf) → List (Item k (W q.label))) (q : t.Leaf) :
    List (Item k (W q.label)) :=
  if Mg.mem s q then chs' q else chs q

end Fill

variable {k kN kS L e : ℕ} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)] {X : Type}

section

variable (M : SPBCS Mg P X k kN kS L e) (D : ODB k kN kS L e)

/-! ### Reading a hidden branch through its final digest -/

/-- **The final input of branch `s` whose view agrees with an observer's** with the chains `chs`
and the final digests `ds`, with the chains `chs'` of the branch. -/
def finalAt (ss : SaltedStatement kS X) (chs : M.Chains) (ds : Mg.Site → Digest k) (s : Mg.Site)
    (chs' : M.Chains) : M.MContent :=
  .final ss s ((Merges.Obs.sink s : Mg.Obs).viewChains (W := fun j => (M.comp j).W)
    (Merges.merged (W := fun j => (M.comp j).W) s chs chs')) ((Merges.Obs.sink s : Mg.Obs).viewDs ds)

/-- **Branch `s`'s chains behind its final digest `ds s`** (module docstring), read at an
observer with the chains `chs` and the final digests `ds`. -/
def resolveSink (ss : SaltedStatement kS X) (chs : M.Chains) (ds : Mg.Site → Digest k)
    (s : Mg.Site) : Option M.Chains :=
  (findTr D (ds s)).bind fun b =>
    match M.senc.decode b with
    | some (.final _ s' chs' _) =>
      if s' = s ∧ M.senc.encode (M.finalAt ss chs ds s chs') = b then some chs' else none
    | _ => none

/-- **The chains of the past of the observer `o`** with the chains `chs` and the final digests
`ds`: the hidden branches resolved through their final digests. -/
def pastChains (ss : SaltedStatement kS X) (o : Mg.Obs) (chs : M.Chains) (ds : Mg.Site → Digest k) :
    Option M.Chains :=
  (optAll fun s => if Mg.Hides s o then M.resolveSink D ss chs ds s else some fun _ => []).map
    fun R => o.fill (W := fun j => (M.comp j).W) chs R

end

section

variable {M : SPBCS Mg P X k kN kS L e} {D : ODB k kN kS L e}

section Resolve

variable (ss : SaltedStatement kS X)

/-- **A final input at an observer's view of chains `chs` is the final content of `chs`.** -/
theorem finalAt_view {o : Mg.Obs} {s : Mg.Site} (hs : Mg.Hides s o) (chs : M.Chains)
    (fs : Mg.Site → Digest k) :
    M.finalAt ss ((o).viewChains (W := fun j => (M.comp j).W) chs) (o.viewDs fs) s
        ((Merges.Obs.sink s : Mg.Obs).viewChains (W := fun j => (M.comp j).W) chs) =
      finalContent ss chs fs s := by
  unfold finalAt finalContent
  congr 1
  · refine Merges.Obs.viewChains_congr _ fun q hq => ?_
    unfold Merges.merged
    split_ifs with hm
    · exact Merges.Obs.viewChains_of_visible _ _ hq
    · have hbef : ∀ q', Mg.mem s q' → q.Before q' := by
        rcases hq.1 with h1 | h1
        · exact absurd h1 hm
        · exact h1
      exact Merges.Obs.viewChains_of_visible _ _ ((Merges.visible_sink_iff hs hbef).1 hq)
  · refine Merges.Obs.viewDs_congr _ fun s' hs' => ?_
    exact Merges.Obs.viewDs_of_hides _ _ (Merges.hides_of_hides_sink hs hs')

/-- **A hidden branch whose final input is recorded resolves to its chains**: at an observer's
view of chains `chs` and final digests `fs`, when the final input of `s` at `chs` and `fs` is
recorded with an answer of digest `fs s`. -/
theorem resolveSink_view (hD : D ∉ digestCollision) {o : Mg.Obs} {s : Mg.Site}
    (hs : Mg.Hides s o) {chs : M.Chains} {fs : Mg.Site → Digest k}
    (hwf : ∀ q, (Merges.Obs.sink s : Mg.Obs).Sees q →
      chainWF (P q.label) (chs q) ∧ (chs q).length = n q.label) {a : Out k e}
    (ha : D.lookup (.transcript (M.senc.encode (finalContent ss chs fs s))) = some a)
    (hd : a.digest = fs s) :
    M.resolveSink D ss (o.viewChains (W := fun j => (M.comp j).W) chs) (o.viewDs fs) s =
      some ((Merges.Obs.sink s : Mg.Obs).viewChains (W := fun j => (M.comp j).W) chs) := by
  have hds : o.viewDs fs s = a.digest := by rw [Merges.Obs.viewDs_of_hides _ _ hs, hd]
  unfold resolveSink
  rw [hds, findTr_of_lookup hD ha, Option.bind_some, M.senc.decode_encode _ (wf_finalContent_of_sees ss fs hwf)]
  simp only [finalContent, finalAt_view ss hs]
  simp

/-- **The past of an observer whose hidden branches' final inputs are recorded resolves to the
chains**: at the observer's view of chains `chs` and final digests `fs`. -/
theorem pastChains_view (hD : D ∉ digestCollision) {o : Mg.Obs} {chs : M.Chains}
    {fs : Mg.Site → Digest k}
    (hwf : ∀ q, o.Sees q → chainWF (P q.label) (chs q) ∧ (chs q).length = n q.label)
    (hrec : ∀ s, Mg.Hides s o → ∃ a : Out k e,
      D.lookup (.transcript (M.senc.encode (finalContent ss chs fs s))) = some a ∧ a.digest = fs s) :
    ∃ F, M.pastChains D ss o (o.viewChains (W := fun j => (M.comp j).W) chs) (o.viewDs fs) = some F ∧
      ∀ q, o.Sees q → F q = chs q := by
  set R : Mg.Site → M.Chains := fun s => if Mg.Hides s o then
    (Merges.Obs.sink s : Mg.Obs).viewChains (W := fun j => (M.comp j).W) chs else fun _ => []
  refine ⟨o.fill (W := fun j => (M.comp j).W) (o.viewChains (W := fun j => (M.comp j).W) chs) R,
    ?_, fun q hq => ?_⟩
  · unfold pastChains
    rw [show (optAll fun s => if Mg.Hides s o then M.resolveSink D ss
        (o.viewChains (W := fun j => (M.comp j).W) chs) (o.viewDs fs) s
        else some fun _ => []) = some R from optAll_eq_some.2 fun s => by
      by_cases hs : Mg.Hides s o
      · simp only [hs, ↓reduceIte, R]
        obtain ⟨a, ha, hd⟩ := hrec s hs
        exact resolveSink_view ss hD hs (fun q hq => hwf q (Merges.sees_of_sees_sink hs hq)) ha hd
      · simp [hs, R]]
    rfl
  · by_cases hv : o.Visible q
    · rw [Merges.Obs.fill_of_visible hv, Merges.Obs.viewChains_of_visible _ _ hv]
    · obtain ⟨s, hs, hm⟩ := Merges.Obs.exists_hides_of_sees hq hv
      rw [Merges.Obs.fill_of_hides hs hm]
      simp only [hs, ↓reduceIte, R]
      exact Merges.Obs.viewChains_of_visible _ _ (Merges.visible_sink_of_mem hm)

end Resolve

/-! ### The database extractor -/

section Extractor

variable (M) {Wit : Type} (rel : Set (X × Wit)) (E : CausalExtractor P t X Wit)

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

/-- The witness the causal extractor reads at the statement `x` from one recorded query: for a
`transcript` input that decodes to a round input of `x` whose own items end before a challenge
round, the causal extractor on the causal past read from `D`, its hidden branches resolved through
their final digests. -/
def candidate [DecidableEq X] (x : X) (D : ODB k kN kS L e) : Query k kN kS L → Option Wit
  | .transcript b =>
    match M.senc.decode b with
    | some (.round ss p chs ds own) =>
      if ss.stmt = x then
        (chAt p own.length).bind fun i =>
          (M.pastChains D ss (.leaf p) chs ds).bind fun F =>
            (M.extPast D ss F ⟨p, i⟩ own).map (E ⟨p, i⟩ x)
      else none
    | _ => none
  | _ => none

/-- **The database extractor at the statement `x`** (paper `prot:bcs-db-extractor`, `LExtract`
with the causal extractor `E`, CMS19 section 8.5.2, p. 44): the witnesses `E` reads from the
recorded `transcript` inputs of `D` that decode to a round input of `x`.

Running time, in the database size `|D|`, the input length `L`, the number of leaves and their
rounds: for each key of `D`, one run of `senc.decode` on at most `L` bytes; then `pastChains`:
at most `|Site|` digests followed, each one pass over the entries of `D`, one decode and one
encoding; then `extPast`: at most `t.size n` calls of `extStep`, each building one chain input
(`keyD`: at most `|Site|²` final steps, each one encoding and one lookup, and one encoding) and two
lookups, or one Merkle view per tree of a round; then one call of `E` (polynomial by its own
Running time paragraph). This running time is argued here, not proved in Lean. -/
def dbExtract [DecidableEq X] (x : X) (D : ODB k kN kS L e) : Multiset Wit :=
  D.keys.val.filterMap (M.candidate E x D)

/-- The databases from which the extractor succeeds at `x`. -/
def extracts [DecidableEq X] (x : X) : Set (ODB k kN kS L e) :=
  {D | ∃ w ∈ M.dbExtract E x D, (x, w) ∈ rel}

variable {M rel E}

/-- **A recorded chain input from which a witness is extracted puts `D` in `extracts`**: in a
database without a digest collision, a past of `x`'s challenge `c` read from full chains whose
chain input is recorded (`keyD`), with a witness. -/
theorem mem_extracts_of [DecidableEq X] (hD : D ∉ digestCollision) {x : X}
    {ss : SaltedStatement kS X} (hx : ss.stmt = x) {c : ChIdx P t} {chs : M.Chains}
    {l : M.Items c.leaf} {past : CausalPast P c} (hfull : M.ChainsFull chs c.leaf)
    (hl : l.length = c.idx.1) {a : Out k e} (ha : M.keyD D ss chs c.leaf l = some a)
    (hp : M.extPast D ss chs c l = some past) (hrel : (x, E c x past) ∈ rel) :
    D ∈ M.extracts rel E x := by
  obtain ⟨hwf, hlwf, hlen⟩ := M.wf_of_extPast D ss chs hfull hl hp
  have ha' := ha
  unfold keyD at ha'
  split_ifs at ha' with hrec
  have hwfc := wf_roundContent_of_before ss (M.finalsD D ss chs) hwf hlwf hlen
  obtain ⟨F, hF, hFe⟩ := pastChains_view ss hD (o := .leaf c.leaf) (chs := chs)
    (fs := M.finalsD D ss chs) (fun q hq => hwf q hq) fun s hs => by
      obtain ⟨a', ha''⟩ := DB.mem_iff_lookup.1 (hrec s hs)
      exact ⟨a', ha'', (M.finalsD_eq_of_lookup D ss chs ha'').symm⟩
  refine ⟨E c x past, (Multiset.mem_filterMap _ _).2 ⟨M.inputD D ss chs c.leaf l,
    Finmap.mem_keys.2 (DB.mem_iff_lookup.2 ⟨a, ha'⟩), ?_⟩, hrel⟩
  have hext : M.extPast D ss F c l = some past := by
    rw [M.extPast_congr D ss (fun r hr => hFe r hr)]
    exact hp
  simp only [candidate, inputD, M.senc.decode_encode _ hwfc]
  simp only [roundContent]
  rw [ite_eq_left hx, hl, chAt_idx, Option.bind_some, hF, Option.bind_some]
  simp only [hext, Option.map_some]

end Extractor

end

end GordieHowe.SPBCS
