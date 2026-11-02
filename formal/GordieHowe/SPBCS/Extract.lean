-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Basic
public import GordieHowe.SPBCS.Extraction.TranscriptLookup

@[expose] public section

/-!
# Extraction of causal pasts from an oracle database

CMS19 `BCSExtract` (p. 41) for the spBCS compiler (`GordieHowe/SPBCS/Basic.lean`): the
transcript of a leaf read from its chain and an oracle database `D`. The chains of all leaves are
given as one function `chs`. A challenge round reads its challenge from the recorded answer at its
chain input with merges, which the extractor builds as the verifier does, with the oracle read off
`D`:

* `dbOracle D`: the recorded answer at a query, `defaultOut` where none is recorded;
  `finalsD D ss chs`: the final digests of the branches at the chains `chs` for that oracle
  (`GordieHowe.SPBCS.finalsWith`); `finalInputD`, `inputD`: the final input of a branch and the
  chain input of a challenge round with these final digests.
* `keyD D ss chs p l`: the recorded answer at the chain input of leaf `p` at its own items `l`,
  when the final inputs of the branches hidden from `p` are recorded (`FinalsRecorded`).
* `extLeaf D ss chs q l r`: the first `r` rounds of leaf `q`'s transcript read from its chain `l`:
  a prover round's message from the write and the Merkle views of `D` at its roots, a challenge
  round's challenge from the recorded key and stream of its chain input (`extChal`) when the
  stream's digest is the absorbed item. `extCtx D ss chs p`: the full transcripts of the leaves
  before `p`; `extPast D ss chs c l`: the causal past of the challenge `c`.
* Stability (CMS19 Lemma 8.8, p. 41): every reading that succeeds on `D` succeeds with the same
  value after recording one new answer (`keyD_extend_of_eq_some`), and if recording one new
  collision-free entry changes the extraction, the new answer's digest is carried by the chains
  read, lies in `S(D)`, or, for a new `transcript` query, is one of the final digests carried by
  the recorded inputs (`pend`, at most `nJ · |D|` digests): a final input recorded after the round
  inputs that hold its digest (`digest_mem_of_extLeaf_extend`, `digest_mem_of_extPast_extend`, and
  the converse forms).
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm
open scoped ENNReal NNReal

variable {k kN kS L e : ℕ}

/-- A function on finitely many arguments read off partial values: defined when every value is. -/
def optAll {α : Type*} [Fintype α] {β : α → Type*} (f : ∀ a, Option (β a)) :
    Option (∀ a, β a) :=
  if h : ∀ a, (f a).isSome then some fun a => (f a).get (h a) else none

theorem optAll_eq_some {α : Type*} [Fintype α] {β : α → Type*} {f : ∀ a, Option (β a)}
    {g : ∀ a, β a} : optAll f = some g ↔ ∀ a, f a = some (g a) := by
  classical
  unfold optAll
  constructor
  · intro h a
    split_ifs at h with hs
    obtain rfl := Option.some_inj.1 h
    simp
  · intro h
    rw [dite_eq_left fun a => by simp [h a]]
    congr 1
    funext a
    simp [h a]

section Obs

variable {ι : Type} {t : SPTerm ι} {Mg : Merges t}

/-! ### The hidden branch of a leaf -/

namespace Merges.Obs

variable (o : Mg.Obs)

/-- **The hidden branch containing a leaf exists uniquely** when the leaf is in some hidden
branch. -/
theorem existsUnique_site {q : t.Leaf} (h : ∃ s, Mg.Hides s o ∧ Mg.mem s q) :
    ∃! s, Mg.Hides s o ∧ Mg.mem s q := by
  obtain ⟨s, hs⟩ := h
  exact ⟨s, hs, fun s' hs' => Merges.eq_of_hides hs'.1 hs.1 hs'.2 hs.2⟩

/-- **The hidden branch that contains the leaf `q`.** -/
def siteOf {q : t.Leaf} (h : ∃ s, Mg.Hides s o ∧ Mg.mem s q) : Mg.Site :=
  Fintype.choose _ (existsUnique_site o h)

variable {o}

theorem hides_siteOf {q : t.Leaf} (h : ∃ s, Mg.Hides s o ∧ Mg.mem s q) : Mg.Hides (o.siteOf h) o :=
  (Fintype.choose_spec _ (existsUnique_site o h)).1

theorem mem_siteOf {q : t.Leaf} (h : ∃ s, Mg.Hides s o ∧ Mg.mem s q) : Mg.mem (o.siteOf h) q :=
  (Fintype.choose_spec _ (existsUnique_site o h)).2

theorem siteOf_eq {q : t.Leaf} (h : ∃ s, Mg.Hides s o ∧ Mg.mem s q) {s : Mg.Site}
    (hs : Mg.Hides s o) (hq : Mg.mem s q) : o.siteOf h = s :=
  Merges.eq_of_hides (hides_siteOf h) hs (mem_siteOf h) hq

/-- **A leaf in the past of an observer is read in full or lies in a hidden branch.** -/
theorem exists_hides_of_sees {q : t.Leaf} (hs : o.Sees q) (hv : ¬ o.Visible q) :
    ∃ s, Mg.Hides s o ∧ Mg.mem s q := by
  by_contra hn
  push Not at hn
  exact hv ⟨hs, fun s h hm => hn s h hm⟩

/-- **A leaf read in full lies in no hidden branch.** -/
theorem not_exists_hides_of_visible {q : t.Leaf} (hv : o.Visible q) :
    ¬ ∃ s, Mg.Hides s o ∧ Mg.mem s q := fun ⟨s, hs, hm⟩ => hv.2 s hs hm

/-- **A leaf of a hidden branch is in the past of the observer.** -/
theorem sees_of_exists_hides {q : t.Leaf} (h : ∃ s, Mg.Hides s o ∧ Mg.mem s q) : o.Sees q := by
  obtain ⟨s, hs, hm⟩ := h
  exact Merges.sees_of_hides_of_mem hs hm

end Merges.Obs

end Obs

variable {ι : Type} {t : SPTerm ι} {Mg : Merges t} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)] {X : Type}

section

variable (M : SPBCS Mg P X k kN kS L e)

/-! ### Well-formed contents -/

section WF

variable {M} (ss : SaltedStatement kS X)

/-- **A round content is well formed** when the chains before its leaf are full and well formed and
its own items a well-formed proper prefix. -/
theorem wf_roundContent_of_before {chs : M.Chains} (fs : Mg.Site → Digest k) {p : t.Leaf}
    (hwf : ∀ q, q.Before p → chainWF (P q.label) (chs q) ∧ (chs q).length = n q.label)
    {l : M.Items p} (hl : chainWF (P p.label) l) (hlen : l.length < n p.label) :
    (roundContent ss chs fs p l).WF n fun j => chainWF (P j) :=
  .round (Content.viewWF_view (Merges.Obs.leaf p) (fun q hq => (hwf q hq.1).1) (fun q hq => (hwf q hq.1).2) _) hl hlen

/-- **A final content is well formed** when the chains in the past of its sink are full and well
formed. -/
theorem wf_finalContent_of_sees {chs : M.Chains} (fs : Mg.Site → Digest k) {s : Mg.Site}
    (hwf : ∀ q, (Merges.Obs.sink s : Mg.Obs).Sees q →
      chainWF (P q.label) (chs q) ∧ (chs q).length = n q.label) :
    (finalContent ss chs fs s).WF n fun j => chainWF (P j) :=
  .final (Content.viewWF_view (Merges.Obs.sink s) (fun q hq => (hwf q hq.1).1) (fun q hq => (hwf q hq.1).2) _)

end WF

/-! ### The chain inputs read from a database -/

/-- **The oracle read off a database**: the recorded answer at a query, `defaultOut` where none is
recorded. -/
def dbOracle (D : ODB k kN kS L e) (q : Query k kN kS L) : Out k e := (D.lookup q).getD defaultOut

variable (D : ODB k kN kS L e) (ss : SaltedStatement kS X) (chs : M.Chains)

/-- **The final digests read from `D`** at the chains `chs`: the final digests
(`GordieHowe.SPBCS.finalsWith`) of the oracle read off `D`. -/
def finalsD : Mg.Site → Digest k := M.finalsWith (dbOracle D) ss chs

/-- **The final input of the branch of site `s`** at the chains `chs` and the final digests read
from `D`. -/
def finalInputD (s : Mg.Site) : Query k kN kS L :=
  .transcript (M.senc.encode (finalContent ss chs (M.finalsD D ss chs) s))

/-- **The final inputs of the branches hidden from `o` are recorded** in `D`. -/
def FinalsRecorded (o : Mg.Obs) : Prop := ∀ s, Mg.Hides s o → M.finalInputD D ss chs s ∈ D

instance (o : Mg.Obs) : Decidable (M.FinalsRecorded D ss chs o) := by
  unfold FinalsRecorded
  infer_instance

/-- **The chain input of leaf `p` at its own items `l`**, with the final digests read from `D`. -/
def inputD (p : t.Leaf) (l : M.Items p) : Query k kN kS L :=
  .transcript (M.senc.encode (roundContent ss chs (M.finalsD D ss chs) p l))

/-- **The recorded answer at the chain input of leaf `p` at its own items `l`**, when the final
inputs of the branches hidden from `p` are recorded. -/
def keyD (p : t.Leaf) (l : M.Items p) : Option (Out k e) :=
  if M.FinalsRecorded D ss chs (.leaf p) then D.lookup (M.inputD D ss chs p l) else none

/-- **A final digest read from `D`** is the digest of the recorded answer at its final input. -/
theorem finalsD_eq_of_lookup {s : Mg.Site} {a : Out k e}
    (h : D.lookup (M.finalInputD D ss chs s) = some a) : M.finalsD D ss chs s = a.digest := by
  show M.finalsWith (dbOracle D) ss chs s = _
  rw [finalsWith_eq]
  show (dbOracle D (M.finalInputD D ss chs s)).digest = _
  rw [dbOracle, h]
  rfl

/-- **The chain items before every challenge round are full and well formed**: the chains of the
leaves before `p` are full chains. -/
def ChainsFull (p : t.Leaf) : Prop := ∀ q, q.Before p → (chs q).length = n q.label

/-! ### The transcript of a leaf read from its chain -/

/-- The challenge `i` of leaf `q` read from `D` at the own items `l₀` and the absorbed digest
`d`: the key (`keyD`) and the stream of the chain input are recorded, the stream's digest is `d`,
and the sampler accepts. -/
def extChal (q : t.Leaf) (l₀ : M.Items q) (d : Digest k) (i : (P q.label).ChallengeIdx) :
    Option ((P q.label).Challenge i) :=
  (M.keyD D ss chs q l₀).bind fun a =>
    (D.lookup (.xof a.digest ss.salt)).bind fun s =>
      if s.digest = d then ((M.comp q.label).sampler i).sample s.stream else none

/-- Round `r` of leaf `q`'s transcript read from its chain `l`. -/
def extStep (q : t.Leaf) (l : M.Items q) (r : ℕ) (hr : r < n q.label) :
    Option ((P q.label).Type ⟨r, hr⟩) :=
  if hd : (P q.label).dir ⟨r, hr⟩ = .P_to_V then
    (l[r]?.bind ((M.comp q.label).writeAt ⟨⟨r, hr⟩, hd⟩)).map fun w =>
      (M.comp q.label).msg ⟨⟨r, hr⟩, hd⟩ w ((M.comp q.label).views D ⟨⟨r, hr⟩, hd⟩ w)
  else
    (l[r]?.bind Item.getAbsorb).bind fun d =>
      M.extChal D ss chs q (l.take r) d ((P q.label).chIdx ⟨r, hr⟩ hd)

/-- **The first `r` rounds of leaf `q`'s transcript** read from its chain `l` (CMS19 `BCSExtract`,
p. 41, for a leaf of the composite).

Running time: `r` calls of `extStep`, each at most two lookups after building one chain input
(`keyD`: the final digests, at most `|Site|²` encodings and lookups, and one encoding), or one
Merkle view per tree of the round. This running time is argued here, not proved in Lean. -/
def extLeaf (q : t.Leaf) (l : M.Items q) : (r : ℕ) → (hr : r ≤ n q.label) →
    Option ((P q.label).Transcript ⟨r, by omega⟩)
  | 0, _ => some fun i => i.elim0
  | r + 1, hr => (extLeaf q l r (by omega)).bind fun tr =>
      (M.extStep D ss chs q l r (by omega)).map ((P q.label).concat (m := ⟨r, by omega⟩) tr)

/-- **The full transcripts of the leaves before `p`**, each read from its chain. -/
def extCtx (p : t.Leaf) : Option (CausalCtx P p) :=
  optAll fun q : {q : t.Leaf // q.Before p} => M.extLeaf D ss chs q.1 (chs q.1) (n q.1.label) le_rfl

/-- **The causal past of the challenge `c`** read from the chains `chs` and `c`'s own items `l`:
the context and the first `c.idx` rounds of `c`'s leaf. -/
def extPast (c : ChIdx P t) (l : M.Items c.leaf) : Option (CausalPast P c) :=
  (M.extCtx D ss chs c.leaf).bind fun ctx =>
    (M.extLeaf D ss chs c.leaf l c.idx.1 c.idx.1.2.le).map fun own => ⟨ctx, own⟩

theorem extLeaf_succ (q : t.Leaf) (l : M.Items q) (r : ℕ) (hr : r + 1 ≤ n q.label) :
    M.extLeaf D ss chs q l (r + 1) hr = (M.extLeaf D ss chs q l r (by omega)).bind fun tr =>
      (M.extStep D ss chs q l r (by omega)).map ((P q.label).concat (m := ⟨r, by omega⟩) tr) := rfl

theorem extStep_take (q : t.Leaf) (l : M.Items q) {r m : ℕ} (hrm : r < m) (hr : r < n q.label) :
    M.extStep D ss chs q (l.take m) r hr = M.extStep D ss chs q l r hr := by
  have h1 : (l.take m)[r]? = l[r]? := List.getElem?_take_of_lt hrm
  have h2 : (l.take m).take r = l.take r := by rw [List.take_take, Nat.min_eq_left hrm.le]
  simp only [extStep, h1, h2]

theorem extLeaf_take (q : t.Leaf) (l : M.Items q) {m : ℕ} :
    ∀ r (hr : r ≤ n q.label), r ≤ m →
      M.extLeaf D ss chs q (l.take m) r hr = M.extLeaf D ss chs q l r hr
  | 0, _, _ => rfl
  | r + 1, hr, hrm => by
    rw [extLeaf_succ, extLeaf_succ, extLeaf_take q l r (by omega) (by omega),
      M.extStep_take D ss chs q l (by omega : r < m)]

/-- A challenge round reads the absorbed item and the challenge at the key of its prefix. -/
theorem extStep_challenge (q : t.Leaf) (l : M.Items q) (i : (P q.label).ChallengeIdx) :
    M.extStep D ss chs q l i.1 i.1.2 = (l[i.1.1]?.bind Item.getAbsorb).bind fun d =>
      M.extChal D ss chs q (l.take i.1) d i := by
  have hd : ¬ (P q.label).dir i.1 = .P_to_V := by simp [i.2]
  unfold extStep
  simp only [hd, ↓reduceDIte]
  rfl

/-- A prover round reads the write and the Merkle views at its roots. -/
theorem extStep_message (q : t.Leaf) (l : M.Items q) (i : (P q.label).MessageIdx) :
    M.extStep D ss chs q l i.1 i.1.2 = (l[i.1.1]?.bind ((M.comp q.label).writeAt i)).map fun w =>
      (M.comp q.label).msg i w ((M.comp q.label).views D i w) := by
  unfold extStep
  simp only [i.2, ↓reduceDIte]
  rfl

/-- A round that is read fits its position of the chain. -/
theorem fits_of_extStep {q : t.Leaf} {l : M.Items q} {r : ℕ} {hr : r < n q.label}
    {v : (P q.label).Type ⟨r, hr⟩} (h : M.extStep D ss chs q l r hr = some v) :
    ∃ it, l[r]? = some it ∧ Fits (P q.label) r it := by
  unfold extStep at h
  split_ifs at h with hd
  · obtain ⟨w, hw, -⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨it, hit, hw'⟩ := Option.bind_eq_some_iff.1 hw
    exact ⟨it, hit, by rw [(M.comp q.label).eq_write_of_writeAt hw']; rfl⟩
  · obtain ⟨d, hdl, -⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨it, hit, hd'⟩ := Option.bind_eq_some_iff.1 hdl
    refine ⟨it, hit, ?_⟩
    rw [Item.eq_absorb_of_getAbsorb hd']
    exact ⟨hr, by cases h' : (P q.label).dir ⟨r, hr⟩ <;> simp_all⟩

theorem extLeaf_isSome (q : t.Leaf) (l : M.Items q)
    (h : ∀ r (hr : r < n q.label), (M.extStep D ss chs q l r hr).isSome) :
    ∀ r (hr : r ≤ n q.label), (M.extLeaf D ss chs q l r hr).isSome
  | 0, _ => rfl
  | r + 1, hr => by
    obtain ⟨tr, htr⟩ := Option.isSome_iff_exists.1 (extLeaf_isSome q l h r (by omega))
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (h r (by omega))
    rw [extLeaf_succ, htr, Option.bind_some, hv, Option.map_some]
    rfl

/-- The rounds of an extracted transcript are the extracted rounds. -/
theorem extStep_of_extLeaf (q : t.Leaf) (l : M.Items q) :
    ∀ r (hr : r ≤ n q.label) {tr}, M.extLeaf D ss chs q l r hr = some tr →
      ∀ j (hj : j < r), M.extStep D ss chs q l j (by omega) = some (tr ⟨j, hj⟩)
  | 0, _, _, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | r + 1, hr, tr, h, j, hj => by
    rw [extLeaf_succ] at h
    obtain ⟨tr₀, h₀, hv⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨v, hsv, rfl⟩ := Option.map_eq_some_iff.1 hv
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | rfl
    · rw [(P q.label).concat_apply_of_lt (m := ⟨r, by omega⟩) tr₀ v j hj']
      exact extStep_of_extLeaf q l r (by omega) h₀ j hj'
    · rw [(P q.label).concat_apply_last (m := ⟨j, by omega⟩) tr₀ v]
      exact hsv

/-- **An extraction of a chain at `m` rounds restricts to `r ≤ m` rounds.** -/
theorem extLeaf_of_le (q : t.Leaf) (l : M.Items q) {m : ℕ} (hm : m ≤ n q.label)
    {tr : (P q.label).Transcript ⟨m, by omega⟩} (h : M.extLeaf D ss chs q l m hm = some tr)
    (r : ℕ) (hr : r ≤ m) :
    M.extLeaf D ss chs q l r (hr.trans hm) = some (tr.take ⟨r, by omega⟩ hr) := by
  have hsteps := M.extStep_of_extLeaf D ss chs q l m hm h
  have hall : ∀ j (hj : j < r), (M.extStep D ss chs q l j (by omega)).isSome := fun j hj => by
    rw [hsteps j (by omega)]
    rfl
  obtain ⟨tr', htr'⟩ : ∃ tr', M.extLeaf D ss chs q l r (hr.trans hm) = some tr' := by
    suffices H : ∀ r' (hr' : r' ≤ r),
        (M.extLeaf D ss chs q l r' (hr'.trans (hr.trans hm))).isSome from
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
  have h1 := M.extStep_of_extLeaf D ss chs q l r (hr.trans hm) htr' i.1 i.2
  have h2 := hsteps i.1 (by have hi : i.1 < r := i.2; omega)
  exact Option.some_inj.1 (h1.symm.trans h2)

/-- **The first `r` items of a chain from which `r` rounds are read are well formed.** -/
theorem chainWF_take_of_extLeaf {q : t.Leaf} {l : M.Items q} {r : ℕ} {hr : r ≤ n q.label}
    {tr : (P q.label).Transcript ⟨r, by omega⟩} (h : M.extLeaf D ss chs q l r hr = some tr) :
    chainWF (P q.label) (l.take r) := by
  intro j hj
  have hjr : j < r := lt_of_lt_of_le hj (List.length_take_le r l)
  obtain ⟨it, hit, hf⟩ := M.fits_of_extStep D ss chs (M.extStep_of_extLeaf D ss chs q l r hr h j hjr)
  have hit' : (l.take r)[j]? = some it := by rw [List.getElem?_take_of_lt hjr]; exact hit
  rw [List.getElem?_eq_getElem hj] at hit'
  exact (Option.some_inj.1 hit') ▸ hf

/-- A chain of `r` items from which the first `r` rounds are read is well formed. -/
theorem chainWF_of_extLeaf {q : t.Leaf} {l : M.Items q} {r : ℕ} {hr : r ≤ n q.label}
    {tr : (P q.label).Transcript ⟨r, by omega⟩} (h : M.extLeaf D ss chs q l r hr = some tr)
    (hl : l.length = r) : chainWF (P q.label) l := by
  have := M.chainWF_take_of_extLeaf D ss chs h
  rwa [List.take_of_length_le hl.le] at this

/-- **An extracted causal past comes from full well-formed chains and a well-formed proper
prefix.** -/
theorem wf_of_extPast {c : ChIdx P t} {l : M.Items c.leaf} {past : CausalPast P c}
    (hfull : M.ChainsFull chs c.leaf) (hl : l.length = c.idx.1)
    (h : M.extPast D ss chs c l = some past) :
    (∀ r, r.Before c.leaf → chainWF (P r.label) (chs r) ∧ (chs r).length = n r.label) ∧
      chainWF (P c.leaf.label) l ∧ l.length < n c.leaf.label := by
  obtain ⟨ctx, hctx, hown⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨own, hown', -⟩ := Option.map_eq_some_iff.1 hown
  refine ⟨fun r hr => ⟨M.chainWF_of_extLeaf D ss chs ((optAll_eq_some.1 hctx) ⟨r, hr⟩) (hfull r hr),
    hfull r hr⟩, M.chainWF_of_extLeaf D ss chs hown' hl, ?_⟩
  rw [hl]
  exact c.idx.1.2

/-! ### The extraction reads only the chains of the causal past -/

section Congr

variable {chs} {chs' : M.Chains}

/-- **The final digests of the branches hidden from `p` read only the chains before `p`.** -/
theorem finalsD_congr_of_hides {p : t.Leaf} (h : ∀ r, r.Before p → chs r = chs' r) {s : Mg.Site}
    (hs : Mg.Hides s (.leaf p)) : M.finalsD D ss chs s = M.finalsD D ss chs' s :=
  finalsWith_congr_of_hides h hs

/-- **The final input of a branch hidden from `p` reads only the chains before `p`.** -/
theorem finalInputD_congr {p : t.Leaf} (h : ∀ r, r.Before p → chs r = chs' r) {s : Mg.Site}
    (hs : Mg.Hides s (.leaf p)) : M.finalInputD D ss chs s = M.finalInputD D ss chs' s := by
  unfold finalInputD
  rw [finalContent_congr (fun q hq => h q (Merges.sees_of_sees_sink hs hq.1)) fun s' hs' =>
    M.finalsD_congr_of_hides D ss h (Merges.hides_of_hides_sink hs hs')]

/-- **The chain input of leaf `p` reads only the chains before `p`.** -/
theorem inputD_congr {p : t.Leaf} (h : ∀ r, r.Before p → chs r = chs' r) (l : M.Items p) :
    M.inputD D ss chs p l = M.inputD D ss chs' p l := by
  unfold inputD
  rw [roundContent_congr (fun q hq => h q hq.1) fun s hs => M.finalsD_congr_of_hides D ss h hs]

/-- **The key of a leaf's chain input reads only the chains before the leaf.** -/
theorem keyD_congr {p : t.Leaf} (h : ∀ r, r.Before p → chs r = chs' r) (l : M.Items p) :
    M.keyD D ss chs p l = M.keyD D ss chs' p l := by
  have hfr : M.FinalsRecorded D ss chs (.leaf p) ↔ M.FinalsRecorded D ss chs' (.leaf p) :=
    forall_congr' fun s => imp_congr_right fun hs => by rw [M.finalInputD_congr D ss h hs]
  unfold keyD
  rw [M.inputD_congr D ss h l]
  by_cases hf : M.FinalsRecorded D ss chs (.leaf p)
  · rw [ite_eq_left hf, ite_eq_left (hfr.1 hf)]
  · rw [ite_eq_right hf, ite_eq_right (mt hfr.2 hf)]

theorem extLeaf_congr {q : t.Leaf} (h : ∀ r, r.Before q → chs r = chs' r) (l : M.Items q) :
    ∀ r (hr : r ≤ n q.label), M.extLeaf D ss chs q l r hr = M.extLeaf D ss chs' q l r hr := by
  have hstep : M.extStep D ss chs q l = M.extStep D ss chs' q l := by
    funext r hr
    simp only [extStep, extChal, M.keyD_congr D ss h]
  intro r
  induction r with
  | zero => intro _; rfl
  | succ r ih => intro hr; rw [extLeaf_succ, extLeaf_succ, ih, hstep]

theorem extCtx_congr {p : t.Leaf} (h : ∀ r, r.Before p → chs r = chs' r) :
    M.extCtx D ss chs p = M.extCtx D ss chs' p := by
  unfold extCtx
  congr 1
  funext q
  rw [h q.1 q.2, M.extLeaf_congr D ss (fun r hr => h r (hr.trans q.2))]

theorem extPast_congr {c : ChIdx P t} (h : ∀ r, r.Before c.leaf → chs r = chs' r)
    (l : M.Items c.leaf) : M.extPast D ss chs c l = M.extPast D ss chs' c l := by
  simp only [extPast, M.extCtx_congr D ss h, M.extLeaf_congr D ss h]

end Congr

/-! ### The digests a new answer must avoid -/

/-- The final digests held by a recorded input. -/
def finalDsOf : Query k kN kS L → Finset (Digest k)
  | .transcript b => ((M.senc.decode b).map Content.finalDs).getD ∅
  | _ => ∅

/-- **The final digests held by the recorded inputs.** -/
def finalDsAll : Finset (Digest k) := D.keys.biUnion M.finalDsOf

/-- **The final digests a new answer at `q` must avoid**: for a new `transcript` query, which may
be the final input of a branch whose final digest recorded round inputs already hold, the final
digests held by the recorded inputs (`finalDsAll`); nothing for any other query. -/
def pend : Query k kN kS L → Finset (Digest k)
  | .transcript _ => M.finalDsAll D
  | _ => ∅

/-- **The recorded inputs hold at most `nJ · |D|` final digests.** -/
theorem card_finalDsAll_le : (M.finalDsAll D).card ≤ Mg.nJ * D.size :=
  Finset.card_biUnion_le.trans ((Finset.sum_le_card_nsmul _ _ Mg.nJ fun q _ => by
    cases q with
    | transcript b =>
      simp only [finalDsOf]
      cases M.senc.decode b with
      | none => simp
      | some c => exact Content.card_finalDs_le c
    | _ => simp [finalDsOf]).trans (by simp [DB.size, mul_comm]))

/-- **The final digests a new answer must avoid are at most `nJ · |D|`.** -/
theorem card_pend_le (q : Query k kN kS L) : (M.pend D q).card ≤ Mg.nJ * D.size := by
  cases q with
  | transcript b => exact M.card_finalDsAll_le D
  | _ => exact Nat.zero_le _

/-! ### Recording one more answer -/

section Stability

variable {D} {q₀ : Query k kN kS L} {y : Out k e}

/-- **The final digests read from `D` stay** after recording a new answer, at the branches hidden
from `o` whose final inputs are recorded. -/
theorem finalsD_extend (hq : q₀ ∉ D) {o : Mg.Obs} (hrec : M.FinalsRecorded D ss chs o) :
    ∀ s, Mg.Hides s o → M.finalsD (D.extend q₀ y) ss chs s = M.finalsD D ss chs s :=
  finalsWith_congr_oracle_of_hides fun s hs => by
    obtain ⟨a, ha⟩ := DB.mem_iff_lookup.1 (hrec s hs)
    show (((D.extend q₀ y).lookup (M.finalInputD D ss chs s)).getD defaultOut) =
      ((D.lookup (M.finalInputD D ss chs s)).getD defaultOut)
    rw [lookup_extend_of_lookup hq ha, ha]

/-- **A final input hidden from `o` stays** after recording a new answer, when the final inputs
hidden from `o` are recorded. -/
theorem finalInputD_extend (hq : q₀ ∉ D) {o : Mg.Obs} (hrec : M.FinalsRecorded D ss chs o)
    {s : Mg.Site} (hs : Mg.Hides s o) :
    M.finalInputD (D.extend q₀ y) ss chs s = M.finalInputD D ss chs s := by
  unfold finalInputD
  rw [finalContent_congr (fun _ _ => rfl) fun s' hs' =>
    M.finalsD_extend ss chs hq hrec s' (Merges.hides_of_hides_sink hs hs')]

/-- **Recorded final inputs stay recorded** after recording a new answer. -/
theorem finalsRecorded_extend (hq : q₀ ∉ D) {o : Mg.Obs} (hrec : M.FinalsRecorded D ss chs o) :
    M.FinalsRecorded (D.extend q₀ y) ss chs o := fun s hs => by
  rw [M.finalInputD_extend ss chs hq hrec hs]
  exact DB.mem_extend.2 (Or.inr (hrec s hs))

/-- **The chain input of leaf `p` stays** after recording a new answer, when the final inputs
hidden from `p` are recorded. -/
theorem inputD_extend (hq : q₀ ∉ D) {p : t.Leaf} (hrec : M.FinalsRecorded D ss chs (.leaf p))
    (l : M.Items p) : M.inputD (D.extend q₀ y) ss chs p l = M.inputD D ss chs p l := by
  unfold inputD
  rw [roundContent_congr (fun _ _ => rfl) fun s hs => M.finalsD_extend ss chs hq hrec s hs]

/-- **A key read from `D` stays** after recording a new answer. -/
theorem keyD_extend_of_eq_some (hq : q₀ ∉ D) {p : t.Leaf} {l : M.Items p} {a : Out k e}
    (h : M.keyD D ss chs p l = some a) : M.keyD (D.extend q₀ y) ss chs p l = some a := by
  unfold keyD at h ⊢
  split_ifs at h with hrec
  rw [ite_eq_left (M.finalsRecorded_extend ss chs hq hrec), M.inputD_extend ss chs hq hrec]
  exact lookup_extend_of_lookup hq h

/-- **A key read after recording `q₀ ↦ y` but not before** is the new answer at the chain input
itself, or the chain input holds `y`'s digest as the final digest of a branch whose final input is
`q₀`, so `y`'s digest is one of the final digests the recorded inputs hold (`pend`). -/
theorem keyD_extend (hq : q₀ ∉ D) {p : t.Leaf}
    (hwf : ∀ r, r.Before p → chainWF (P r.label) (chs r) ∧ (chs r).length = n r.label)
    {l : M.Items p} (hl : chainWF (P p.label) l) (hlen : l.length < n p.label) {a : Out k e}
    (h' : M.keyD (D.extend q₀ y) ss chs p l = some a) (h : M.keyD D ss chs p l ≠ some a) :
    (q₀ = M.inputD (D.extend q₀ y) ss chs p l ∧ a = y) ∨ y.digest ∈ M.pend D q₀ := by
  unfold keyD at h' h
  split_ifs at h' with hrec'
  by_cases hrec : M.FinalsRecorded D ss chs (.leaf p)
  · rw [ite_eq_left hrec] at h
    have he := M.inputD_extend (y := y) ss chs hq hrec l
    rw [he] at h'
    rcases (lookup_extend_eq_some_iff hq).1 h' with h1 | ⟨h1, h2⟩
    · exact absurd h1 h
    · exact Or.inl ⟨by rw [he]; exact h1.symm, h2⟩
  · have hne : (Finset.univ.filter fun s =>
        Mg.Hides s (.leaf p) ∧ M.finalInputD D ss chs s ∉ D).Nonempty := by
      by_contra hc
      refine hrec fun s hs => ?_
      by_contra hm
      exact hc ⟨s, Finset.mem_filter.2 ⟨Finset.mem_univ _, hs, hm⟩⟩
    obtain ⟨s, hsf, hmin⟩ :=
      Finset.exists_min_image _ (fun s => (Merges.hiders (M := Mg) (.sink s)).card) hne
    obtain ⟨-, hs, hnot⟩ := Finset.mem_filter.1 hsf
    have hrecs : M.FinalsRecorded D ss chs (.sink s) := fun s' hs' => by
      by_contra hm
      have hlt := Finset.card_lt_card (Merges.hiders_sink_ssubset hs')
      exact absurd (hmin s' (Finset.mem_filter.2 ⟨Finset.mem_univ _,
        Merges.hides_of_hides_sink hs hs', hm⟩)) (not_le.2 hlt)
    have hfin : M.finalInputD (D.extend q₀ y) ss chs s = M.finalInputD D ss chs s := by
      unfold finalInputD
      rw [finalContent_congr (fun _ _ => rfl) fun s' hs' => M.finalsD_extend ss chs hq hrecs s' hs']
    have hq₀ : q₀ = M.finalInputD D ss chs s := by
      have := hrec' s hs
      rw [hfin] at this
      rcases DB.mem_extend.1 this with h1 | h1
      · exact h1.symm
      · exact absurd h1 hnot
    have hds : M.finalsD (D.extend q₀ y) ss chs s = y.digest := by
      refine M.finalsD_eq_of_lookup (D.extend q₀ y) ss chs ?_
      rw [hfin, ← hq₀, DB.lookup_extend_self]
    by_cases hqr : q₀ = M.inputD (D.extend q₀ y) ss chs p l
    · refine Or.inl ⟨hqr, ?_⟩
      rw [← hqr, DB.lookup_extend_self] at h'
      exact (Option.some_inj.1 h').symm
    · right
      have hrD : M.inputD (D.extend q₀ y) ss chs p l ∈ D := by
        rcases DB.mem_extend.1 (DB.mem_iff_lookup.2 ⟨a, h'⟩) with h1 | h1
        · exact absurd h1.symm hqr
        · exact h1
      have hwfc := wf_roundContent_of_before ss (M.finalsD (D.extend q₀ y) ss chs) hwf hl hlen
      rw [hq₀]
      show y.digest ∈ M.finalDsAll D
      refine Finset.mem_biUnion.2 ⟨_, Finmap.mem_keys.2 hrD, ?_⟩
      simp only [inputD, finalDsOf, M.senc.decode_encode _ hwfc, Option.map_some, Option.getD_some]
      simp only [roundContent, Content.finalDs, Content.obs_round, Content.ds]
      refine Finset.mem_image.2 ⟨s, Merges.mem_hiders.2 hs, ?_⟩
      rw [Merges.Obs.viewDs_of_hides _ _ hs, hds]

/-- **A challenge read from `D` stays** after recording a new answer. -/
theorem extChal_extend_of_eq_some (hq : q₀ ∉ D) {q : t.Leaf} {l₀ : M.Items q} {d : Digest k}
    {i : (P q.label).ChallengeIdx} {v : (P q.label).Challenge i}
    (h : M.extChal D ss chs q l₀ d i = some v) :
    M.extChal (D.extend q₀ y) ss chs q l₀ d i = some v := by
  simp only [extChal, Option.bind_eq_some_iff] at h ⊢
  obtain ⟨a, ha, s, hs, hv⟩ := h
  exact ⟨a, M.keyD_extend_of_eq_some ss chs hq ha, s, lookup_extend_of_lookup hq hs, hv⟩

/-- If `D + [q₀ ↦ y]` reads a challenge that `D` does not, the digest of `y` is the absorbed
item, lies in `S(D)`, or is one of the final digests `pend D q₀`. -/
theorem digest_mem_of_extChal_extend (hq : q₀ ∉ D) {q : t.Leaf}
    (hwf : ∀ r, r.Before q → chainWF (P r.label) (chs r) ∧ (chs r).length = n r.label)
    {l₀ : M.Items q} (hl : chainWF (P q.label) l₀) (hlen : l₀.length < n q.label) {d : Digest k}
    {i : (P q.label).ChallengeIdx} {v : (P q.label).Challenge i}
    (h' : M.extChal (D.extend q₀ y) ss chs q l₀ d i = some v)
    (h : M.extChal D ss chs q l₀ d i ≠ some v) :
    y.digest = d ∨ y.digest ∈ halfPre M.senc.digestsOf D ∪ M.pend D q₀ := by
  simp only [extChal, Option.bind_eq_some_iff] at h'
  obtain ⟨a', ha', s', hs', hv⟩ := h'
  split_ifs at hv with hsd
  by_cases ha : M.keyD D ss chs q l₀ = some a'
  · cases hs : D.lookup (.xof a'.digest ss.salt) with
    | none =>
      obtain ⟨rfl, rfl⟩ := eq_of_lookup_extend hs hs'
      exact Or.inl hsd
    | some s =>
      obtain rfl : s' = s := Option.some_inj.1 ((lookup_extend_of_lookup hq hs).symm.trans hs').symm
      exact absurd (by simp [extChal, ha, hs, hsd, hv]) h
  · rcases M.keyD_extend ss chs hq hwf hl hlen ha' ha with ⟨hq₀, hay⟩ | hp
    · have hne : Query.xof a'.digest ss.salt ≠ q₀ := fun he => by
        rw [hq₀] at he
        simp [inputD] at he
      rw [DB.lookup_extend_of_ne hne] at hs'
      refine Or.inr (Finset.mem_union_left _ ?_)
      rw [← hay]
      exact key_mem_halfPre (DB.mem_iff_lookup.2 ⟨s', hs'⟩)
    · exact Or.inr (Finset.mem_union_right _ hp)

theorem digest_mem_of_extStep_extend (hq : q₀ ∉ D) (hcol : D.extend q₀ y ∉ digestCollision)
    {q : t.Leaf}
    (hwf : ∀ r, r.Before q → chainWF (P r.label) (chs r) ∧ (chs r).length = n r.label)
    {l : M.Items q} {r : ℕ} {hr : r < n q.label} (hpre : chainWF (P q.label) (l.take r))
    {v : (P q.label).Type ⟨r, hr⟩}
    (h' : M.extStep (D.extend q₀ y) ss chs q l r hr = some v) (h : M.extStep D ss chs q l r hr ≠ some v) :
    y.digest ∈ chainDigests (M.comp q.label).roots (l.take (r + 1)) ∪
      (halfPre M.senc.digestsOf D ∪ M.pend D q₀) := by
  unfold extStep at h h'
  split_ifs at h h' with hd
  · obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.1 h'
    rw [hw, Option.map_some] at h
    have hv : (M.comp q.label).views (D.extend q₀ y) ⟨⟨r, hr⟩, hd⟩ w ≠
        (M.comp q.label).views D ⟨⟨r, hr⟩, hd⟩ w := fun he => h (by rw [he])
    obtain ⟨it, hit, hw'⟩ := Option.bind_eq_some_iff.1 hw
    exact Finset.union_subset_union ((M.comp q.label).roots_subset_chainDigests hit hw')
      Finset.subset_union_left ((M.comp q.label).digest_mem_of_views_ne M.senc.digestsOf hq hcol hv)
  · obtain ⟨d, hdl, hc⟩ := Option.bind_eq_some_iff.1 h'
    rw [hdl] at h
    have h2 : M.extChal D ss chs q (l.take r) d ((P q.label).chIdx ⟨r, hr⟩ hd) ≠ some v := h
    obtain ⟨it, hit, hd'⟩ := Option.bind_eq_some_iff.1 hdl
    rcases M.digest_mem_of_extChal_extend ss chs hq hwf hpre
      ((List.length_take_le r l).trans_lt hr) hc h2 with he | he
    · refine Finset.mem_union_left _ (mem_chainDigests.2
        ⟨it, SPBCS.mem_take_succ_of_getElem? hit, ?_⟩)
      rw [Item.eq_absorb_of_getAbsorb hd', he]
      simp [Item.digests]
    · exact Finset.mem_union_right _ he

theorem digest_mem_of_extStep_extend_ne (hq : q₀ ∉ D) (hcol : D.extend q₀ y ∉ digestCollision)
    {q : t.Leaf} {l : M.Items q} {r : ℕ} {hr : r < n q.label} {v : (P q.label).Type ⟨r, hr⟩}
    (h : M.extStep D ss chs q l r hr = some v)
    (h' : M.extStep (D.extend q₀ y) ss chs q l r hr ≠ some v) :
    y.digest ∈ chainDigests (M.comp q.label).roots (l.take (r + 1)) ∪ halfPre M.senc.digestsOf D := by
  unfold extStep at h h'
  split_ifs at h h' with hd
  · obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.1 h
    rw [hw, Option.map_some] at h'
    have hv : (M.comp q.label).views (D.extend q₀ y) ⟨⟨r, hr⟩, hd⟩ w ≠
        (M.comp q.label).views D ⟨⟨r, hr⟩, hd⟩ w := fun he => h' (by rw [he])
    obtain ⟨it, hit, hw'⟩ := Option.bind_eq_some_iff.1 hw
    exact Finset.union_subset_union_left ((M.comp q.label).roots_subset_chainDigests hit hw')
      ((M.comp q.label).digest_mem_of_views_ne M.senc.digestsOf hq hcol hv)
  · exfalso
    obtain ⟨d, hdl, hc⟩ := Option.bind_eq_some_iff.1 h
    rw [hdl] at h'
    have h2 : M.extChal (D.extend q₀ y) ss chs q (l.take r) d ((P q.label).chIdx ⟨r, hr⟩ hd) ≠
        some v := h'
    exact h2 (M.extChal_extend_of_eq_some ss chs hq hc)

/-- **Extraction stability for one leaf** (CMS19 Lemma 8.8, p. 41). -/
theorem digest_mem_of_extLeaf_extend (hq : q₀ ∉ D) (hcol : D.extend q₀ y ∉ digestCollision)
    (q : t.Leaf)
    (hwf : ∀ r, r.Before q → chainWF (P r.label) (chs r) ∧ (chs r).length = n r.label)
    (l : M.Items q) :
    ∀ r (hr : r ≤ n q.label) {tr}, M.extLeaf (D.extend q₀ y) ss chs q l r hr = some tr →
      M.extLeaf D ss chs q l r hr ≠ some tr →
      y.digest ∈ chainDigests (M.comp q.label).roots (l.take r) ∪
        (halfPre M.senc.digestsOf D ∪ M.pend D q₀)
  | 0, _, _, h', h => absurd h' (by rw [extLeaf] at h ⊢; exact h)
  | r + 1, hr, tr, h', h => by
    rw [extLeaf_succ] at h' h
    obtain ⟨tr₀, h₀, hv⟩ := Option.bind_eq_some_iff.1 h'
    obtain ⟨v, hsv, rfl⟩ := Option.map_eq_some_iff.1 hv
    by_cases hD : M.extLeaf D ss chs q l r (by omega) = some tr₀
    · rw [hD, Option.bind_some] at h
      exact M.digest_mem_of_extStep_extend ss chs hq hcol hwf
        (M.chainWF_take_of_extLeaf (D.extend q₀ y) ss chs h₀) hsv
        fun hs => h (by rw [hs, Option.map_some])
    · have := digest_mem_of_extLeaf_extend hq hcol q hwf l r (by omega) h₀ hD
      exact Finset.union_subset_union_left
        (by simpa [List.take_take] using
          chainDigests_take_subset (M.comp q.label).roots (l.take (r + 1)) r)
        this

/-- `digest_mem_of_extLeaf_extend` in the converse direction. -/
theorem digest_mem_of_extLeaf_extend_ne (hq : q₀ ∉ D) (hcol : D.extend q₀ y ∉ digestCollision)
    (q : t.Leaf) (l : M.Items q) :
    ∀ r (hr : r ≤ n q.label) {tr}, M.extLeaf D ss chs q l r hr = some tr →
      M.extLeaf (D.extend q₀ y) ss chs q l r hr ≠ some tr →
      y.digest ∈ chainDigests (M.comp q.label).roots (l.take r) ∪ halfPre M.senc.digestsOf D
  | 0, _, _, h, h' => absurd h (by rw [extLeaf] at h' ⊢; exact h')
  | r + 1, hr, tr, h, h' => by
    rw [extLeaf_succ] at h' h
    obtain ⟨tr₀, h₀, hv⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨v, hsv, rfl⟩ := Option.map_eq_some_iff.1 hv
    by_cases hD : M.extLeaf (D.extend q₀ y) ss chs q l r (by omega) = some tr₀
    · rw [hD, Option.bind_some] at h'
      exact M.digest_mem_of_extStep_extend_ne ss chs hq hcol hsv
        fun hs => h' (by rw [hs, Option.map_some])
    · have := digest_mem_of_extLeaf_extend_ne hq hcol q l r (by omega) h₀ hD
      exact Finset.union_subset_union_left
        (by simpa [List.take_take] using
          chainDigests_take_subset (M.comp q.label).roots (l.take (r + 1)) r)
        this

/-- The digests carried by the chains of the leaves before `p` and by `p`'s own items `l`. -/
def pastDigests (p : t.Leaf) (l : M.Items p) : Finset (Digest k) :=
  ((Finset.univ.filter fun q : t.Leaf => q.Before p).biUnion fun q =>
    chainDigests (M.comp q.label).roots (chs q)) ∪ chainDigests (M.comp p.label).roots l

theorem chainDigests_own_subset (p : t.Leaf) (l : M.Items p) :
    chainDigests (M.comp p.label).roots l ⊆ M.pastDigests chs p l :=
  Finset.subset_union_right

theorem chainDigests_ctx_subset {p q : t.Leaf} (hq : q.Before p) (l : M.Items p) :
    chainDigests (M.comp q.label).roots (chs q) ⊆ M.pastDigests chs p l := fun _ hd =>
  Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨q, Finset.mem_filter.2 ⟨Finset.mem_univ _, hq⟩, hd⟩)

/-- **Extraction stability for a causal past**: if recording one new collision-free entry
changes the extracted causal past of `c` at own items `l` from full chains, the new digest is
carried by the chains of the past, lies in `S(D)`, or is one of the final digests `pend D q₀`. -/
theorem digest_mem_of_extPast_extend (hq : q₀ ∉ D) (hcol : D.extend q₀ y ∉ digestCollision)
    (c : ChIdx P t) (hfull : M.ChainsFull chs c.leaf) (l : M.Items c.leaf) {past : CausalPast P c}
    (h' : M.extPast (D.extend q₀ y) ss chs c l = some past) (h : M.extPast D ss chs c l ≠ some past) :
    y.digest ∈ M.pastDigests chs c.leaf l ∪ (halfPre M.senc.digestsOf D ∪ M.pend D q₀) := by
  obtain ⟨ctx', hctx', hown'⟩ := Option.bind_eq_some_iff.1 h'
  obtain ⟨own', hown'', rfl⟩ := Option.map_eq_some_iff.1 hown'
  have hwf : ∀ r, r.Before c.leaf → chainWF (P r.label) (chs r) ∧ (chs r).length = n r.label :=
    fun r hr => ⟨M.chainWF_of_extLeaf (D.extend q₀ y) ss chs ((optAll_eq_some.1 hctx') ⟨r, hr⟩)
      (hfull r hr), hfull r hr⟩
  by_cases hctx : M.extCtx D ss chs c.leaf = some ctx'
  · rw [extPast, hctx, Option.bind_some] at h
    have hne : M.extLeaf D ss chs c.leaf l c.idx.1 c.idx.1.2.le ≠ some own' := fun he =>
      h (by rw [he]; rfl)
    have := M.digest_mem_of_extLeaf_extend ss chs hq hcol c.leaf hwf l _ _ hown'' hne
    exact Finset.union_subset_union_left ((chainDigests_take_subset _ _ _).trans
      (M.chainDigests_own_subset chs c.leaf l)) this
  · obtain ⟨r, hr⟩ : ∃ r : {q : t.Leaf // q.Before c.leaf},
        M.extLeaf D ss chs r.1 (chs r.1) (n r.1.label) le_rfl ≠ some (ctx' r) := by
      by_contra hne
      push Not at hne
      exact hctx (optAll_eq_some.2 hne)
    have h1 := optAll_eq_some.1 hctx' r
    have := M.digest_mem_of_extLeaf_extend ss chs hq hcol r.1
      (fun r' hr' => hwf r' (hr'.trans r.2)) (chs r.1) _ _ h1 hr
    exact Finset.union_subset_union_left ((chainDigests_take_subset _ _ _).trans
      (M.chainDigests_ctx_subset chs r.2 l)) this

/-- `digest_mem_of_extPast_extend` in the converse direction. -/
theorem digest_mem_of_extPast_extend_ne (hq : q₀ ∉ D) (hcol : D.extend q₀ y ∉ digestCollision)
    (c : ChIdx P t) (l : M.Items c.leaf) {past : CausalPast P c}
    (h : M.extPast D ss chs c l = some past) (h' : M.extPast (D.extend q₀ y) ss chs c l ≠ some past) :
    y.digest ∈ M.pastDigests chs c.leaf l ∪ halfPre M.senc.digestsOf D := by
  obtain ⟨ctx, hctx, hown⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨own, hown', rfl⟩ := Option.map_eq_some_iff.1 hown
  by_cases hctx' : M.extCtx (D.extend q₀ y) ss chs c.leaf = some ctx
  · rw [extPast, hctx', Option.bind_some] at h'
    have hne : M.extLeaf (D.extend q₀ y) ss chs c.leaf l c.idx.1 c.idx.1.2.le ≠ some own :=
      fun he => h' (by rw [he]; rfl)
    have := M.digest_mem_of_extLeaf_extend_ne ss chs hq hcol c.leaf l _ _ hown' hne
    exact Finset.union_subset_union_left ((chainDigests_take_subset _ _ _).trans
      (M.chainDigests_own_subset chs c.leaf l)) this
  · obtain ⟨r, hr⟩ : ∃ r : {q : t.Leaf // q.Before c.leaf},
        M.extLeaf (D.extend q₀ y) ss chs r.1 (chs r.1) (n r.1.label) le_rfl ≠ some (ctx r) := by
      by_contra hne
      push Not at hne
      exact hctx' (optAll_eq_some.2 hne)
    have h1 := optAll_eq_some.1 hctx r
    have := M.digest_mem_of_extLeaf_extend_ne ss chs hq hcol r.1 (chs r.1) _ _ h1 hr
    exact Finset.union_subset_union_left ((chainDigests_take_subset _ _ _).trans
      (M.chainDigests_ctx_subset chs r.2 l)) this

end Stability

/-! ### The digests of a recorded past -/

section Recorded

variable {D chs}

/-- **The digests of a past whose chain input and final inputs are recorded lie in `S(D)`.** -/
theorem pastDigests_subset_halfPre {p : t.Leaf}
    (hwf : ∀ r, r.Before p → chainWF (P r.label) (chs r) ∧ (chs r).length = n r.label)
    {l : M.Items p} (hl : chainWF (P p.label) l) (hlen : l.length < n p.label) {a : Out k e}
    (ha : M.keyD D ss chs p l = some a) : M.pastDigests chs p l ⊆ halfPre M.senc.digestsOf D := by
  unfold keyD at ha
  split_ifs at ha with hrec
  have hin : M.inputD D ss chs p l ∈ D := DB.mem_iff_lookup.2 ⟨a, ha⟩
  have hwfc := wf_roundContent_of_before ss (M.finalsD D ss chs) hwf hl hlen
  have hround : (roundContent ss chs (M.finalsD D ss chs) p l).itemDigests
      (fun j => (M.comp j).roots) ⊆ halfPre M.senc.digestsOf D := fun u hu =>
    mem_halfPre_of_transcript hin (M.senc.digest_mem _ hwfc hu)
  intro u hu
  rcases Finset.mem_union.1 hu with hu | hu
  · obtain ⟨q, hqf, hu⟩ := Finset.mem_biUnion.1 hu
    have hqp : q.Before p := (Finset.mem_filter.1 hqf).2
    by_cases hv : (Merges.Obs.leaf p : Mg.Obs).Visible q
    · apply hround
      simp only [roundContent, Content.itemDigests]
      refine Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨q, Finset.mem_univ _, ?_⟩)
      rw [Merges.Obs.viewChains_of_visible _ _ hv]
      exact hu
    · obtain ⟨s, hs, hm⟩ := Merges.Obs.exists_hides_of_sees (o := .leaf p) hqp hv
      have hwff := wf_finalContent_of_sees ss (M.finalsD D ss chs) (s := s) fun r hr =>
        hwf r (Merges.sees_of_sees_sink hs hr)
      refine mem_halfPre_of_transcript (hrec s hs) (M.senc.digest_mem _ hwff ?_)
      simp only [finalContent, Content.itemDigests]
      refine Finset.mem_biUnion.2 ⟨q, Finset.mem_univ _, ?_⟩
      rw [Merges.Obs.viewChains_of_visible _ _ (Merges.visible_sink_of_mem hm)]
      exact hu
  · apply hround
    simp only [roundContent, Content.itemDigests]
    exact Finset.mem_union_right _ hu

/-- **Recorded final inputs with equal final digests read the same chains**: in a database without
a digest collision, two chains whose final inputs of a branch are recorded with the same final
digest agree on the leaves the branch's sink reads in full. -/
theorem eq_of_finalsD_eq (hcol : D ∉ digestCollision) {chs' : M.Chains} {s : Mg.Site}
    (hwf : ∀ q, (Merges.Obs.sink s : Mg.Obs).Sees q →
      chainWF (P q.label) (chs q) ∧ (chs q).length = n q.label)
    (hwf' : ∀ q, (Merges.Obs.sink s : Mg.Obs).Sees q →
      chainWF (P q.label) (chs' q) ∧ (chs' q).length = n q.label)
    (h₁ : M.finalInputD D ss chs s ∈ D) (h₂ : M.finalInputD D ss chs' s ∈ D)
    (hd : M.finalsD D ss chs s = M.finalsD D ss chs' s) :
    ∀ q, (Merges.Obs.sink s : Mg.Obs).Visible q → chs q = chs' q := by
  obtain ⟨a₁, ha₁⟩ := DB.mem_iff_lookup.1 h₁
  obtain ⟨a₂, ha₂⟩ := DB.mem_iff_lookup.1 h₂
  rw [M.finalsD_eq_of_lookup D ss chs ha₁, M.finalsD_eq_of_lookup D ss chs' ha₂] at hd
  have he := Query.transcript.inj (eq_of_lookup_digest_eq hcol ha₁ ha₂ hd)
  have hc := M.senc.encode_injective (wf_finalContent_of_sees ss _ hwf) (wf_finalContent_of_sees ss _ hwf') he
  obtain ⟨-, -, hch, -⟩ := Content.final.inj hc
  intro q hq
  have := congrFun hch q
  rwa [Merges.Obs.viewChains_of_visible _ _ hq, Merges.Obs.viewChains_of_visible _ _ hq] at this

/-- **A recorded chain input determines its salted statement, leaf, own items and past**: in a
database without a digest collision, two chains with full well-formed pasts whose chain inputs
are recorded with answers of the same digest have the same salted statement, leaf and own items,
and agree on the leaves before the leaf. -/
theorem eq_of_keyD_digest_eq (hcol : D ∉ digestCollision) {ss' : SaltedStatement kS X}
    {chs' : M.Chains} {p p' : t.Leaf}
    (hwf : ∀ r, r.Before p → chainWF (P r.label) (chs r) ∧ (chs r).length = n r.label)
    (hwf' : ∀ r, r.Before p' → chainWF (P r.label) (chs' r) ∧ (chs' r).length = n r.label)
    {l : M.Items p} {l' : M.Items p'} (hl : chainWF (P p.label) l) (hl' : chainWF (P p'.label) l')
    (hlen : l.length < n p.label) (hlen' : l'.length < n p'.label) {a a' : Out k e}
    (ha : M.keyD D ss chs p l = some a) (ha' : M.keyD D ss' chs' p' l' = some a')
    (hd : a.digest = a'.digest) :
    ss = ss' ∧ p = p' ∧ HEq l l' ∧ ∀ r, r.Before p → chs r = chs' r := by
  unfold keyD at ha ha'
  split_ifs at ha with hrec
  split_ifs at ha' with hrec'
  have he := Query.transcript.inj (eq_of_lookup_digest_eq hcol ha ha' hd)
  have hc := M.senc.encode_injective (wf_roundContent_of_before ss _ hwf hl hlen)
    (wf_roundContent_of_before ss' _ hwf' hl' hlen') he
  obtain ⟨rfl, rfl, hch, hds, hown⟩ := Content.round.inj hc
  refine ⟨rfl, rfl, hown, fun r hr => ?_⟩
  by_cases hv : (Merges.Obs.leaf p : Mg.Obs).Visible r
  · have := congrFun hch r
    rwa [Merges.Obs.viewChains_of_visible _ _ hv, Merges.Obs.viewChains_of_visible _ _ hv] at this
  · obtain ⟨s, hs, hm⟩ := Merges.Obs.exists_hides_of_sees (o := .leaf p) hr hv
    have hds' := congrFun hds s
    rw [Merges.Obs.viewDs_of_hides _ _ hs, Merges.Obs.viewDs_of_hides _ _ hs] at hds'
    exact M.eq_of_finalsD_eq ss hcol (fun q hq => hwf q (Merges.sees_of_sees_sink hs hq))
      (fun q hq => hwf' q (Merges.sees_of_sees_sink hs hq)) (hrec s hs) (hrec' s hs) hds' r
      (Merges.visible_sink_of_mem hm)

end Recorded

end

end GordieHowe.SPBCS
