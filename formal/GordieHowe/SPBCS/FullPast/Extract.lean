-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.FullPast.Model

@[expose] public section

/-!
# Extraction of causal pasts from an oracle database

CMS19 `BCSExtract` (p. 41) for the series–parallel base model
(`GordieHowe.SPBCS.FullPast`, `GordieHowe/SPBCS/FullPast/Model.lean`). The chains of all leaves are given as one function `chs`; leaf `q`'s
chain is read with keys at the chain inputs whose causal context is `chs` restricted to the leaves
before `q` (`ctxOfChains`).

* `extLeaf D x σ chs q l r`: the first `r` rounds of leaf `q`'s transcript read from its chain
  `l`: a prover round's message from the write and the Merkle views of `D` at its roots, a
  challenge round's challenge from the recorded key and stream of its chain input
  (`chal`) when the stream's digest is the absorbed item.
* `extCtx D x σ chs p`: the full transcripts of the leaves before `p`, each read from its chain;
  `extPast D x σ c chs l`: the causal past of the challenge `c` (the context and `c`'s own
  prefix read from `l`).
* Stability (CMS19 Lemma 8.8, p. 41): if recording one new collision-free entry changes the
  extraction, the new answer's digest is carried by the chains read or lies in `S(D)`
  (`digest_mem_of_extLeaf_extend`, `digest_mem_of_extPast_extend`, and the converse forms).
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm
open scoped ENNReal NNReal

variable {k kN kS L e : ℕ}

namespace ComponentModel

variable {m : ℕ} {P : ProtocolSpec m} [∀ i, Fintype (P.Challenge i)]
  [∀ i, DecidableEq (P.Challenge i)] (C : ComponentModel P k kN L e)

/-- The write of round `i` held by an item, if it is one. -/
def writeAt (i : P.MessageIdx) : Item k C.W → Option (C.MessageWrite i)
  | .write w => if h : w.1 = i then some (h ▸ w.2) else none
  | .absorb _ => none

theorem writeAt_write (i : P.MessageIdx) (w : C.MessageWrite i) :
    C.writeAt i (.write ⟨i, w⟩) = some w := by
  simp [writeAt]

theorem eq_write_of_writeAt {i : P.MessageIdx} {it : Item k C.W} {w : C.MessageWrite i}
    (h : C.writeAt i it = some w) : it = .write ⟨i, w⟩ := by
  cases it with
  | write w' =>
    obtain ⟨j, w'⟩ := w'
    simp only [writeAt] at h
    split_ifs at h with hj
    subst hj
    simp_all
  | absorb d => simp [writeAt] at h

/-- The Merkle views of round `i`'s trees read from `D`, at the roots of the write `w`. -/
def views (D : ODB k kN kS L e) (i : P.MessageIdx) (w : C.MessageWrite i) :
    (τ : Fin (C.nTrees i)) → MerkleView k kN L (C.nLeaves i τ) :=
  fun τ => view D (C.nLeaves i τ) (C.rootOf i w τ)

theorem rootOf_mem_roots (i : P.MessageIdx) (w : C.MessageWrite i) (τ : Fin (C.nTrees i)) :
    C.rootOf i w τ ∈ C.roots ⟨i, w⟩ :=
  Finset.mem_image_of_mem _ (Finset.mem_univ τ)

/-- A write item's roots are digests of the chain prefix that contains it. -/
theorem roots_subset_chainDigests {l : List (Item k C.W)} {r : ℕ} {i : P.MessageIdx}
    {w : C.MessageWrite i} {it : Item k C.W} (hit : l[r]? = some it) (hw : C.writeAt i it = some w) :
    C.roots ⟨i, w⟩ ⊆ chainDigests C.roots (l.take (r + 1)) := fun _ hu =>
  mem_chainDigests.2 ⟨it, SPBCS.mem_take_succ_of_getElem? hit, by
    rw [C.eq_write_of_writeAt hw]; exact hu⟩

/-- If recording `q ↦ y` (collision-free) changes the views of a round's trees at the roots of
`w`, the digest of `y` is one of those roots or lies in `S(D)`. -/
theorem digest_mem_of_views_ne {D : ODB k kN kS L e} {q : Query k kN kS L} {y : Out k e}
    (digestsOf : Bytes L → Finset (Digest k)) (hq : q ∉ D) (hcol : D.extend q y ∉ digestCollision)
    {i : P.MessageIdx} {w : C.MessageWrite i} (h : C.views (D.extend q y) i w ≠ C.views D i w) :
    y.digest ∈ C.roots ⟨i, w⟩ ∪ halfPre digestsOf D := by
  obtain ⟨τ, hτ⟩ : ∃ τ, C.views (D.extend q y) i w τ ≠ C.views D i w τ := by
    by_contra hne
    push Not at hne
    exact h (funext hne)
  have hmem := digest_mem_of_view_ne hq hcol digestsOf hτ
  rw [Finset.mem_insert] at hmem
  rcases hmem with hmem | hmem
  · exact Finset.mem_union_left _ (hmem ▸ C.rootOf_mem_roots i w τ)
  · exact Finset.mem_union_right _ hmem

end ComponentModel

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

namespace Base

variable {ι : Type} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)] {t : SPTerm ι}
  {X : Type} (M : Base P t X k kN kS L e)

/-- The causal context of leaf `q` in the chains `chs` of all leaves. -/
def ctxOfChains (q : t.Leaf) (chs : (r : t.Leaf) → M.Items r) : M.Ctx q := fun r => chs r.1

/-- The chain input of leaf `q` with own items `l` in the chains `chs`. -/
def inputAt (x : X) (σ : FiatShamirSalt kS) (chs : (r : t.Leaf) → M.Items r) (q : t.Leaf)
    (l : M.Items q) : Bytes L :=
  M.enc.encode ⟨σ, x⟩ (M.content q (M.ctxOfChains q chs) l)

variable (D : ODB k kN kS L e) (x : X) (σ : FiatShamirSalt kS) (chs : (r : t.Leaf) → M.Items r)

/-- The challenge `i` of leaf `q` read from `D` at the own items `l₀` and the absorbed digest
`d`: the key and the stream of the chain input are recorded, the stream's digest is `d`, and the
sampler accepts. -/
def chal (q : t.Leaf) (l₀ : M.Items q) (d : Digest k) (i : (P q.label).ChallengeIdx) :
    Option ((P q.label).Challenge i) :=
  (D.lookup (.transcript (M.inputAt x σ chs q l₀))).bind fun a =>
    (D.lookup (.xof a.digest σ)).bind fun s =>
      if s.digest = d then ((M.comp q.label).sampler i).sample s.stream else none

/-- Round `r` of leaf `q`'s transcript read from its chain `l`. -/
def step (q : t.Leaf) (l : M.Items q) (r : ℕ) (hr : r < n q.label) :
    Option ((P q.label).Type ⟨r, hr⟩) :=
  if hd : (P q.label).dir ⟨r, hr⟩ = .P_to_V then
    (l[r]?.bind ((M.comp q.label).writeAt ⟨⟨r, hr⟩, hd⟩)).map fun w =>
      (M.comp q.label).msg ⟨⟨r, hr⟩, hd⟩ w ((M.comp q.label).views D ⟨⟨r, hr⟩, hd⟩ w)
  else
    (l[r]?.bind Item.getAbsorb).bind fun d =>
      M.chal D x σ chs q (l.take r) d ((P q.label).chIdx ⟨r, hr⟩ hd)

/-- **The first `r` rounds of leaf `q`'s transcript** read from its chain `l` (CMS19 `BCSExtract`,
p. 41, for a leaf of the composite).

Running time: `r` calls of `step`, each at most two lookups and one encoding of a chain input,
or one Merkle view per tree of the round. This running time is argued here, not proved in Lean. -/
def extLeaf (q : t.Leaf) (l : M.Items q) : (r : ℕ) → (hr : r ≤ n q.label) →
    Option ((P q.label).Transcript ⟨r, by omega⟩)
  | 0, _ => some fun i => i.elim0
  | r + 1, hr => (extLeaf q l r (by omega)).bind fun tr =>
      (M.step D x σ chs q l r (by omega)).map ((P q.label).concat (m := ⟨r, by omega⟩) tr)

/-- **The full transcripts of the leaves before `p`**, each read from its chain. -/
def extCtx (p : t.Leaf) : Option (CausalCtx P p) :=
  optAll fun q : {q : t.Leaf // q.Before p} => M.extLeaf D x σ chs q.1 (chs q.1) (n q.1.label) le_rfl

/-- **The causal past of the challenge `c`** read from the chains `chs` and `c`'s own items `l`:
the context and the first `c.idx` rounds of `c`'s leaf. -/
def extPast (c : ChIdx P t) (l : M.Items c.leaf) : Option (CausalPast P c) :=
  (M.extCtx D x σ chs c.leaf).bind fun ctx =>
    (M.extLeaf D x σ chs c.leaf l c.idx.1 c.idx.1.2.le).map fun own => ⟨ctx, own⟩

theorem extLeaf_succ (q : t.Leaf) (l : M.Items q) (r : ℕ) (hr : r + 1 ≤ n q.label) :
    M.extLeaf D x σ chs q l (r + 1) hr = (M.extLeaf D x σ chs q l r (by omega)).bind fun tr =>
      (M.step D x σ chs q l r (by omega)).map ((P q.label).concat (m := ⟨r, by omega⟩) tr) := rfl

theorem step_take (q : t.Leaf) (l : M.Items q) {r m : ℕ} (hrm : r < m) (hr : r < n q.label) :
    M.step D x σ chs q (l.take m) r hr = M.step D x σ chs q l r hr := by
  have h1 : (l.take m)[r]? = l[r]? := List.getElem?_take_of_lt hrm
  have h2 : (l.take m).take r = l.take r := by rw [List.take_take, Nat.min_eq_left hrm.le]
  simp only [step, h1, h2]

theorem extLeaf_take (q : t.Leaf) (l : M.Items q) {m : ℕ} :
    ∀ r (hr : r ≤ n q.label), r ≤ m →
      M.extLeaf D x σ chs q (l.take m) r hr = M.extLeaf D x σ chs q l r hr
  | 0, _, _ => rfl
  | r + 1, hr, hrm => by
    rw [extLeaf_succ, extLeaf_succ, extLeaf_take q l r (by omega) (by omega),
      M.step_take D x σ chs q l (by omega : r < m)]

/-- A challenge round reads the absorbed item and the challenge at the key of its prefix. -/
theorem step_challenge (q : t.Leaf) (l : M.Items q) (i : (P q.label).ChallengeIdx) :
    M.step D x σ chs q l i.1 i.1.2 = (l[i.1.1]?.bind Item.getAbsorb).bind fun d =>
      M.chal D x σ chs q (l.take i.1) d i := by
  have hd : ¬ (P q.label).dir i.1 = .P_to_V := by simp [i.2]
  unfold step
  simp only [hd, ↓reduceDIte]
  rfl

/-- A prover round reads the write and the Merkle views at its roots. -/
theorem step_message (q : t.Leaf) (l : M.Items q) (i : (P q.label).MessageIdx) :
    M.step D x σ chs q l i.1 i.1.2 = (l[i.1.1]?.bind ((M.comp q.label).writeAt i)).map fun w =>
      (M.comp q.label).msg i w ((M.comp q.label).views D i w) := by
  unfold step
  simp only [i.2, ↓reduceDIte]
  rfl

/-- A round that is read fits its position of the chain. -/
theorem fits_of_step {q : t.Leaf} {l : M.Items q} {r : ℕ} {hr : r < n q.label}
    {v : (P q.label).Type ⟨r, hr⟩} (h : M.step D x σ chs q l r hr = some v) :
    ∃ it, l[r]? = some it ∧ Fits (P q.label) r it := by
  unfold step at h
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
    (h : ∀ r (hr : r < n q.label), (M.step D x σ chs q l r hr).isSome) :
    ∀ r (hr : r ≤ n q.label), (M.extLeaf D x σ chs q l r hr).isSome
  | 0, _ => rfl
  | r + 1, hr => by
    obtain ⟨tr, htr⟩ := Option.isSome_iff_exists.1 (extLeaf_isSome q l h r (by omega))
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (h r (by omega))
    rw [extLeaf_succ, htr, Option.bind_some, hv, Option.map_some]
    rfl

/-- The rounds of an extracted transcript are the extracted rounds. -/
theorem step_of_extLeaf (q : t.Leaf) (l : M.Items q) :
    ∀ r (hr : r ≤ n q.label) {tr}, M.extLeaf D x σ chs q l r hr = some tr →
      ∀ j (hj : j < r), M.step D x σ chs q l j (by omega) = some (tr ⟨j, hj⟩)
  | 0, _, _, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | r + 1, hr, tr, h, j, hj => by
    rw [extLeaf_succ] at h
    obtain ⟨tr₀, h₀, hv⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨v, hsv, rfl⟩ := Option.map_eq_some_iff.1 hv
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | rfl
    · rw [(P q.label).concat_apply_of_lt (m := ⟨r, by omega⟩) tr₀ v j hj']
      exact step_of_extLeaf q l r (by omega) h₀ j hj'
    · rw [(P q.label).concat_apply_last (m := ⟨j, by omega⟩) tr₀ v]
      exact hsv

/-- A chain of `r` items from which the first `r` rounds are read is well formed. -/
theorem chainWF_of_extLeaf {q : t.Leaf} {l : M.Items q} {r : ℕ} {hr : r ≤ n q.label}
    {tr : (P q.label).Transcript ⟨r, by omega⟩} (h : M.extLeaf D x σ chs q l r hr = some tr)
    (hl : l.length = r) : chainWF (P q.label) l := by
  intro j hj
  obtain ⟨it, hit, hf⟩ := M.fits_of_step D x σ chs (M.step_of_extLeaf D x σ chs q l r hr h j (hl ▸ hj))
  rw [List.getElem?_eq_getElem hj] at hit
  exact (Option.some_inj.1 hit) ▸ hf

/-! ### The extraction reads only the chains of the causal past -/

section Congr

variable {chs} {chs' : (r : t.Leaf) → M.Items r}

theorem extLeaf_congr {q : t.Leaf} (h : ∀ r, r.Before q → chs r = chs' r) (l : M.Items q) :
    ∀ r (hr : r ≤ n q.label), M.extLeaf D x σ chs q l r hr = M.extLeaf D x σ chs' q l r hr := by
  have hstep : M.step D x σ chs q l = M.step D x σ chs' q l := by
    funext r hr
    have hc : M.ctxOfChains q chs = M.ctxOfChains q chs' := funext fun r => h r.1 r.2
    simp only [step, chal, inputAt]
    rw [hc]
  intro r
  induction r with
  | zero => intro _; rfl
  | succ r ih => intro hr; rw [extLeaf_succ, extLeaf_succ, ih, hstep]

theorem extCtx_congr {p : t.Leaf} (h : ∀ r, r.Before p → chs r = chs' r) :
    M.extCtx D x σ chs p = M.extCtx D x σ chs' p := by
  unfold extCtx
  congr 1
  funext q
  rw [h q.1 q.2, M.extLeaf_congr D x σ (fun r hr => h r (hr.trans q.2))]

theorem extPast_congr {c : ChIdx P t} (h : ∀ r, r.Before c.leaf → chs r = chs' r)
    (l : M.Items c.leaf) : M.extPast D x σ chs c l = M.extPast D x σ chs' c l := by
  simp only [extPast, M.extCtx_congr D x σ h, M.extLeaf_congr D x σ h]

end Congr

/-! ### Stability of one leaf's extraction -/

section Stability

variable {D} {q₀ : Query k kN kS L} {y : Out k e}

theorem chal_extend_of_eq_some (hq : q₀ ∉ D) {q : t.Leaf} {l₀ : M.Items q} {d : Digest k}
    {i : (P q.label).ChallengeIdx} {v : (P q.label).Challenge i}
    (h : M.chal D x σ chs q l₀ d i = some v) : M.chal (D.extend q₀ y) x σ chs q l₀ d i = some v := by
  simp only [chal, Option.bind_eq_some_iff] at h ⊢
  obtain ⟨a, ha, s, hs, hv⟩ := h
  exact ⟨a, lookup_extend_of_lookup hq ha, s, lookup_extend_of_lookup hq hs, hv⟩

/-- If `D + [q₀ ↦ y]` reads a challenge that `D` does not, the digest of `y` is the absorbed
item or lies in `S(D)`. -/
theorem digest_mem_of_chal_extend (hq : q₀ ∉ D) {q : t.Leaf} {l₀ : M.Items q} {d : Digest k}
    {i : (P q.label).ChallengeIdx} {v : (P q.label).Challenge i}
    (h' : M.chal (D.extend q₀ y) x σ chs q l₀ d i = some v) (h : M.chal D x σ chs q l₀ d i ≠ some v) :
    y.digest = d ∨ y.digest ∈ halfPre M.enc.digestsOf D := by
  simp only [chal, Option.bind_eq_some_iff] at h'
  obtain ⟨a', ha', s', hs', hv⟩ := h'
  split_ifs at hv with hsd
  cases ha : D.lookup (.transcript (M.inputAt x σ chs q l₀)) with
  | none =>
    obtain ⟨rfl, rfl⟩ := eq_of_lookup_extend ha ha'
    rw [DB.lookup_extend_of_ne (by simp)] at hs'
    exact Or.inr (key_mem_halfPre (DB.mem_iff_lookup.2 ⟨s', hs'⟩))
  | some a =>
    obtain rfl : a' = a := Option.some_inj.1 ((lookup_extend_of_lookup hq ha).symm.trans ha').symm
    cases hs : D.lookup (.xof a'.digest σ) with
    | none =>
      obtain ⟨rfl, rfl⟩ := eq_of_lookup_extend hs hs'
      exact Or.inl hsd
    | some s =>
      obtain rfl : s' = s := Option.some_inj.1 ((lookup_extend_of_lookup hq hs).symm.trans hs').symm
      exact absurd (by simp [chal, ha, hs, hsd, hv]) h

theorem digest_mem_of_step_extend (hq : q₀ ∉ D) (hcol : D.extend q₀ y ∉ digestCollision)
    {q : t.Leaf} {l : M.Items q} {r : ℕ} {hr : r < n q.label} {v : (P q.label).Type ⟨r, hr⟩}
    (h' : M.step (D.extend q₀ y) x σ chs q l r hr = some v) (h : M.step D x σ chs q l r hr ≠ some v) :
    y.digest ∈ chainDigests (M.comp q.label).roots (l.take (r + 1)) ∪ halfPre M.enc.digestsOf D := by
  unfold step at h h'
  split_ifs at h h' with hd
  · obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.1 h'
    rw [hw, Option.map_some] at h
    have hv : (M.comp q.label).views (D.extend q₀ y) ⟨⟨r, hr⟩, hd⟩ w ≠
        (M.comp q.label).views D ⟨⟨r, hr⟩, hd⟩ w := fun he => h (by rw [he])
    obtain ⟨it, hit, hw'⟩ := Option.bind_eq_some_iff.1 hw
    exact Finset.union_subset_union_left ((M.comp q.label).roots_subset_chainDigests hit hw')
      ((M.comp q.label).digest_mem_of_views_ne M.enc.digestsOf hq hcol hv)
  · obtain ⟨d, hdl, hc⟩ := Option.bind_eq_some_iff.1 h'
    rw [hdl] at h
    have h2 : M.chal D x σ chs q (l.take r) d ((P q.label).chIdx ⟨r, hr⟩ hd) ≠ some v := h
    obtain ⟨it, hit, hd'⟩ := Option.bind_eq_some_iff.1 hdl
    rcases M.digest_mem_of_chal_extend x σ chs hq hc h2 with he | he
    · refine Finset.mem_union_left _ (mem_chainDigests.2
        ⟨it, SPBCS.mem_take_succ_of_getElem? hit, ?_⟩)
      rw [Item.eq_absorb_of_getAbsorb hd', he]
      simp [Item.digests]
    · exact Finset.mem_union_right _ he

theorem digest_mem_of_step_extend_ne (hq : q₀ ∉ D) (hcol : D.extend q₀ y ∉ digestCollision)
    {q : t.Leaf} {l : M.Items q} {r : ℕ} {hr : r < n q.label} {v : (P q.label).Type ⟨r, hr⟩}
    (h : M.step D x σ chs q l r hr = some v) (h' : M.step (D.extend q₀ y) x σ chs q l r hr ≠ some v) :
    y.digest ∈ chainDigests (M.comp q.label).roots (l.take (r + 1)) ∪ halfPre M.enc.digestsOf D := by
  unfold step at h h'
  split_ifs at h h' with hd
  · obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.1 h
    rw [hw, Option.map_some] at h'
    have hv : (M.comp q.label).views (D.extend q₀ y) ⟨⟨r, hr⟩, hd⟩ w ≠
        (M.comp q.label).views D ⟨⟨r, hr⟩, hd⟩ w := fun he => h' (by rw [he])
    obtain ⟨it, hit, hw'⟩ := Option.bind_eq_some_iff.1 hw
    exact Finset.union_subset_union_left ((M.comp q.label).roots_subset_chainDigests hit hw')
      ((M.comp q.label).digest_mem_of_views_ne M.enc.digestsOf hq hcol hv)
  · exfalso
    obtain ⟨d, hdl, hc⟩ := Option.bind_eq_some_iff.1 h
    rw [hdl] at h'
    have h2 : M.chal (D.extend q₀ y) x σ chs q (l.take r) d ((P q.label).chIdx ⟨r, hr⟩ hd) ≠
        some v := h'
    exact h2 (M.chal_extend_of_eq_some x σ chs hq hc)

/-- **Extraction stability for one leaf** (CMS19 Lemma 8.8, p. 41). -/
theorem digest_mem_of_extLeaf_extend (hq : q₀ ∉ D) (hcol : D.extend q₀ y ∉ digestCollision)
    (q : t.Leaf) (l : M.Items q) :
    ∀ r (hr : r ≤ n q.label) {tr}, M.extLeaf (D.extend q₀ y) x σ chs q l r hr = some tr →
      M.extLeaf D x σ chs q l r hr ≠ some tr →
      y.digest ∈ chainDigests (M.comp q.label).roots (l.take r) ∪ halfPre M.enc.digestsOf D
  | 0, _, _, h', h => absurd h' (by rw [extLeaf] at h ⊢; exact h)
  | r + 1, hr, tr, h', h => by
    rw [extLeaf_succ] at h' h
    obtain ⟨tr₀, h₀, hv⟩ := Option.bind_eq_some_iff.1 h'
    obtain ⟨v, hsv, rfl⟩ := Option.map_eq_some_iff.1 hv
    by_cases hD : M.extLeaf D x σ chs q l r (by omega) = some tr₀
    · rw [hD, Option.bind_some] at h
      exact M.digest_mem_of_step_extend x σ chs hq hcol hsv fun hs => h (by rw [hs, Option.map_some])
    · have := digest_mem_of_extLeaf_extend hq hcol q l r (by omega) h₀ hD
      exact Finset.union_subset_union_left
        (by simpa [List.take_take] using
          chainDigests_take_subset (M.comp q.label).roots (l.take (r + 1)) r)
        this

/-- `digest_mem_of_extLeaf_extend` in the converse direction. -/
theorem digest_mem_of_extLeaf_extend_ne (hq : q₀ ∉ D) (hcol : D.extend q₀ y ∉ digestCollision)
    (q : t.Leaf) (l : M.Items q) :
    ∀ r (hr : r ≤ n q.label) {tr}, M.extLeaf D x σ chs q l r hr = some tr →
      M.extLeaf (D.extend q₀ y) x σ chs q l r hr ≠ some tr →
      y.digest ∈ chainDigests (M.comp q.label).roots (l.take r) ∪ halfPre M.enc.digestsOf D
  | 0, _, _, h, h' => absurd h (by rw [extLeaf] at h' ⊢; exact h')
  | r + 1, hr, tr, h, h' => by
    rw [extLeaf_succ] at h' h
    obtain ⟨tr₀, h₀, hv⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨v, hsv, rfl⟩ := Option.map_eq_some_iff.1 hv
    by_cases hD : M.extLeaf (D.extend q₀ y) x σ chs q l r (by omega) = some tr₀
    · rw [hD, Option.bind_some] at h'
      exact M.digest_mem_of_step_extend_ne x σ chs hq hcol hsv
        fun hs => h' (by rw [hs, Option.map_some])
    · have := digest_mem_of_extLeaf_extend_ne hq hcol q l r (by omega) h₀ hD
      exact Finset.union_subset_union_left
        (by simpa [List.take_take] using
          chainDigests_take_subset (M.comp q.label).roots (l.take (r + 1)) r)
        this

end Stability

end Base

namespace FullPast

open Base

variable {ι : Type} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)] {t : SPTerm ι}
  {X : Type} (M : FullPast P t X k kN kS L e)

variable (D : ODB k kN kS L e) (x : X) (σ : FiatShamirSalt kS) (chs : (r : t.Leaf) → M.Items r)

/-! ### Stability of one leaf's extraction -/

section Stability

variable {D} {q₀ : Query k kN kS L} {y : Out k e}

/-- The digests carried by the chains of the leaves before `p` and by `p`'s own items `l`. -/
def pastDigests (p : t.Leaf) (l : M.Items p) : Finset (Digest k) :=
  CausalChain.digests (fun j => (M.comp j).roots) (M.content p (M.ctxOfChains p chs) l)

theorem chainDigests_own_subset (p : t.Leaf) (l : M.Items p) :
    chainDigests (M.comp p.label).roots l ⊆ M.pastDigests chs p l :=
  Finset.subset_union_right

theorem chainDigests_ctx_subset {p q : t.Leaf} (hq : q.Before p) (l : M.Items p) :
    chainDigests (M.comp q.label).roots (chs q) ⊆ M.pastDigests chs p l := by
  intro d hd
  refine Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨q, Finset.mem_univ _, ?_⟩)
  show d ∈ chainDigests _ (M.chainsOf (M.ctxOfChains p chs) q)
  rw [chainsOf_of_before M _ hq]
  exact hd

/-- **Extraction stability for a causal past**: if recording one new collision-free entry
changes the extracted causal past of `c` at own items `l`, the new digest is carried by the
chains of the past or lies in `S(D)`. -/
theorem digest_mem_of_extPast_extend (hq : q₀ ∉ D) (hcol : D.extend q₀ y ∉ digestCollision)
    (c : ChIdx P t) (l : M.Items c.leaf) {past : CausalPast P c}
    (h' : M.extPast (D.extend q₀ y) x σ chs c l = some past) (h : M.extPast D x σ chs c l ≠ some past) :
    y.digest ∈ M.pastDigests chs c.leaf l ∪ halfPre M.enc.digestsOf D := by
  obtain ⟨ctx', hctx', hown'⟩ := Option.bind_eq_some_iff.1 h'
  obtain ⟨own', hown'', rfl⟩ := Option.map_eq_some_iff.1 hown'
  by_cases hctx : M.extCtx D x σ chs c.leaf = some ctx'
  · rw [extPast, hctx, Option.bind_some] at h
    have hne : M.extLeaf D x σ chs c.leaf l c.idx.1 c.idx.1.2.le ≠ some own' := fun he =>
      h (by rw [he]; rfl)
    have := M.digest_mem_of_extLeaf_extend x σ chs hq hcol c.leaf l _ _ hown'' hne
    exact Finset.union_subset_union_left ((chainDigests_take_subset _ _ _).trans
      (M.chainDigests_own_subset chs c.leaf l)) this
  · obtain ⟨r, hr⟩ : ∃ r : {q : t.Leaf // q.Before c.leaf},
        M.extLeaf D x σ chs r.1 (chs r.1) (n r.1.label) le_rfl ≠ some (ctx' r) := by
      by_contra hne
      push Not at hne
      exact hctx (optAll_eq_some.2 hne)
    have h1 := optAll_eq_some.1 hctx' r
    have := M.digest_mem_of_extLeaf_extend x σ chs hq hcol r.1 (chs r.1) _ _ h1 hr
    refine Finset.union_subset_union_left ((chainDigests_take_subset _ _ _).trans
      (M.chainDigests_ctx_subset chs r.2 l)) this

/-- `digest_mem_of_extPast_extend` in the converse direction. -/
theorem digest_mem_of_extPast_extend_ne (hq : q₀ ∉ D) (hcol : D.extend q₀ y ∉ digestCollision)
    (c : ChIdx P t) (l : M.Items c.leaf) {past : CausalPast P c}
    (h : M.extPast D x σ chs c l = some past) (h' : M.extPast (D.extend q₀ y) x σ chs c l ≠ some past) :
    y.digest ∈ M.pastDigests chs c.leaf l ∪ halfPre M.enc.digestsOf D := by
  obtain ⟨ctx, hctx, hown⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨own, hown', rfl⟩ := Option.map_eq_some_iff.1 hown
  by_cases hctx' : M.extCtx (D.extend q₀ y) x σ chs c.leaf = some ctx
  · rw [extPast, hctx', Option.bind_some] at h'
    have hne : M.extLeaf (D.extend q₀ y) x σ chs c.leaf l c.idx.1 c.idx.1.2.le ≠ some own :=
      fun he => h' (by rw [he]; rfl)
    have := M.digest_mem_of_extLeaf_extend_ne x σ chs hq hcol c.leaf l _ _ hown' hne
    exact Finset.union_subset_union_left ((chainDigests_take_subset _ _ _).trans
      (M.chainDigests_own_subset chs c.leaf l)) this
  · obtain ⟨r, hr⟩ : ∃ r : {q : t.Leaf // q.Before c.leaf},
        M.extLeaf (D.extend q₀ y) x σ chs r.1 (chs r.1) (n r.1.label) le_rfl ≠ some (ctx r) := by
      by_contra hne
      push Not at hne
      exact hctx' (optAll_eq_some.2 hne)
    have h1 := optAll_eq_some.1 hctx r
    have := M.digest_mem_of_extLeaf_extend_ne x σ chs hq hcol r.1 (chs r.1) _ _ h1 hr
    exact Finset.union_subset_union_left ((chainDigests_take_subset _ _ _).trans
      (M.chainDigests_ctx_subset chs r.2 l)) this

end Stability

end FullPast

end GordieHowe.SPBCS
