-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.FullPast.Extract
public import GordieHowe.Model.IOP.CausalSound

@[expose] public section

/-!
# The instability bound of the series–parallel base model

CMS19 Proposition 8.14 (p. 44) for the series–parallel base model (`GordieHowe.SPBCS.FullPast`,
`GordieHowe/SPBCS/FullPast/Model.lean`), from causal round-by-round soundness (`CausalRBR`,
`GordieHowe/Model/IOP/Causal.lean`).

`flipAt x σ c chs l` (`P_σ ∩ P̄_{E,σ}` for the challenge `c`): the chains of the leaves before
`c.leaf` (`chs`, full) and `c`'s own items `l` (`|l| = c.idx`) are recorded as the content of a
chain input, the causal past of `c` is extracted from them, the stream at the key and the salt is
recorded and samples a challenge that moves `c`'s leaf state from false to true (`FlipAt`) while
the causal extractor fails on the past. `badAny` is the union over statements, salts, challenges
and chains.

A fresh `xof` answer completes at most one challenge of one causal past: the key has one recorded
`transcript` preimage, which determines the statement, the salt, the leaf, the chains before it
and the own items (`CausalEncoding.encode_injective`; `nextBad_unique`), so the union costs
nothing, and the challenge's own error `ε c` bounds the event (`CausalRBR.rbr`); the bound is at
the largest `ε c`. Every other change of the extraction puts the new digest among the digests of a
recorded chain input or of the query (`digest_mem_of_extPast_extend`).
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm
open scoped ENNReal NNReal

variable {k kN kS L e : ℕ}

namespace FullPast

open Base

variable {ι : Type} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)] {t : SPTerm ι}
  {X Wit : Type} (M : FullPast P t X k kN kS L e) (rel : Set (X × Wit))
  (E : CausalExtractor P t X Wit) (S : CausalStateFn P t X)

/-- The chains of the leaves before `p` are full. -/
def ChainsFull (chs : (r : t.Leaf) → M.Items r) (p : t.Leaf) : Prop :=
  ∀ q, q.Before p → (chs q).length = n q.label

/-- **The extracted causal past of `c` flips at the challenge `ch`**: the causal extractor fails
on the past and the leaf's state moves from false to true. -/
structure PastFlip (x : X) (c : ChIdx P t) (past : CausalPast P c) (ch : c.Challenge) : Prop where
  /-- The causal extractor fails on the past. -/
  extract_fails : (x, E c x past) ∉ rel
  /-- The leaf's state moves from false to true. -/
  flip : FlipAt S c x past ch

/-- `P_σ ∩ P̄_{E,σ}` at the challenge `c` (module docstring). -/
def flipAt (x : X) (σ : FiatShamirSalt kS) (c : ChIdx P t) (chs : (r : t.Leaf) → M.Items r)
    (l : M.Items c.leaf) : Set (ODB k kN kS L e) :=
  {D | ∃ (past : CausalPast P c) (a s : Out k e) (ch : c.Challenge),
    M.ChainsFull chs c.leaf ∧ l.length = c.idx.1 ∧ M.extPast D x σ chs c l = some past ∧
    D.lookup (.transcript (M.inputAt x σ chs c.leaf l)) = some a ∧ D.lookup (.xof a.digest σ) = some s ∧
    ((M.comp c.leaf.label).sampler c.idx).sample s.stream = some ch ∧ PastFlip rel E S x c past ch}

/-- `∪ (P_σ ∩ P̄_{E,σ})` over statements, salts, challenges and chains. -/
def badAny : Set (ODB k kN kS L e) :=
  {D | ∃ x σ c chs l, D ∈ M.flipAt rel E S x σ c chs l}

theorem empty_notMem_badAny : (∅ : ODB k kN kS L e) ∉ M.badAny rel E S := by
  rintro ⟨x, σ, c, chs, l, past, a, s, ch, -, -, -, ha, -⟩
  simp [Finmap.lookup_empty] at ha

/-- The event that a fresh `xof` answer `y` at the query `q` completes the challenge `c` of an
extracted causal past whose chain input is recorded. -/
def nextBad (D : ODB k kN kS L e) (q : Query k kN kS L) (y : Out k e) : Prop :=
  ∃ (x : X) (σ : FiatShamirSalt kS) (c : ChIdx P t) (chs : (r : t.Leaf) → M.Items r)
    (l : M.Items c.leaf) (past : CausalPast P c) (a : Out k e) (ch : c.Challenge),
    M.ChainsFull chs c.leaf ∧ l.length = c.idx.1 ∧ M.extPast D x σ chs c l = some past ∧
    D.lookup (.transcript (M.inputAt x σ chs c.leaf l)) = some a ∧ q = .xof a.digest σ ∧
    ((M.comp c.leaf.label).sampler c.idx).sample y.stream = some ch ∧ PastFlip rel E S x c past ch

variable {D : ODB k kN kS L e} {q : Query k kN kS L} {y : Out k e}

/-- **The content of an extracted chain input is well formed.** -/
theorem wf_content_of_extPast {x : X} {σ : FiatShamirSalt kS} {c : ChIdx P t}
    {chs : (r : t.Leaf) → M.Items r} {l : M.Items c.leaf} {past : CausalPast P c}
    (hfull : M.ChainsFull chs c.leaf) (hl : l.length = c.idx.1)
    (h : M.extPast D x σ chs c l = some past) :
    (M.content c.leaf (M.ctxOfChains c.leaf chs) l).WF n fun j => chainWF (P j) := by
  obtain ⟨ctx, hctx, hown⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨own, hown', -⟩ := Option.map_eq_some_iff.1 hown
  refine ⟨fun r hr => ?_, fun r hr => ?_, fun r hr => chainsOf_of_not_before M _ hr, ?_, ?_⟩
  · have hr' : r.Before c.leaf := hr
    show chainWF _ (M.chainsOf _ r)
    rw [chainsOf_of_before M _ hr']
    exact M.chainWF_of_extLeaf D x σ chs ((optAll_eq_some.1 hctx) ⟨r, hr'⟩) (hfull r hr')
  · have hr' : r.Before c.leaf := hr
    show (M.chainsOf _ r).length = _
    rw [chainsOf_of_before M _ hr']
    exact hfull r hr'
  · exact M.chainWF_of_extLeaf D x σ chs hown' hl
  · show l.length < _
    rw [hl]
    exact c.idx.1.2

/-- The digests of the past lie in `S(D)` when its chain input is recorded. -/
theorem pastDigests_subset_halfPre {x : X} {σ : FiatShamirSalt kS} {c : ChIdx P t}
    {chs : (r : t.Leaf) → M.Items r} {l : M.Items c.leaf}
    (hwf : (M.content c.leaf (M.ctxOfChains c.leaf chs) l).WF n fun j => chainWF (P j))
    (h : Query.transcript (M.inputAt x σ chs c.leaf l) ∈ D) :
    M.pastDigests chs c.leaf l ⊆ halfPre M.enc.digestsOf D :=
  fun _ hu => mem_halfPre_of_transcript h (M.enc.digest_mem _ _ hwf hu)

/-- Flipping into `badAny` (the first half of CMS19 Proposition 8.14, p. 44). -/
theorem flip_into_bad (hD : D ∉ M.badAny rel E S) (hq : q ∉ D)
    (hcol : D.extend q y ∉ digestCollision) (h : D.extend q y ∈ M.badAny rel E S) :
    y.digest ∈ halfPre M.enc.digestsOf D ∪ q.digests M.enc.digestsOf ∨ M.nextBad rel E S D q y := by
  obtain ⟨x, σ, c, chs, l, past, a', s', ch, hfull, hl, hpast', ha', hs', hc, hflip⟩ := h
  have hwf := M.wf_content_of_extPast hfull hl hpast'
  have hkey : Query.transcript (M.inputAt x σ chs c.leaf l) ∈ D.extend q y :=
    DB.mem_iff_lookup.2 ⟨a', ha'⟩
  by_cases hpast : M.extPast D x σ chs c l = some past
  · cases ha : D.lookup (.transcript (M.inputAt x σ chs c.leaf l)) with
    | none =>
      obtain ⟨rfl, rfl⟩ := eq_of_lookup_extend ha ha'
      rw [DB.lookup_extend_of_ne (by simp)] at hs'
      exact Or.inl (Finset.mem_union_left _ (key_mem_halfPre (DB.mem_iff_lookup.2 ⟨s', hs'⟩)))
    | some a =>
      obtain rfl : a' = a :=
        (Option.some_inj.1 ((lookup_extend_of_lookup hq ha).symm.trans ha')).symm
      cases hs : D.lookup (.xof a'.digest σ) with
      | none =>
        obtain ⟨rfl, rfl⟩ := eq_of_lookup_extend hs hs'
        exact Or.inr ⟨x, σ, c, chs, l, past, a', ch, hfull, hl, hpast, ha, rfl, hc, hflip⟩
      | some s =>
        obtain rfl : s' = s :=
          (Option.some_inj.1 ((lookup_extend_of_lookup hq hs).symm.trans hs')).symm
        exact absurd ⟨x, σ, c, chs, l, past, a', s', ch, hfull, hl, hpast, ha, hs, hc, hflip⟩ hD
  · have hmem := M.digest_mem_of_extPast_extend x σ chs hq hcol c l hpast' hpast
    refine Or.inl ?_
    rcases Finset.mem_union.1 hmem with hm | hm
    · exact halfPre_extend_subset (M.pastDigests_subset_halfPre hwf hkey hm)
    · exact Finset.mem_union_left _ hm

/-- Flipping out of `badAny` (the second half of CMS19 Proposition 8.14, p. 45). -/
theorem flip_out_of_bad (hD : D ∈ M.badAny rel E S) (hq : q ∉ D)
    (hcol : D.extend q y ∉ digestCollision) (h : D.extend q y ∉ M.badAny rel E S) :
    y.digest ∈ halfPre M.enc.digestsOf D := by
  obtain ⟨x, σ, c, chs, l, past, a, s, ch, hfull, hl, hpast, ha, hs, hc, hflip⟩ := hD
  have hwf := M.wf_content_of_extPast hfull hl hpast
  by_cases hpast' : M.extPast (D.extend q y) x σ chs c l = some past
  · exact absurd ⟨x, σ, c, chs, l, past, a, s, ch, hfull, hl, hpast',
      lookup_extend_of_lookup hq ha, lookup_extend_of_lookup hq hs, hc, hflip⟩ h
  · have hmem := M.digest_mem_of_extPast_extend_ne x σ chs hq hcol c l hpast hpast'
    rcases Finset.mem_union.1 hmem with hm | hm
    · exact M.pastDigests_subset_halfPre hwf (DB.mem_iff_lookup.2 ⟨a, ha⟩) hm
    · exact hm

/-- **In a collision-free database, `nextBad` determines its statement, salt, challenge and
past**: the key has one recorded `transcript` preimage, which determines the content of the chain
input. -/
theorem nextBad_unique (hcol : D ∉ digestCollision) {x x' : X} {σ σ' : FiatShamirSalt kS}
    {c c' : ChIdx P t} {chs chs' : (r : t.Leaf) → M.Items r} {l : M.Items c.leaf}
    {l' : M.Items c'.leaf} {past : CausalPast P c} {past' : CausalPast P c'} {a a' : Out k e}
    (hfull : M.ChainsFull chs c.leaf) (hfull' : M.ChainsFull chs' c'.leaf)
    (hl : l.length = c.idx.1) (hl' : l'.length = c'.idx.1)
    (hp : M.extPast D x σ chs c l = some past) (hp' : M.extPast D x' σ' chs' c' l' = some past')
    (ha : D.lookup (.transcript (M.inputAt x σ chs c.leaf l)) = some a)
    (ha' : D.lookup (.transcript (M.inputAt x' σ' chs' c'.leaf l')) = some a')
    (hq : q = .xof a.digest σ) (hq' : q = .xof a'.digest σ') :
    x = x' ∧ c = c' ∧ HEq past past' := by
  obtain ⟨hd, rfl⟩ := Query.xof.inj (hq.symm.trans hq')
  have hb : M.inputAt x σ chs c.leaf l = M.inputAt x' σ chs' c'.leaf l' := by
    by_contra hne
    exact hcol ⟨_, DB.mem_iff_lookup.2 ⟨a, ha⟩, _, DB.mem_iff_lookup.2 ⟨a', ha'⟩,
      fun h => hne (Query.transcript.inj h), by rw [ha, ha']; simp [hd]⟩
  obtain ⟨hσx, hch⟩ := M.enc.encode_injective (M.wf_content_of_extPast hfull hl hp)
    (M.wf_content_of_extPast hfull' hl' hp') hb
  obtain ⟨-, rfl⟩ := SaltedStatement.mk.inj hσx
  obtain ⟨hleaf, hchains, hown⟩ := CausalChain.mk.inj hch
  obtain ⟨p, i⟩ := c
  obtain ⟨p', i'⟩ := c'
  dsimp only [content] at hleaf hchains hown hl hl' hp hp'
  subst hleaf
  obtain rfl := eq_of_heq hown
  obtain rfl : i = i' := Subtype.ext (Fin.ext (hl.symm.trans hl'))
  have hagree : ∀ r, r.Before p → chs r = chs' r := fun r hr => by
    have := congrFun hchains r
    rwa [chainsOf_of_before M _ hr, chainsOf_of_before M _ hr] at this
  rw [M.extPast_congr D x σ hagree, hp'] at hp
  exact ⟨rfl, rfl, heq_of_eq (Option.some_inj.1 hp).symm⟩

variable [∀ j i, Nonempty ((P j).Challenge i)] {ε : ChIdx P t → ℝ≥0}
  {claim : X → Prop} {claimOut : X → FullTr P t → Prop}

/-- **The `xof` case of the flip bound**: by the round-by-round bound of the unique challenge
and past, `Pr[nextBad] ≤ ε c ≤ max_c ε c`. -/
theorem prob_nextBad_le (hcol : D ∉ digestCollision) (hrbr : CausalRBR rel E S ε claim claimOut) :
    Pr[y ← Out k e : M.nextBad rel E S D q y] ≤ maxError ε := by
  by_cases hex : ∃ (x : X) (σ : FiatShamirSalt kS) (c : ChIdx P t) (chs : (r : t.Leaf) → M.Items r)
      (l : M.Items c.leaf) (past : CausalPast P c) (a : Out k e), M.ChainsFull chs c.leaf ∧
      l.length = c.idx.1 ∧ M.extPast D x σ chs c l = some past ∧
      D.lookup (.transcript (M.inputAt x σ chs c.leaf l)) = some a ∧ q = .xof a.digest σ
  · obtain ⟨x₀, σ₀, c₀, chs₀, l₀, past₀, a₀, hf₀, hl₀, hp₀, ha₀, hq₀⟩ := hex
    let A : Set c₀.Challenge := {ch | (x₀, E c₀ x₀ past₀) ∉ rel ∧ FlipAt S c₀ x₀ past₀ ch}
    calc Pr[y ← Out k e : M.nextBad rel E S D q y]
        ≤ Pr[y ← Out k e : ∃ ch ∈ A, ((M.comp c₀.leaf.label).sampler c₀.idx).sample y.stream =
            some ch] := by
          refine QROM.probUniform_mono fun y hy => ?_
          obtain ⟨x, σ, c, chs, l, past, a, ch, hf, hl, hp, ha, hq, hc, hflip⟩ := hy
          obtain ⟨rfl, rfl, hpp⟩ := M.nextBad_unique hcol hf hf₀ hl hl₀ hp hp₀ ha ha₀ hq hq₀
          obtain rfl := eq_of_heq hpp
          exact ⟨ch, ⟨hflip.extract_fails, hflip.flip⟩, hc⟩
      _ ≤ Pr[ch ← c₀.Challenge : ch ∈ A] := ((M.comp c₀.leaf.label).sampler c₀.idx).prob_mem_le A
      _ ≤ ε c₀ := hrbr.rbr c₀ x₀ past₀
      _ ≤ maxError ε := by exact_mod_cast le_maxError ε c₀
  · refine le_of_eq_of_le (probUniform_eq_zero fun y hy => hex ?_) zero_le
    obtain ⟨x, σ, c, chs, l, past, a, ch, hf, hl, hp, ha, hq, -⟩ := hy
    exact ⟨x, σ, c, chs, l, past, a, hf, hl, hp, ha, hq⟩

end FullPast

end GordieHowe.SPBCS
