-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Extractor
public import GordieHowe.Model.IOP.CausalSound
public import GordieHowe.Model.QROM.Lifting

@[expose] public section

/-!
# The instability bound of the database extractor

CMS19 Proposition 8.14 (p. 44) for the database extractor of the spBCS compiler
(`GordieHowe/SPBCS/Extractor.lean`, paper `lem:sse-instability`), from causal round-by-round
soundness (`CausalRBR`, `GordieHowe/Model/IOP/Causal.lean`).

`flipAt ss c chs l` (`P_σ ∩ P̄_{E,σ}` for the challenge `c`): the chains of the leaves before
`c.leaf` (`chs`, full) and `c`'s own items `l` (`|l| = c.idx`) give a chain input of `c` recorded
with its final inputs (`keyD`), the causal past of `c` is extracted from them, the stream at the
key and the salt is recorded and samples a challenge that moves `c`'s leaf state from false to
true (`FlipAt`) while the causal extractor fails on the past. `bad` is the union over salted
statements, challenges and chains: the knowledge failures of the paper's `lem:sse-instability`.

A fresh `xof` answer completes at most one challenge of one causal past: the key has one recorded
`transcript` preimage, which determines the salted statement, the leaf, the own items and, through
the recorded final inputs, the chains before the leaf (`eq_of_keyD_digest_eq`; `nextBad_unique`),
so the union costs nothing, and the challenge's own error `ε c` bounds the event (`CausalRBR.rbr`);
the bound is at the largest `ε c`. Every other change of the extraction puts the new digest among
the digests of a recorded input, of the query, or among the final digests the recorded inputs hold
(`digest_mem_of_extPast_extend`): at most `(max 2 c_in + nJ) · t` digests for a database of fewer
than `t` entries. This gives `I(bad | P̄_col, t) ≤ max_c ε c + (max 2 c_in + nJ) · t / 2^(8k)`
(`condInstab_bad_le`).
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm
open scoped ENNReal NNReal

variable {ι : Type} {t : SPTerm ι} {Mg : Merges t} {k kN kS L e : ℕ} {n : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (n j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] {X Wit : Type}

section

variable (M : SPBCS Mg P X k kN kS L e) (rel : Set (X × Wit)) (E : CausalExtractor P t X Wit)
  (S : CausalStateFn P t X)

/-- **The extracted causal past of `c` flips at the challenge `ch`**: the causal extractor fails
on the past and the leaf's state moves from false to true. -/
structure PastFlip (x : X) (c : ChIdx P t) (past : CausalPast P c) (ch : c.Challenge) : Prop where
  /-- The causal extractor fails on the past. -/
  extract_fails : (x, E c x past) ∉ rel
  /-- The leaf's state moves from false to true. -/
  flip : FlipAt S c x past ch

/-- `P_σ ∩ P̄_{E,σ}` at the challenge `c` (module docstring). -/
def flipAt (ss : SaltedStatement kS X) (c : ChIdx P t) (chs : M.Chains) (l : M.Items c.leaf) :
    Set (ODB k kN kS L e) :=
  {D | ∃ (past : CausalPast P c) (a s : Out k e) (ch : c.Challenge),
    M.ChainsFull chs c.leaf ∧ l.length = c.idx.1 ∧ M.extPast D ss chs c l = some past ∧
    M.keyD D ss chs c.leaf l = some a ∧ D.lookup (.xof a.digest ss.salt) = some s ∧
    ((M.comp c.leaf.label).sampler c.idx).sample s.stream = some ch ∧
    PastFlip rel E S ss.stmt c past ch}

/-- **The bad databases** (paper `lem:sse-instability`, the knowledge failures): the union of
`flipAt` over salted statements, challenges and chains. -/
def bad : Set (ODB k kN kS L e) :=
  {D | ∃ ss c chs l, D ∈ M.flipAt rel E S ss c chs l}

theorem empty_notMem_bad : (∅ : ODB k kN kS L e) ∉ M.bad rel E S := by
  rintro ⟨ss, c, chs, l, past, a, s, ch, -, -, -, ha, -⟩
  unfold keyD at ha
  split_ifs at ha
  simp [Finmap.lookup_empty] at ha

/-- The event that a fresh `xof` answer `y` at the query `q` completes the challenge `c` of an
extracted causal past whose chain input is recorded. -/
def nextBad (D : ODB k kN kS L e) (q : Query k kN kS L) (y : Out k e) : Prop :=
  ∃ (ss : SaltedStatement kS X) (c : ChIdx P t) (chs : M.Chains) (l : M.Items c.leaf)
    (past : CausalPast P c) (a : Out k e) (ch : c.Challenge),
    M.ChainsFull chs c.leaf ∧ l.length = c.idx.1 ∧ M.extPast D ss chs c l = some past ∧
    M.keyD D ss chs c.leaf l = some a ∧ q = .xof a.digest ss.salt ∧
    ((M.comp c.leaf.label).sampler c.idx).sample y.stream = some ch ∧
    PastFlip rel E S ss.stmt c past ch

variable {M rel E S} {D : ODB k kN kS L e} {q : Query k kN kS L} {y : Out k e}

/-- **The digests of an extracted past whose chain input is recorded lie in `S(D)`.** -/
theorem pastDigests_subset_halfPre_of_extPast {ss : SaltedStatement kS X} {c : ChIdx P t}
    {chs : M.Chains} {l : M.Items c.leaf} {past : CausalPast P c} {a : Out k e}
    (hfull : M.ChainsFull chs c.leaf) (hl : l.length = c.idx.1)
    (hp : M.extPast D ss chs c l = some past) (ha : M.keyD D ss chs c.leaf l = some a) :
    M.pastDigests chs c.leaf l ⊆ halfPre M.senc.digestsOf D := by
  obtain ⟨hwf, hlwf, hlen⟩ := M.wf_of_extPast D ss chs hfull hl hp
  exact M.pastDigests_subset_halfPre ss hwf hlwf hlen ha

/-- Flipping into `bad` (the first half of CMS19 Proposition 8.14, p. 44). -/
theorem flip_into_bad (hD : D ∉ M.bad rel E S) (hq : q ∉ D)
    (hcol : D.extend q y ∉ digestCollision) (h : D.extend q y ∈ M.bad rel E S) :
    y.digest ∈ halfPre M.senc.digestsOf D ∪ q.digests M.senc.digestsOf ∪ M.pend D q ∨
      M.nextBad rel E S D q y := by
  obtain ⟨ss, c, chs, l, past, a', s', ch, hfull, hl, hpast', ha', hs', hc, hflip⟩ := h
  obtain ⟨hwf, hlwf, hlen⟩ := M.wf_of_extPast (D.extend q y) ss chs hfull hl hpast'
  by_cases hpast : M.extPast D ss chs c l = some past
  · by_cases ha : M.keyD D ss chs c.leaf l = some a'
    · cases hs : D.lookup (.xof a'.digest ss.salt) with
      | none =>
        obtain ⟨rfl, rfl⟩ := eq_of_lookup_extend hs hs'
        exact Or.inr ⟨ss, c, chs, l, past, a', ch, hfull, hl, hpast, ha, rfl, hc, hflip⟩
      | some s =>
        obtain rfl : s' = s :=
          (Option.some_inj.1 ((lookup_extend_of_lookup hq hs).symm.trans hs')).symm
        exact absurd ⟨ss, c, chs, l, past, a', s', ch, hfull, hl, hpast, ha, hs, hc, hflip⟩ hD
    · refine Or.inl ?_
      rcases M.keyD_extend ss chs hq hwf hlwf hlen ha' ha with ⟨hq₀, hay⟩ | hp
      · have hne : Query.xof a'.digest ss.salt ≠ q := fun he => by
          rw [hq₀] at he
          simp [inputD] at he
        rw [DB.lookup_extend_of_ne hne] at hs'
        rw [← hay]
        exact Finset.mem_union_left _ (Finset.mem_union_left _
          (key_mem_halfPre (DB.mem_iff_lookup.2 ⟨s', hs'⟩)))
      · exact Finset.mem_union_right _ hp
  · have hmem := M.digest_mem_of_extPast_extend ss chs hq hcol c hfull l hpast' hpast
    refine Or.inl ?_
    rcases Finset.mem_union.1 hmem with hm | hm
    · have := halfPre_extend_subset
        (pastDigests_subset_halfPre_of_extPast hfull hl hpast' ha' hm)
      exact Finset.mem_union_left _ this
    · rcases Finset.mem_union.1 hm with hm | hm
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ hm)
      · exact Finset.mem_union_right _ hm

/-- Flipping out of `bad` (the second half of CMS19 Proposition 8.14, p. 45). -/
theorem flip_out_of_bad (hD : D ∈ M.bad rel E S) (hq : q ∉ D)
    (hcol : D.extend q y ∉ digestCollision) (h : D.extend q y ∉ M.bad rel E S) :
    y.digest ∈ halfPre M.senc.digestsOf D := by
  obtain ⟨ss, c, chs, l, past, a, s, ch, hfull, hl, hpast, ha, hs, hc, hflip⟩ := hD
  by_cases hpast' : M.extPast (D.extend q y) ss chs c l = some past
  · exact absurd ⟨ss, c, chs, l, past, a, s, ch, hfull, hl, hpast',
      M.keyD_extend_of_eq_some ss chs hq ha, lookup_extend_of_lookup hq hs, hc, hflip⟩ h
  · have hmem := M.digest_mem_of_extPast_extend_ne ss chs hq hcol c l hpast hpast'
    rcases Finset.mem_union.1 hmem with hm | hm
    · exact pastDigests_subset_halfPre_of_extPast hfull hl hpast ha hm
    · exact hm

/-- **In a collision-free database, `nextBad` determines its statement, challenge and past**: the
key has one recorded `transcript` preimage, which determines the salted statement, the leaf, the
own items and the chains before the leaf (`eq_of_keyD_digest_eq`). -/
theorem nextBad_unique (hcol : D ∉ digestCollision) {ss ss' : SaltedStatement kS X}
    {c c' : ChIdx P t} {chs chs' : M.Chains} {l : M.Items c.leaf}
    {l' : M.Items c'.leaf} {past : CausalPast P c} {past' : CausalPast P c'} {a a' : Out k e}
    (hfull : M.ChainsFull chs c.leaf) (hfull' : M.ChainsFull chs' c'.leaf)
    (hl : l.length = c.idx.1) (hl' : l'.length = c'.idx.1)
    (hp : M.extPast D ss chs c l = some past) (hp' : M.extPast D ss' chs' c' l' = some past')
    (ha : M.keyD D ss chs c.leaf l = some a) (ha' : M.keyD D ss' chs' c'.leaf l' = some a')
    (hq : q = .xof a.digest ss.salt) (hq' : q = .xof a'.digest ss'.salt) :
    ss.stmt = ss'.stmt ∧ c = c' ∧ HEq past past' := by
  obtain ⟨hd, -⟩ := Query.xof.inj (hq.symm.trans hq')
  obtain ⟨hwf, hlwf, hlen⟩ := M.wf_of_extPast D ss chs hfull hl hp
  obtain ⟨hwf', hlwf', hlen'⟩ := M.wf_of_extPast D ss' chs' hfull' hl' hp'
  obtain ⟨rfl, hleaf, hown, hagree⟩ :=
    M.eq_of_keyD_digest_eq ss hcol hwf hwf' hlwf hlwf' hlen hlen' ha ha' hd
  obtain ⟨p, i⟩ := c
  obtain ⟨p', i'⟩ := c'
  dsimp only at hleaf hown hl hl' hp hp' hagree
  subst hleaf
  obtain rfl := eq_of_heq hown
  obtain rfl : i = i' := Subtype.ext (Fin.ext (hl.symm.trans hl'))
  rw [M.extPast_congr D ss hagree, hp'] at hp
  exact ⟨rfl, rfl, heq_of_eq (Option.some_inj.1 hp).symm⟩

variable [∀ j i, Nonempty ((P j).Challenge i)] {ε : ChIdx P t → ℝ≥0}
  {claim : X → Prop} {claimOut : X → FullTr P t → Prop}

/-- **The `xof` case of the flip bound**: by the round-by-round bound of the unique challenge
and past, `Pr[nextBad] ≤ ε c ≤ max_c ε c`. -/
theorem prob_nextBad_le (hcol : D ∉ digestCollision) (hrbr : CausalRBR rel E S ε claim claimOut) :
    Pr[y ← Out k e : M.nextBad rel E S D q y] ≤ maxError ε := by
  by_cases hex : ∃ (ss : SaltedStatement kS X) (c : ChIdx P t) (chs : M.Chains)
      (l : M.Items c.leaf) (past : CausalPast P c) (a : Out k e), M.ChainsFull chs c.leaf ∧
      l.length = c.idx.1 ∧ M.extPast D ss chs c l = some past ∧
      M.keyD D ss chs c.leaf l = some a ∧ q = .xof a.digest ss.salt
  · obtain ⟨ss₀, c₀, chs₀, l₀, past₀, a₀, hf₀, hl₀, hp₀, ha₀, hq₀⟩ := hex
    let A : Set c₀.Challenge :=
      {ch | (ss₀.stmt, E c₀ ss₀.stmt past₀) ∉ rel ∧ FlipAt S c₀ ss₀.stmt past₀ ch}
    calc Pr[y ← Out k e : M.nextBad rel E S D q y]
        ≤ Pr[y ← Out k e : ∃ ch ∈ A, ((M.comp c₀.leaf.label).sampler c₀.idx).sample y.stream =
            some ch] := by
          refine QROM.probUniform_mono fun y hy => ?_
          obtain ⟨ss, c, chs, l, past, a, ch, hf, hl, hp, ha, hq, hc, hflip⟩ := hy
          obtain ⟨hx, rfl, hpp⟩ := nextBad_unique hcol hf hf₀ hl hl₀ hp hp₀ ha ha₀ hq hq₀
          obtain rfl := eq_of_heq hpp
          rw [hx] at hflip
          exact ⟨ch, ⟨hflip.extract_fails, hflip.flip⟩, hc⟩
      _ ≤ Pr[ch ← c₀.Challenge : ch ∈ A] := ((M.comp c₀.leaf.label).sampler c₀.idx).prob_mem_le A
      _ ≤ ε c₀ := hrbr.rbr c₀ ss₀.stmt past₀
      _ ≤ maxError ε := by exact_mod_cast le_maxError ε c₀
  · refine le_of_eq_of_le (probUniform_eq_zero fun y hy => hex ?_) zero_le
    obtain ⟨ss, c, chs, l, past, a, ch, hf, hl, hp, ha, hq, -⟩ := hy
    exact ⟨ss, c, chs, l, past, a, hf, hl, hp, ha, hq⟩

variable (M rel E S)

/-- `flip(bad | P̄_col, t) ≤ max_c ε c + (max 2 c_in + nJ) · t / 2^(8k)`. -/
theorem condFlip_bad_le (hrbr : CausalRBR rel E S ε claim claimOut) {tq : ℕ} :
    condFlip (M.bad rel E S) digestCollisionᶜ tq ≤
      maxError ε + (((max 2 M.senc.digestsPerInput + Mg.nJ) * tq : ℕ) : ENNReal) /
        2 ^ (8 * k) := by
  refine flipProb_le fun D hD hs q hq => ?_
  obtain ⟨hDb, hDc⟩ := hD
  have hDc' : D ∉ digestCollision := hDc
  set A := halfPre M.senc.digestsOf D ∪ q.digests M.senc.digestsOf ∪ M.pend D q with hA
  calc Pr[y ← Out k e : D.extend q y ∈ M.bad rel E S ∩ digestCollisionᶜ]
      ≤ Pr[y ← Out k e : y.digest ∈ A ∨ M.nextBad rel E S D q y] :=
        QROM.probUniform_mono fun y hy => flip_into_bad hDb hq hy.2 hy.1
    _ ≤ Pr[y ← Out k e : y.digest ∈ A] + Pr[y ← Out k e : M.nextBad rel E S D q y] :=
        probUniform_or_le _ _
    _ ≤ (((max 2 M.senc.digestsPerInput + Mg.nJ) * tq : ℕ) : ENNReal) / 2 ^ (8 * k) +
          maxError ε := by
        gcongr
        · rw [Out.probUniform_digest_mem]
          gcongr
          have h1 := M.card_pend_le D q
          have h2 := card_halfPre_union_le (digestsOf := M.senc.digestsOf) (D := D) (q := q)
            M.senc.card_digestsOf_le
          have h3 : (A.card : ℕ) ≤ max 2 M.senc.digestsPerInput * (D.size + 1) + Mg.nJ * D.size :=
            (Finset.card_union_le _ _).trans (Nat.add_le_add h2 h1)
          have h4 : max 2 M.senc.digestsPerInput * (D.size + 1) + Mg.nJ * D.size ≤
              (max 2 M.senc.digestsPerInput + Mg.nJ) * tq := by
            have hs1 : D.size + 1 ≤ tq := hs
            calc max 2 M.senc.digestsPerInput * (D.size + 1) + Mg.nJ * D.size
                ≤ max 2 M.senc.digestsPerInput * tq + Mg.nJ * tq :=
                  Nat.add_le_add (Nat.mul_le_mul_left _ hs1) (Nat.mul_le_mul_left _ (by omega))
              _ = _ := by ring
          exact_mod_cast h3.trans h4
        · exact prob_nextBad_le hDc' hrbr
    _ = _ := add_comm _ _

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- `flip(complement of bad | P̄_col, t) ≤ (max 2 c_in + nJ) · t / 2^(8k)`. -/
theorem condFlip_compl_bad_le {tq : ℕ} :
    condFlip (M.bad rel E S)ᶜ digestCollisionᶜ tq ≤
      (((max 2 M.senc.digestsPerInput + Mg.nJ) * tq : ℕ) : ENNReal) / 2 ^ (8 * k) := by
  refine flipProb_le fun D hD hs q hq => ?_
  rw [compl_compl] at hD
  obtain ⟨hDb, hDc⟩ := hD
  calc Pr[y ← Out k e : D.extend q y ∈ (M.bad rel E S)ᶜ ∩ digestCollisionᶜ]
      ≤ Pr[y ← Out k e : y.digest ∈ halfPre M.senc.digestsOf D] :=
        QROM.probUniform_mono fun y hy => flip_out_of_bad hDb hq hy.2 hy.1
    _ ≤ _ := by
        rw [Out.probUniform_digest_mem]
        gcongr
        have h2 := card_halfPre_le (digestsOf := M.senc.digestsOf) (D := D) M.senc.card_digestsOf_le
        have h4 : max 2 M.senc.digestsPerInput * D.size ≤
            (max 2 M.senc.digestsPerInput + Mg.nJ) * tq := by
          have hs1 : D.size ≤ tq := hs.le
          calc max 2 M.senc.digestsPerInput * D.size
              ≤ (max 2 M.senc.digestsPerInput + Mg.nJ) * D.size :=
                Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
            _ ≤ _ := Nat.mul_le_mul_left _ hs1
        exact_mod_cast h2.trans h4

/-- **The instability bound** (paper `lem:sse-instability`, CMS19 Proposition 8.14, conditional
part): `I(bad | P̄_col, t) ≤ max_c ε c + (max 2 c_in + nJ) · t / 2^(8k)`. -/
theorem condInstab_bad_le (hrbr : CausalRBR rel E S ε claim claimOut) {tq : ℕ} :
    condInstab (M.bad rel E S) digestCollisionᶜ tq ≤
      maxError ε + (((max 2 M.senc.digestsPerInput + Mg.nJ) * tq : ℕ) : ENNReal) /
        2 ^ (8 * k) :=
  max_le (M.condFlip_bad_le rel E S hrbr) ((M.condFlip_compl_bad_le rel E S).trans le_add_self)

/-- **The instability of the bad set** (paper `lem:sse-instability`): the databases with a digest
collision or a knowledge failure, `bad ∪ digestCollision`, have instability
`I(bad ∪ digestCollision, t) ≤ max_c ε c + (max 2 c_in + nJ + 1) · t / 2^(8k)`. CMS19
Proposition 5.12 (3), p. 24 (`instab_union_le`), splits it into the conditional bound
`condInstab_bad_le` and the collision bound `instab_digestCollision_le`. -/
theorem instab_bad_union_le (hrbr : CausalRBR rel E S ε claim claimOut) {tq : ℕ} :
    instab (M.bad rel E S ∪ digestCollision) tq ≤
      maxError ε + (((max 2 M.senc.digestsPerInput + Mg.nJ + 1) * tq : ℕ) : ENNReal) /
        2 ^ (8 * k) :=
  instab_union_le.trans <| (add_le_add (M.condInstab_bad_le rel E S hrbr)
    instab_digestCollision_le).trans_eq (by
      rw [add_assoc, ENNReal.div_add_div_same, ← Nat.cast_add, add_mul _ 1, one_mul])

end

end GordieHowe.SPBCS
