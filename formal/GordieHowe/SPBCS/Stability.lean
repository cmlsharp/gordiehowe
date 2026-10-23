-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Cover

@[expose] public section

/-!
# Recording a fresh answer and the translated database with merges

How the translation of a database with merges (`GordieHowe/SPBCS/Translate.lean`) changes when one
fresh answer is recorded. A round input holds the final digests of the branches hidden from its
leaf and is read through the recorded final inputs whose answers have those digests; recording a
new answer can change such a reading only when the new answer is a final input whose digest is
one being looked for. `pend D q` is the set of those digests for a new query `q`: for a new final
input, the final digests held by the recorded inputs (`finalDsAll`); nothing for any other query.
A new round input reads only recorded answers: should its own answer have a digest it looks for,
the input it finds is itself, a round input, which resolves no branch.

**The extension lemma** (`trans_extend`): outside `pend D q`, the translation of `D` with the new
answer is the translation of `D`, with the translated query's answer recorded when `q` has a
translation. `pend D q` has at most `nJ · |D|` elements (`card_pend_le`): a content holds at most
`nJ` final digests (`Content.card_finalDs_le`). This gives the instability bound
`max_c ε c + (max 2 c_in + nJ) · t / 2^(8k)` (`condInstab_bad_le`, paper `lem:sse-instability`).
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm

variable {ι : Type} {t : SPTerm ι} {Mg : Merges t} {k kN kS L e : ℕ} {n : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (n j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] {X : Type}

section

variable (M : SPBCS Mg P X k kN kS L e)

/-! ### The digests a new answer must avoid -/

/-- The final digests held by a recorded input. -/
def finalDsOf : Query k kN kS L → Finset (Digest k)
  | .transcript b => ((M.senc.decode b).map Content.finalDs).getD ∅
  | _ => ∅

/-- **The final digests held by the recorded inputs.** -/
def finalDsAll (D : ODB k kN kS L e) : Finset (Digest k) := D.keys.biUnion M.finalDsOf

/-- **The digests a new answer at `q` must avoid** (module docstring). -/
def pend (D : ODB k kN kS L e) : Query k kN kS L → Finset (Digest k)
  | .transcript b =>
    match M.senc.decode b with
    | some (.final _ _ _ _) => M.finalDsAll D
    | _ => ∅
  | _ => ∅

theorem card_finalDsAll_le (D : ODB k kN kS L e) : (M.finalDsAll D).card ≤ Mg.nJ * D.size :=
  Finset.card_biUnion_le.trans ((Finset.sum_le_card_nsmul _ _ Mg.nJ fun q _ => by
    cases q with
    | transcript b =>
      simp only [finalDsOf]
      cases M.senc.decode b with
      | none => simp
      | some c => exact Content.card_finalDs_le c
    | _ => simp [finalDsOf]).trans (by simp [DB.size, mul_comm]))

/-- **The digests a new answer must avoid are at most `nJ · |D|`.** -/
theorem card_pend_le (D : ODB k kN kS L e) (q : Query k kN kS L) :
    (M.pend D q).card ≤ Mg.nJ * D.size := by
  cases q with
  | transcript b =>
    simp only [pend]
    split
    · exact M.card_finalDsAll_le D
    · exact Nat.zero_le _
  | _ => exact Nat.zero_le _

/-! ### Resolutions after recording one answer -/

section ResolveExtend

variable {M} {D : ODB k kN kS L e} {q : Query k kN kS L} {y : Out k e}
  (hq : q ∉ D) (hcol : D.extend q y ∉ digestCollision)
include hq hcol

/-- **A hidden branch resolves as before** unless the new answer is a final input with its final
digest. -/
theorem resolveSink_extend {ss : SaltedStatement kS X} {chs : M.Chains} {ds : Mg.Site → Digest k}
    {s : Mg.Site}
    (hb : ∀ b ss' s' chs' ds', q = .transcript b → M.senc.decode b = some (.final ss' s' chs' ds') →
      y.digest ≠ ds s) :
    M.resolveSink (D.extend q y) ss chs ds s = M.resolveSink D ss chs ds s := by
  unfold resolveSink
  by_cases hu : ∃ b, q = .transcript b ∧ y.digest = ds s
  · obtain ⟨b, rfl, hv⟩ := hu
    obtain ⟨h1, h2⟩ := findTr_extend_self hq hcol rfl
    rw [← hv, h1, h2, Option.bind_some, Option.bind_none]
    rcases hdec : M.senc.decode b with _ | c
    · rfl
    rcases c with ⟨ss', p, chs', ds', own⟩ | ⟨ss', s', chs', ds'⟩
    · rfl
    · exact absurd hv (hb b ss' s' chs' ds' rfl hdec)
  · rw [findTr_extend hq hcol fun b hb hd => hu ⟨b, hb, hd⟩]

variable (M q y) in
/-- **The new answer misses the digests the reading of a content looks for**: a new final input
misses the digests `V`. -/
def NoHit (V : Finset (Digest k)) : Prop :=
  ∀ b ss s chs ds, q = .transcript b → M.senc.decode b = some (.final ss s chs ds) → y.digest ∉ V

/-- **A content reads the same causal past** after recording a new answer that misses the
digests it looks for. -/
theorem fullChain_extend {c : M.MContent} (hn : M.NoHit q y c.finalDs) :
    M.fullChain (D.extend q y) c = M.fullChain D c := by
  rcases c with ⟨ss, p, chs, ds, own⟩ | ⟨ss, s, chs, ds⟩
  · simp only [fullChain, pastChains]
    congr 2
    congr 1
    funext s
    split_ifs with hs
    · exact resolveSink_extend hq hcol fun b ss' s' chs' ds' hb hd he =>
        hn b ss' s' chs' ds' hb hd (he ▸ Finset.mem_image_of_mem _ (Merges.mem_hiders.2 hs))
    · rfl
  · rfl

/-- **The pending digests cover what the readings of recorded inputs look for.** -/
theorem noHit_of_pend (hy : y.digest ∉ M.pend D q) : M.NoHit q y (M.finalDsAll D) := by
  intro b ss s chs ds hb hd hm
  subst hb
  apply hy
  simp only [pend, hd]
  exact hm

omit hq hcol in
/-- The final digests of a recorded input are among those of `D`. -/
theorem finalDs_subset_of_mem {b : Bytes L} {c : M.MContent} (hb : Query.transcript b ∈ D)
    (hc : M.senc.decode b = some c) : c.finalDs ⊆ M.finalDsAll D :=
  fun v hv => Finset.mem_biUnion.2 ⟨_, Finmap.mem_keys.2 hb, by simp [finalDsOf, hc, hv]⟩

/-- **A recorded query translates as before** after recording a new answer outside the pending
digests. -/
theorem φ_extend_of_mem (hy : y.digest ∉ M.pend D q) {q₀ : Query k kN kS L} (hq₀ : q₀ ∈ D) :
    M.φ (D.extend q y) q₀ = M.φ D q₀ := by
  cases q₀ with
  | transcript b₀ =>
    simp only [φ, fullOf]
    rcases hc : M.senc.decode b₀ with _ | c
    · rfl
    · simp only [Option.bind_some]
      rw [fullChain_extend hq hcol fun b' ss s chs ds hb' hd hm =>
        noHit_of_pend hq hcol hy b' ss s chs ds hb' hd (finalDs_subset_of_mem hq₀ hc hm)]
  | _ => rfl

/-- **The new query translates as before**: a new final input has no translation, and a new
round input finds itself at most, which resolves no branch. -/
theorem φ_extend_self : M.φ (D.extend q y) q = M.φ D q := by
  cases q with
  | transcript b =>
    simp only [φ, fullOf]
    rcases hc : M.senc.decode b with _ | c
    · rfl
    simp only [Option.bind_some]
    rcases c with ⟨ss', p, chs', ds', own⟩ | ⟨ss', s', chs', ds'⟩
    · rw [fullChain_extend hq hcol]
      intro b' ss s chs ds hb hd
      cases hb
      rw [hc] at hd
      cases hd
    · rfl
  | _ => rfl

/-- **The translation of the new query is a new query** of the translated database. -/
theorem φ_notMem_trans (hy : y.digest ∉ M.pend D q) {q' : Query k kN kS L}
    (hφ : M.φ D q = some q') : q' ∉ M.trans D := by
  have hD := notMem_digestCollision_of_extend hq hcol
  intro hm
  obtain ⟨q₁, hq₁, hφ₁⟩ := (DB.mem_image_iff (injOnKeys_φ hD)).1 hm
  have := injOnKeys_φ (M := M) hcol (DB.mem_extend.2 (Or.inr hq₁)) (DB.mem_extend.2 (Or.inl rfl))
    ((φ_extend_of_mem hq hcol hy hq₁).trans hφ₁) ((φ_extend_self hq hcol).trans hφ)
  exact hq (this ▸ hq₁)

/-- **The extension lemma** (module docstring): outside the pending digests, the translation of
`D` with the new answer is the translation of `D`, with the translated query's answer recorded
when the new query has a translation. -/
theorem trans_extend (hy : y.digest ∉ M.pend D q) :
    M.trans (D.extend q y) = match M.φ D q with
      | none => M.trans D
      | some q' => (M.trans D).extend q' y := by
  have hD := notMem_digestCollision_of_extend hq hcol
  have hL : ∀ q' y', (M.trans (D.extend q y)).lookup q' = some y' ↔
      (M.trans D).lookup q' = some y' ∨ (M.φ D q = some q' ∧ y' = y) := fun q' y' => by
    rw [trans, DB.lookup_image_eq_some_iff (injOnKeys_φ hcol), trans,
      DB.lookup_image_eq_some_iff (injOnKeys_φ hD)]
    constructor
    · rintro ⟨q₀, hq₀, hφ₀⟩
      rcases (lookup_extend_eq_some_iff hq).1 hq₀ with h | ⟨rfl, rfl⟩
      · exact Or.inl ⟨q₀, h, (φ_extend_of_mem hq hcol hy (Finmap.mem_of_lookup_eq_some h)).symm.trans hφ₀⟩
      · exact Or.inr ⟨(φ_extend_self hq hcol).symm.trans hφ₀, rfl⟩
    · rintro (⟨q₀, h, hφ₀⟩ | ⟨hφ, rfl⟩)
      · exact ⟨q₀, (lookup_extend_eq_some_iff hq).2 (Or.inl h),
          (φ_extend_of_mem hq hcol hy (Finmap.mem_of_lookup_eq_some h)).trans hφ₀⟩
      · exact ⟨q, DB.lookup_extend_self, (φ_extend_self hq hcol).trans hφ⟩
  refine Finmap.ext_lookup fun q' => Option.ext fun y' => ?_
  rw [hL]
  rcases hφ : M.φ D q with _ | q₀'
  · simp
  · have hf := φ_notMem_trans hq hcol hy hφ
    simp only [lookup_extend_eq_some_iff hf, Option.some.injEq]
    constructor
    · rintro (h | ⟨rfl, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨rfl, rfl⟩
    · rintro (h | ⟨rfl, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨rfl, rfl⟩

end ResolveExtend

/-! ### Collisions and digests of the translated database -/

section Digests

variable {M} {D : ODB k kN kS L e}

/-- **The translated database has no digest collision** when `D` has none: its answers are
answers of `D` at distinct queries. -/
theorem trans_notMem_digestCollision (hD : D ∉ digestCollision) : M.trans D ∉ digestCollision := by
  rintro ⟨q₁, h₁, q₂, h₂, hne, heq⟩
  obtain ⟨y₁, hy₁⟩ := Finmap.mem_iff.1 h₁
  obtain ⟨y₂, hy₂⟩ := Finmap.mem_iff.1 h₂
  obtain ⟨p₁, hp₁, hφ₁⟩ := (DB.lookup_image_eq_some_iff (injOnKeys_φ hD)).1 hy₁
  obtain ⟨p₂, hp₂, hφ₂⟩ := (DB.lookup_image_eq_some_iff (injOnKeys_φ hD)).1 hy₂
  rw [hy₁, hy₂] at heq
  refine hD ⟨p₁, Finmap.mem_of_lookup_eq_some hp₁, p₂, Finmap.mem_of_lookup_eq_some hp₂,
    fun he => hne ?_, by rw [hp₁, hp₂]; exact heq⟩
  rw [he] at hφ₁
  exact Option.some_inj.1 (hφ₁.symm.trans hφ₂)

/-- The item digests of a chain of a content are among the content's. -/
theorem chainDigests_subset_itemDigests {c : M.MContent} (q : t.Leaf) :
    chainDigests ((M.comp q.label).roots) (c.chains q) ⊆ c.itemDigests (fun j => (M.comp j).roots) := by
  rcases c with ⟨ss, p, chs, ds, own⟩ | ⟨ss, s, chs, ds⟩
  · simp only [Content.itemDigests, Content.chains]
    exact (Finset.subset_biUnion_of_mem (fun q : t.Leaf => chainDigests ((M.comp q.label).roots) (chs q))
      (Finset.mem_univ q)).trans Finset.subset_union_left
  · simp only [Content.itemDigests, Content.chains]
    exact Finset.subset_biUnion_of_mem (fun q : t.Leaf => chainDigests ((M.comp q.label).roots) (chs q))
      (Finset.mem_univ q)

/-- **A resolved branch's chains carry digests of a recorded input.** -/
theorem chainDigests_of_resolveSink (hD : D ∉ digestCollision) {ss : SaltedStatement kS X}
    {chs : M.Chains} {ds : Mg.Site → Digest k} {s : Mg.Site} {chs' : M.Chains}
    (h : M.resolveSink D ss chs ds s = some chs') (q : t.Leaf) :
    chainDigests ((M.comp q.label).roots) (chs' q) ⊆ halfPre M.senc.digestsOf D := by
  obtain ⟨⟨a, ha, -⟩, ss', ds', hdec⟩ := resolveSink_spec hD h
  have hwf := M.senc.wf_of_decode _ _ hdec
  have he := M.senc.encode_decode _ _ hdec
  refine (chainDigests_subset_itemDigests (c := .final ss' s chs' ds') q).trans fun u hu => ?_
  have hu' := M.senc.digest_mem _ hwf hu
  rw [he] at hu'
  exact mem_halfPre_of_transcript (Finmap.mem_of_lookup_eq_some ha) hu'

/-- **The digests of a translated content** are those of the recorded inputs it reads and of its
own items. -/
theorem digests_fullChain_subset (hD : D ∉ digestCollision) {c : M.MContent}
    {ss : SaltedStatement kS X}
    {ch : CausalChain t k fun j => (M.comp j).W} (h : M.fullChain D c = some (ss, ch)) :
    ch.digests (fun j => (M.comp j).roots) ⊆
      halfPre M.senc.digestsOf D ∪ c.itemDigests (fun j => (M.comp j).roots) := by
  rcases c with ⟨ss', p, chs, ds, own⟩ | ⟨ss', s, chs, ds⟩
  · obtain ⟨F, hF, he⟩ := fullChain_round h
    obtain ⟨-, rfl⟩ := Prod.mk.inj he
    obtain ⟨R, hR, rfl⟩ := pastChains_spec hF
    intro u hu
    simp only [CausalChain.digests, Base.content, Finset.mem_union, Finset.mem_biUnion,
      Finset.mem_univ, true_and] at hu
    rcases hu with ⟨q, hq⟩ | hu
    · unfold Base.chainsOf at hq
      split_ifs at hq with hb
      · dsimp only at hq
        have hb' : (Merges.Obs.leaf p : Mg.Obs).Sees q := hb
        by_cases hv : (Merges.Obs.leaf p : Mg.Obs).Visible q
        · rw [Merges.Obs.fill_of_visible hv] at hq
          exact Finset.mem_union_right _
            (chainDigests_subset_itemDigests (c := .round ss' p chs ds own) q hq)
        · obtain ⟨s, hs, hm⟩ := Merges.Obs.exists_hides_of_sees hb' hv
          rw [Merges.Obs.fill_of_hides hs hm] at hq
          exact Finset.mem_union_left _ (chainDigests_of_resolveSink hD (hR s hs) q hq)
      · simp [chainDigests] at hq
    · refine Finset.mem_union_right _ ?_
      simp only [Content.itemDigests]
      exact Finset.mem_union_right _ hu
  · exact absurd h (by simp [fullChain])

/-- **The digests of a translated query** are among those of the recorded inputs and of the
query itself. -/
theorem digests_φ_subset (hD : D ∉ digestCollision) {q q' : Query k kN kS L}
    (hφ : M.φ D q = some q') :
    q'.digests M.enc.digestsOf ⊆ halfPre M.senc.digestsOf D ∪ q.digests M.senc.digestsOf := by
  cases q with
  | leaf a b =>
    obtain rfl := Option.some_inj.1 hφ
    exact Finset.subset_union_right
  | node l r =>
    obtain rfl := Option.some_inj.1 hφ
    exact Finset.subset_union_right
  | xof u s =>
    obtain rfl := Option.some_inj.1 hφ
    exact Finset.subset_union_right
  | transcript b =>
    obtain ⟨c, ss, ch, hc, hf, rfl⟩ := φ_transcript_eq_some hφ
    have hwc := M.senc.wf_of_decode b c hc
    have hwf := wf_fullChain hD hwc hf
    intro u hu
    have hu' := digests_fullChain_subset hD hf (M.enc_digests_subset ss ch hwf hu)
    rcases Finset.mem_union.1 hu' with h | h
    · exact Finset.mem_union_left _ h
    · refine Finset.mem_union_right _ ?_
      show u ∈ M.senc.digestsOf b
      rw [← M.senc.encode_decode b c hc]
      exact M.senc.digest_mem c hwc h

/-- **The digests of the translated database's queries** are among those of the recorded
inputs. -/
theorem halfPre_trans_subset (hD : D ∉ digestCollision) :
    halfPre M.enc.digestsOf (M.trans D) ⊆ halfPre M.senc.digestsOf D := by
  intro u hu
  obtain ⟨q', hq', hu'⟩ := mem_halfPre.1 hu
  obtain ⟨q, hq, hφ⟩ := (DB.mem_image_iff (injOnKeys_φ hD)).1 hq'
  rcases Finset.mem_union.1 (digests_φ_subset hD hφ hu') with h | h
  · exact h
  · exact mem_halfPre.2 ⟨q, hq, h⟩

end Digests

/-! ### The instability bound with merges -/

section Instability

variable {Wit : Type} (rel : Set (X × Wit)) (E : CausalExtractor P t X Wit)
  (St : CausalStateFn P t X)

theorem trans_empty : M.trans (∅ : ODB k kN kS L e) = ∅ := by
  refine Finmap.ext_lookup fun q' => ?_
  rw [trans, DB.lookup_image, Finmap.lookup_empty]
  exact DB.select_eq_none_of_forall fun q y hq => by simp [Finmap.lookup_empty] at hq

/-- **The bad databases with merges**: those whose translation lies in `badAny` of the compiler
over the term (paper `lem:sse-instability`, the knowledge failures read through the final
digests). -/
def bad : Set (ODB k kN kS L e) := {D | M.trans D ∈ M.toFullPast.badAny rel E St}

theorem empty_notMem_bad : (∅ : ODB k kN kS L e) ∉ M.bad rel E St := by
  show M.trans ∅ ∉ _
  rw [trans_empty]
  exact M.toFullPast.empty_notMem_badAny rel E St

variable [∀ j i, Nonempty ((P j).Challenge i)] {ε : ChIdx P t → NNReal}
  {claim : X → Prop} {claimOut : X → FullTr P t → Prop}

/-- `flip(bad | P̄_col, t) ≤ max_c ε c + (max 2 c_in + nJ) · t / 2^(8k)`. -/
theorem condFlip_bad_le (hrbr : CausalRBR rel E St ε claim claimOut) {tq : ℕ} :
    condFlip (M.bad rel E St) digestCollisionᶜ tq ≤
      maxError ε + (((max 2 M.senc.digestsPerInput + Mg.nJ) * tq : ℕ) : ENNReal) /
        2 ^ (8 * k) := by
  refine flipProb_le fun D hD hs q hq => ?_
  obtain ⟨hDb, hDc⟩ := hD
  have hDc' : D ∉ digestCollision := hDc
  set A := M.pend D q ∪ (halfPre M.senc.digestsOf D ∪ q.digests M.senc.digestsOf) with hA
  calc Pr[y ← Out k e : D.extend q y ∈ M.bad rel E St ∩ digestCollisionᶜ]
      ≤ Pr[y ← Out k e : y.digest ∈ A ∨
          ∃ q', M.φ D q = some q' ∧ M.toFullPast.nextBad rel E St (M.trans D) q' y] := by
        refine QROM.probUniform_mono fun y hy => ?_
        obtain ⟨hyb, hyc⟩ := hy
        by_cases hyA : y.digest ∈ A
        · exact Or.inl hyA
        right
        have hyp : y.digest ∉ M.pend D q := fun h => hyA (Finset.mem_union_left _ h)
        have hext := trans_extend hq hyc hyp
        rcases hφ : M.φ D q with _ | q'
        · simp only [hφ] at hext
          exact absurd (show M.trans D ∈ M.toFullPast.badAny rel E St by rw [← hext]; exact hyb) hDb
        · simp only [hφ] at hext
          refine ⟨q', rfl, ?_⟩
          have hcol' : (M.trans D).extend q' y ∉ digestCollision := by
            rw [← hext]
            exact trans_notMem_digestCollision hyc
          rcases M.toFullPast.flip_into_bad rel E St hDb (φ_notMem_trans hq hyc hyp hφ) hcol'
              (by rw [← hext]; exact hyb) with h | h
          · exfalso
            apply hyA
            rcases Finset.mem_union.1 h with h | h
            · exact Finset.mem_union_right _ (Finset.mem_union_left _ (halfPre_trans_subset hDc' h))
            · exact Finset.mem_union_right _ (digests_φ_subset hDc' hφ h)
          · exact h
    _ ≤ Pr[y ← Out k e : y.digest ∈ A] +
          Pr[y ← Out k e : ∃ q', M.φ D q = some q' ∧ M.toFullPast.nextBad rel E St (M.trans D) q' y] :=
        probUniform_or_le _ _
    _ ≤ (((max 2 M.senc.digestsPerInput + Mg.nJ) * tq : ℕ) : ENNReal) / 2 ^ (8 * k) +
          maxError ε := by
        gcongr
        · rw [Out.probUniform_digest_mem]
          gcongr
          have h1 := M.card_pend_le D q
          have h2 := card_halfPre_union_le (digestsOf := M.senc.digestsOf) (D := D) (q := q)
            M.senc.card_digestsOf_le
          have h3 : (A.card : ℕ) ≤ Mg.nJ * D.size + max 2 M.senc.digestsPerInput * (D.size + 1) :=
            (Finset.card_union_le _ _).trans (Nat.add_le_add h1 h2)
          have h4 : Mg.nJ * D.size + max 2 M.senc.digestsPerInput * (D.size + 1) ≤
              (max 2 M.senc.digestsPerInput + Mg.nJ) * tq := by
            have hs1 : D.size + 1 ≤ tq := hs
            calc Mg.nJ * D.size + max 2 M.senc.digestsPerInput * (D.size + 1)
                ≤ Mg.nJ * tq + max 2 M.senc.digestsPerInput * tq :=
                  Nat.add_le_add (Nat.mul_le_mul_left _ (by omega)) (Nat.mul_le_mul_left _ hs1)
              _ = _ := by ring
          exact_mod_cast h3.trans h4
        · rcases hφ : M.φ D q with _ | q'
          · exact le_of_eq_of_le (probUniform_eq_zero fun y ⟨q', h, _⟩ => by cases h) zero_le
          · refine (QROM.probUniform_mono (E' := fun y => M.toFullPast.nextBad rel E St (M.trans D) q' y)
              fun y ⟨q'', h, hb⟩ => ?_).trans
              (M.toFullPast.prob_nextBad_le rel E St (q := q') (trans_notMem_digestCollision (M := M) hDc') hrbr)
            obtain rfl := Option.some_inj.1 h
            exact hb
    _ = _ := add_comm _ _

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- `flip(complement of bad | P̄_col, t) ≤ (max 2 c_in + nJ) · t / 2^(8k)`. -/
theorem condFlip_compl_bad_le {tq : ℕ} :
    condFlip (M.bad rel E St)ᶜ digestCollisionᶜ tq ≤
      (((max 2 M.senc.digestsPerInput + Mg.nJ) * tq : ℕ) : ENNReal) / 2 ^ (8 * k) := by
  refine flipProb_le fun D hD hs q hq => ?_
  rw [compl_compl] at hD
  obtain ⟨hDb, hDc⟩ := hD
  have hDc' : D ∉ digestCollision := hDc
  calc Pr[y ← Out k e : D.extend q y ∈ (M.bad rel E St)ᶜ ∩ digestCollisionᶜ]
      ≤ Pr[y ← Out k e : y.digest ∈ M.pend D q ∪ halfPre M.senc.digestsOf D] := by
        refine QROM.probUniform_mono fun y hy => ?_
        obtain ⟨hyb, hyc⟩ := hy
        by_cases hyp : y.digest ∈ M.pend D q
        · exact Finset.mem_union_left _ hyp
        refine Finset.mem_union_right _ ?_
        have hext := trans_extend hq hyc hyp
        rcases hφ : M.φ D q with _ | q'
        · simp only [hφ] at hext
          exact absurd (show M.trans (D.extend q y) ∈ M.toFullPast.badAny rel E St by rw [hext]; exact hDb) hyb
        · simp only [hφ] at hext
          have hcol' : (M.trans D).extend q' y ∉ digestCollision := by
            rw [← hext]
            exact trans_notMem_digestCollision hyc
          exact halfPre_trans_subset hDc' (M.toFullPast.flip_out_of_bad rel E St hDb
            (φ_notMem_trans hq hyc hyp hφ) hcol' (by rw [← hext]; exact hyb))
    _ ≤ _ := by
        rw [Out.probUniform_digest_mem]
        gcongr
        have h1 := M.card_pend_le D q
        have h2 := card_halfPre_le (digestsOf := M.senc.digestsOf) (D := D) M.senc.card_digestsOf_le
        have h3 := (Finset.card_union_le (M.pend D q) (halfPre M.senc.digestsOf D)).trans
          (Nat.add_le_add h1 h2)
        have h4 : Mg.nJ * D.size + max 2 M.senc.digestsPerInput * D.size ≤
            (max 2 M.senc.digestsPerInput + Mg.nJ) * tq := by
          have hs1 : D.size ≤ tq := hs.le
          calc Mg.nJ * D.size + max 2 M.senc.digestsPerInput * D.size
              ≤ Mg.nJ * tq + max 2 M.senc.digestsPerInput * tq :=
                Nat.add_le_add (Nat.mul_le_mul_left _ hs1) (Nat.mul_le_mul_left _ hs1)
            _ = _ := by ring
        exact_mod_cast h3.trans h4

/-- **The instability bound with merges** (paper `lem:sse-instability`, CMS19 Proposition 8.14,
conditional part, read through the final digests): `I(bad | P̄_col, t) ≤ max_c ε c +
(max 2 c_in + nJ) · t / 2^(8k)`. -/
theorem condInstab_bad_le (hrbr : CausalRBR rel E St ε claim claimOut) {tq : ℕ} :
    condInstab (M.bad rel E St) digestCollisionᶜ tq ≤
      maxError ε + (((max 2 M.senc.digestsPerInput + Mg.nJ) * tq : ℕ) : ENNReal) /
        2 ^ (8 * k) :=
  max_le (M.condFlip_bad_le rel E St hrbr) ((M.condFlip_compl_bad_le rel E St).trans le_add_self)

/-- **The instability of the bad set with merges** (paper `lem:sse-instability`): the databases
with a digest collision or a knowledge failure, `bad ∪ digestCollision`, have instability
`I(bad ∪ digestCollision, t) ≤ max_c ε c + (max 2 c_in + nJ + 1) · t / 2^(8k)`. CMS19
Proposition 5.12 (3), p. 24 (`instab_union_le`), splits it into the conditional bound
`condInstab_bad_le` and the collision bound `instab_digestCollision_le`. -/
theorem instab_bad_union_le (hrbr : CausalRBR rel E St ε claim claimOut) {tq : ℕ} :
    instab (M.bad rel E St ∪ digestCollision) tq ≤
      maxError ε + (((max 2 M.senc.digestsPerInput + Mg.nJ + 1) * tq : ℕ) : ENNReal) /
        2 ^ (8 * k) :=
  instab_union_le.trans <| (add_le_add (M.condInstab_bad_le rel E St hrbr)
    instab_digestCollision_le).trans_eq (by
      rw [add_assoc, ENNReal.div_add_div_same, ← Nat.cast_add, add_mul _ 1, one_mul])

end Instability

end

end GordieHowe.SPBCS
