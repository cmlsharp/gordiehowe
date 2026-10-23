-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Basic
public import GordieHowe.SPBCS.Extraction.TranscriptLookup
public import GordieHowe.SPBCS.Extraction.ChainProg
public import GordieHowe.SPBCS.FullPast.Extract

@[expose] public section

/-!
# Reading causal pasts through final digests: the database translation with merges

A database of the spBCS compiler (`GordieHowe/SPBCS/Basic.lean`) records chain inputs that hold,
for every branch hidden from their observer, the branch's final digest in place of the branch's
chains. Following each such digest once, through the recorded final input whose answer has that
digest, recovers the chains of the branch: the sink of a hidden branch reads its branch in full
(`Merges.visible_sink_of_mem`), and it reads the leaves before the branch as the observer does
(`Merges.visible_sink_iff`, `Merges.hides_sink_iff`). Re-encoding the recovered causal past with
the full-past compiler's encoding gives the chain input of the compiler over the term (`GordieHowe.SPBCS.FullPast`)
with the same answer, which carries the knowledge argument of the compiler over the term to the
spBCS compiler.

* `Merges.Obs.siteOf`: the hidden branch that contains a leaf an observer does not read in full
  (unique, `Merges.eq_of_hides`).
* `resolveSink D ss chs ds s`: branch `s`'s chains behind its final digest `ds s`, from the
  recorded `transcript` input whose answer has that digest, accepted only when it is the final
  input of `s` whose view is the observer's (chains `chs`, final digests `ds`) on the leaves before
  the branch.
* `fill o chs R`: the chains of the past of `o`: `chs` at the leaves `o` reads in full, the
  resolved chains `R s` at the leaves of each hidden branch `s`.
* `fullChain D c`: the salted statement and causal-model content of a round content; final inputs
  have none. `φ D`, `trans D`: the translated query and database.

Running time: `findTr` is one pass over the entries; `fullChain` follows at most `nJ` digests,
each one pass, one decode and one encoding, then one causal encoding; `trans` evaluates `φ`
`|D|²` times. This running time is argued here, not proved in Lean.
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm

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
  rw [fill, if_neg fun hv => not_exists_hides_of_visible hv hex, dif_pos hex, siteOf_eq hex hs hq]

theorem fill_of_not_sees {q : t.Leaf} (hq : ¬ o.Sees q) : o.fill chs R q = [] := by
  rw [fill, if_neg fun hv => hq hv.1, dif_neg fun h => hq (sees_of_exists_hides h)]

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
    · rw [fill, if_neg hv, dif_neg hex, fill, if_neg hv, dif_neg hex]

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

/-- **The salted statement and the causal past of a content** (module docstring): a round input
reads its past through `pastChains`; a final input has none. -/
def fullChain : M.MContent → Option (SaltedStatement kS X × CausalChain t k fun j => (M.comp j).W)
  | .round ss p chs ds own =>
    (M.pastChains D ss (.leaf p) chs ds).map fun F => (ss, M.content p (fun q => F q.1) own)
  | .final _ _ _ _ => none

/-- **The salted statement and the causal-model chain input of a content.** -/
def fullOf (c : M.MContent) : Option (SaltedStatement kS X × Bytes L) :=
  (M.fullChain D c).map fun r => (r.1, M.enc.encode r.1 r.2)

/-- **The translated query**: a chain input by `fullOf`; every other query stays. -/
def φ : Query k kN kS L → Option (Query k kN kS L)
  | .transcript b => (M.senc.decode b).bind fun c => (M.fullOf D c).map fun r => .transcript r.2
  | q => some q

/-- **The translated database**: the answers of `D` at the translated queries. -/
def trans : ODB k kN kS L e := D.image (M.φ D)

/-! ### What a resolution reads -/

section Spec

variable {M} {D : ODB k kN kS L e}

theorem resolveSink_eq_some_iff (hD : D ∉ digestCollision) {ss : SaltedStatement kS X}
    {chs : M.Chains} {ds : Mg.Site → Digest k} {s : Mg.Site} {chs' : M.Chains} :
    M.resolveSink D ss chs ds s = some chs' ↔
      ∃ a ss' ds', D.lookup (.transcript (M.senc.encode (M.finalAt ss chs ds s chs'))) = some a ∧
        a.digest = ds s ∧
        M.senc.decode (M.senc.encode (M.finalAt ss chs ds s chs')) = some (.final ss' s chs' ds') := by
  unfold resolveSink
  constructor
  · intro h0
    obtain ⟨b, hb, h1⟩ := Option.bind_eq_some_iff.1 h0
    obtain ⟨a, ha, had⟩ := (findTr_eq_some_iff hD).1 hb
    rcases hdec : M.senc.decode b with _ | c
    · simp [hdec] at h1
    rw [hdec] at h1
    rcases c with ⟨ss', p, chs₀, ds₀, own⟩ | ⟨ss', s', chs₀, ds₀⟩
    · simp at h1
    · by_cases he : s' = s ∧ M.senc.encode (M.finalAt ss chs ds s chs₀) = b
      · obtain ⟨rfl, he⟩ := he
        have h2 : chs₀ = chs' := by simpa [he] using h1
        subst h2
        exact ⟨a, ss', ds₀, he ▸ ha, had, he ▸ hdec⟩
      · simp [he] at h1
  · rintro ⟨a, ss', ds', ha, had, hdec⟩
    rw [← had, findTr_of_lookup hD ha, Option.bind_some, hdec]
    simp

/-- **A resolved branch is recorded**: its final input at the observer's view is recorded with
an answer of digest `ds s`, and the resolved chains are well formed on the branch. -/
theorem resolveSink_spec (hD : D ∉ digestCollision) {ss : SaltedStatement kS X}
    {chs : M.Chains} {ds : Mg.Site → Digest k} {s : Mg.Site} {chs' : M.Chains}
    (h : M.resolveSink D ss chs ds s = some chs') :
    (∃ a, D.lookup (.transcript (M.senc.encode (M.finalAt ss chs ds s chs'))) = some a ∧
      a.digest = ds s) ∧
    ∃ ss' ds', M.senc.decode (M.senc.encode (M.finalAt ss chs ds s chs')) =
      some (.final ss' s chs' ds') := by
  obtain ⟨a, ss', ds', ha, had, hdec⟩ := (resolveSink_eq_some_iff hD).1 h
  exact ⟨⟨a, ha, had⟩, ss', ds', hdec⟩

/-- **A resolved branch's chains are full and well formed on the branch.** -/
theorem resolveSink_wf (hD : D ∉ digestCollision) {ss : SaltedStatement kS X}
    {chs : M.Chains} {ds : Mg.Site → Digest k} {s : Mg.Site} {chs' : M.Chains}
    (h : M.resolveSink D ss chs ds s = some chs') {q : t.Leaf} (hq : Mg.mem s q) :
    chainWF (P q.label) (chs' q) ∧ (chs' q).length = n q.label := by
  obtain ⟨-, ss', ds', hdec⟩ := resolveSink_spec hD h
  have hwf := M.senc.wf_of_decode _ _ hdec
  have hv := hwf.viewWF
  exact ⟨hv.chains_wf q (Merges.visible_sink_of_mem hq),
    hv.chains_length q (Merges.visible_sink_of_mem hq)⟩

/-- **A resolved past**: the resolution of each hidden branch, filled in. -/
theorem pastChains_spec {ss : SaltedStatement kS X} {o : Mg.Obs} {chs : M.Chains}
    {ds : Mg.Site → Digest k} {F : M.Chains} (h : M.pastChains D ss o chs ds = some F) :
    ∃ R : Mg.Site → M.Chains, (∀ s, Mg.Hides s o → M.resolveSink D ss chs ds s = some (R s)) ∧
      F = o.fill (W := fun j => (M.comp j).W) chs R := by
  unfold pastChains at h
  obtain ⟨R, hR, rfl⟩ := Option.map_eq_some_iff.1 h
  refine ⟨R, fun s hs => ?_, rfl⟩
  have := (optAll_eq_some.1 hR) s
  simpa [hs] using this

/-- **The past of an observer resolved from well-formed content is full and well formed.** -/
theorem pastChains_wf (hD : D ∉ digestCollision) {ss : SaltedStatement kS X} {o : Mg.Obs}
    {chs : M.Chains} {ds : Mg.Site → Digest k}
    (hv : Content.ViewWF (W := fun j => (M.comp j).W) n (fun j => chainWF (P j)) o chs ds) {F : M.Chains}
    (h : M.pastChains D ss o chs ds = some F) {q : t.Leaf} (hq : o.Sees q) :
    chainWF (P q.label) (F q) ∧ (F q).length = n q.label := by
  obtain ⟨R, hR, rfl⟩ := pastChains_spec h
  by_cases hvq : o.Visible q
  · rw [Merges.Obs.fill_of_visible hvq]
    exact ⟨hv.chains_wf q hvq, hv.chains_length q hvq⟩
  · obtain ⟨s, hs, hm⟩ := Merges.Obs.exists_hides_of_sees hq hvq
    rw [Merges.Obs.fill_of_hides hs hm]
    exact resolveSink_wf hD (hR s hs) hm

/-- **A resolved past determines the final digests** of the hidden branches: two digest
functions, `0` off the hidden branches, whose resolved pasts agree on the past of the observer
are equal. -/
theorem eq_of_pastChains (hD : D ∉ digestCollision) {ss : SaltedStatement kS X} {o : Mg.Obs}
    {chs : M.Chains} {ds₁ ds₂ : Mg.Site → Digest k}
    (hz₁ : ∀ s, ¬ Mg.Hides s o → ds₁ s = 0) (hz₂ : ∀ s, ¬ Mg.Hides s o → ds₂ s = 0)
    {F₁ F₂ : M.Chains} (h₁ : M.pastChains D ss o chs ds₁ = some F₁)
    (h₂ : M.pastChains D ss o chs ds₂ = some F₂) (hF : ∀ q, o.Sees q → F₁ q = F₂ q) :
    ds₁ = ds₂ := by
  obtain ⟨R₁, hR₁, rfl⟩ := pastChains_spec h₁
  obtain ⟨R₂, hR₂, rfl⟩ := pastChains_spec h₂
  have hRq : ∀ s, Mg.Hides s o → ∀ q, Mg.mem s q → R₁ s q = R₂ s q := fun s hs q hq => by
    have := hF q (Merges.sees_of_hides_of_mem hs hq)
    rwa [Merges.Obs.fill_of_hides hs hq, Merges.Obs.fill_of_hides hs hq] at this
  have key : ∀ c s, Mg.Hides s o → (Merges.hiders (M := Mg) (.sink s)).card = c → ds₁ s = ds₂ s := by
    intro c
    induction c using Nat.strong_induction_on with
    | _ c ih =>
      intro s hs hc
      obtain ⟨⟨a₁, ha₁, hd₁⟩, -⟩ := resolveSink_spec hD (hR₁ s hs)
      obtain ⟨⟨a₂, ha₂, hd₂⟩, -⟩ := resolveSink_spec hD (hR₂ s hs)
      have hfin : M.finalAt ss chs ds₁ s (R₁ s) = M.finalAt ss chs ds₂ s (R₂ s) := by
        unfold finalAt
        congr 1
        · refine Merges.Obs.viewChains_congr _ fun q _ => ?_
          unfold Merges.merged
          split_ifs with hq
          · exact hRq s hs q hq
          · rfl
        · refine Merges.Obs.viewDs_congr _ fun s' hs' => ?_
          have hlt := Finset.card_lt_card (Merges.hiders_sink_ssubset hs')
          rw [hc] at hlt
          exact ih _ hlt s' (Merges.hides_of_hides_sink hs hs') rfl
      rw [hfin] at ha₁
      obtain rfl : a₁ = a₂ := Option.some_inj.1 (ha₁.symm.trans ha₂)
      exact hd₁.symm.trans hd₂
  funext s
  by_cases hs : Mg.Hides s o
  · exact key _ s hs rfl
  · rw [hz₁ s hs, hz₂ s hs]

end Spec

/-! ### The translated contents -/

section Full

variable {M} {D : ODB k kN kS L e}

theorem fullChain_round {ss : SaltedStatement kS X} {p : t.Leaf} {chs : M.Chains}
    {ds : Mg.Site → Digest k} {own : M.Items p}
    {r : SaltedStatement kS X × CausalChain t k fun j => (M.comp j).W}
    (h : M.fullChain D (.round ss p chs ds own) = some r) :
    ∃ F, M.pastChains D ss (.leaf p) chs ds = some F ∧ r = (ss, M.content p (fun q => F q.1) own) := by
  simp only [fullChain] at h
  obtain ⟨F, hF, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨F, hF, rfl⟩

theorem fullChain_final {ss : SaltedStatement kS X} {s : Mg.Site} {chs : M.Chains}
    {ds : Mg.Site → Digest k} : M.fullChain D (.final ss s chs ds) = none := rfl

/-- **A translated content is well formed.** -/
theorem wf_fullChain (hD : D ∉ digestCollision) {c : M.MContent}
    (hc : c.WF n fun j => chainWF (P j)) {ss : SaltedStatement kS X}
    {ch : CausalChain t k fun j => (M.comp j).W} (h : M.fullChain D c = some (ss, ch)) :
    ch.WF n fun j => chainWF (P j) := by
  cases hc with
  | @round ss' p chs ds own hv hown hlen =>
    obtain ⟨F, hF, he⟩ := fullChain_round h
    obtain ⟨-, rfl⟩ := Prod.mk.inj he
    exact {
      chains_wf := fun q hq => by
        simp only [Base.content, Base.chainsOf] at hq ⊢
        rw [dite_eq_left hq]
        exact (pastChains_wf hD hv hF hq).1
      chains_length := fun q hq => by
        simp only [Base.content, Base.chainsOf] at hq ⊢
        rw [dite_eq_left hq]
        exact (pastChains_wf hD hv hF hq).2
      chains_nil := fun q hq => by
        simp only [Base.content]
        exact Base.chainsOf_of_not_before _ _ hq
      own_wf := hown
      own_length := hlen }
  | final _ => exact absurd h (by simp [fullChain])

/-- **The translation is injective on well-formed contents.** -/
theorem fullChain_inj (hD : D ∉ digestCollision) {c₁ c₂ : M.MContent}
    (hc₁ : c₁.WF n fun j => chainWF (P j)) (hc₂ : c₂.WF n fun j => chainWF (P j))
    {r : SaltedStatement kS X × CausalChain t k fun j => (M.comp j).W}
    (h₁ : M.fullChain D c₁ = some r) (h₂ : M.fullChain D c₂ = some r) : c₁ = c₂ := by
  cases hc₁ with
  | final _ => exact absurd h₁ (by simp [fullChain])
  | @round ss₁ p₁ chs₁ ds₁ own₁ hv₁ _ _ =>
  cases hc₂ with
  | final _ => exact absurd h₂ (by simp [fullChain])
  | @round ss₂ p₂ chs₂ ds₂ own₂ hv₂ _ _ =>
  obtain ⟨F₁, hF₁, rfl⟩ := fullChain_round h₁
  obtain ⟨F₂, hF₂, he⟩ := fullChain_round h₂
  obtain ⟨rfl, hch⟩ := Prod.mk.inj he
  simp only [Base.content, CausalChain.mk.injEq] at hch
  obtain ⟨rfl, hcs, ho⟩ := hch
  obtain rfl := eq_of_heq ho
  have hcs' : ∀ q, q.Before p₁ → F₁ q = F₂ q := fun q hq => by
    have := congrFun hcs q
    rwa [Base.chainsOf_of_before _ _ hq, Base.chainsOf_of_before _ _ hq] at this
  obtain ⟨R₁, -, rfl⟩ := pastChains_spec hF₁
  obtain ⟨R₂, -, hF₂e⟩ := pastChains_spec hF₂
  have hchs : chs₁ = chs₂ := funext fun q => by
    by_cases hq : (Merges.Obs.leaf p₁ : Mg.Obs).Visible q
    · have := hcs' q hq.1
      rwa [hF₂e, Merges.Obs.fill_of_visible hq, Merges.Obs.fill_of_visible hq] at this
    · rw [hv₁.chains_nil q hq, hv₂.chains_nil q hq]
  subst hchs
  obtain rfl := eq_of_pastChains hD hv₁.ds_zero hv₂.ds_zero hF₁ hF₂ fun q hq => hcs' q hq
  rfl

theorem φ_transcript_eq_some {b : Bytes L} {q' : Query k kN kS L} (h : M.φ D (.transcript b) = some q') :
    ∃ c ss ch, M.senc.decode b = some c ∧ M.fullChain D c = some (ss, ch) ∧
      q' = .transcript (M.enc.encode ss ch) := by
  simp only [φ] at h
  obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨⟨ss, r⟩, hr, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨⟨ss', ch⟩, hch, hrr⟩ := Option.map_eq_some_iff.1 hr
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrr
  exact ⟨c, ss', ch, hc, hch, rfl⟩

/-- **Every query other than a chain input translates to itself.** -/
theorem φ_of_not_transcript {q : Query k kN kS L} (hq : ∀ b, q ≠ .transcript b) : M.φ D q = some q := by
  cases q with
  | transcript b => exact absurd rfl (hq b)
  | _ => rfl

/-- **The translation is injective on the recorded queries** of a database without digest
collisions. -/
theorem injOnKeys_φ (hD : D ∉ digestCollision) : DB.InjOnKeys (M.φ D) D := by
  intro q₁ q₂ q' hm₁ hm₂ h₁ h₂
  by_cases ht₁ : ∃ b, q₁ = .transcript b
  · obtain ⟨b₁, rfl⟩ := ht₁
    obtain ⟨c₁, ss₁, ch₁, hc₁, hf₁, rfl⟩ := φ_transcript_eq_some h₁
    by_cases ht₂ : ∃ b, q₂ = .transcript b
    · obtain ⟨b₂, rfl⟩ := ht₂
      obtain ⟨c₂, ss₂, ch₂, hc₂, hf₂, he⟩ := φ_transcript_eq_some h₂
      have hw₁ := M.senc.wf_of_decode _ _ hc₁
      have hw₂ := M.senc.wf_of_decode _ _ hc₂
      obtain ⟨rfl, rfl⟩ := M.enc.encode_injective (wf_fullChain hD hw₁ hf₁) (wf_fullChain hD hw₂ hf₂)
        (Query.transcript.inj he)
      obtain rfl := fullChain_inj hD hw₁ hw₂ hf₁ hf₂
      rw [← M.senc.encode_decode _ _ hc₁, ← M.senc.encode_decode _ _ hc₂]
    · push Not at ht₂
      rw [φ_of_not_transcript ht₂] at h₂
      exact absurd (Option.some_inj.1 h₂) (ht₂ _)
  · push Not at ht₁
    rw [φ_of_not_transcript ht₁] at h₁
    obtain rfl := Option.some_inj.1 h₁
    by_cases ht₂ : ∃ b, q₂ = .transcript b
    · obtain ⟨b₂, rfl⟩ := ht₂
      obtain ⟨_, _, _, _, _, he⟩ := φ_transcript_eq_some h₂
      exact absurd he (ht₁ _)
    · push Not at ht₂
      rw [φ_of_not_transcript ht₂] at h₂
      exact (Option.some_inj.1 h₂).symm

end Full

/-! ### The honest inputs translate -/

section Honest

/-- `D` records `q` with the answer of `h`. -/
def Recorded (h : Query k kN kS L → Out k e) (D : ODB k kN kS L e) (q : Query k kN kS L) : Prop :=
  D.lookup q = some (h q)

variable (h : Query k kN kS L → Out k e) (ss : SaltedStatement kS X) (wr : M.Writes)

/-- **The database records each branch's final input of the proof** with the answer of `h`. -/
def RecordsFinals (D : ODB k kN kS L e) : Prop :=
  ∀ s, Recorded h D (.transcript (M.senc.encode
    (finalContent ss (M.chains h ss wr) (M.finals h ss wr) s)))

/-- **The causal context of leaf `p`** in the chains of the proof. -/
def ctx (p : t.Leaf) : M.Ctx p := fun q => M.chains h ss wr q.1

variable {M h ss wr} {D : ODB k kN kS L e}

/-- **The final content of a proof is well formed.** -/
theorem wf_finalContent_chains (s : Mg.Site) :
    (finalContent ss (M.chains h ss wr) (M.finals h ss wr) s).WF n fun j => chainWF (P j) :=
  .final (Content.viewWF_view _ (fun q _ => chainWF_chains wr q) (fun q _ => length_chains wr q) _)

/-- **The round content of a proof at a proper prefix is well formed.** -/
theorem wf_roundContent_chains (p : t.Leaf) {l : M.Items p} (hl : chainWF (P p.label) l)
    (hlen : l.length < n p.label) :
    (roundContent ss (M.chains h ss wr) (M.finals h ss wr) p l).WF n fun j => chainWF (P j) :=
  .round (Content.viewWF_view _ (fun q _ => chainWF_chains wr q) (fun q _ => length_chains wr q) _)
    hl hlen

/-- **A final input of the proof at an observer's view is the final content of the proof.** -/
theorem finalAt_honest {o : Mg.Obs} {s : Mg.Site} (hs : Mg.Hides s o) :
    M.finalAt ss ((o).viewChains (W := fun j => (M.comp j).W) (M.chains h ss wr))
        (o.viewDs (M.finals h ss wr)) s
        ((Merges.Obs.sink s : Mg.Obs).viewChains (W := fun j => (M.comp j).W) (M.chains h ss wr)) =
      finalContent ss (M.chains h ss wr) (M.finals h ss wr) s := by
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

/-- **A hidden branch of the proof resolves to its chains.** -/
theorem resolveSink_honest (hD : D ∉ digestCollision) (hr : M.RecordsFinals h ss wr D)
    {o : Mg.Obs} {s : Mg.Site} (hs : Mg.Hides s o) :
    M.resolveSink D ss (o.viewChains (W := fun j => (M.comp j).W) (M.chains h ss wr))
        (o.viewDs (M.finals h ss wr)) s =
      some ((Merges.Obs.sink s : Mg.Obs).viewChains (W := fun j => (M.comp j).W) (M.chains h ss wr)) := by
  have hds : o.viewDs (M.finals h ss wr) s =
      (h (.transcript (M.senc.encode (finalContent ss (M.chains h ss wr) (M.finals h ss wr) s)))).digest := by
    rw [Merges.Obs.viewDs_of_hides _ _ hs, finals_eq]
    rfl
  unfold resolveSink
  rw [hds, findTr_of_lookup hD (hr s), Option.bind_some, M.senc.decode_encode _ (wf_finalContent_chains s)]
  simp only [finalContent, finalAt_honest hs]
  simp [finalContent]

/-- **The past of an observer of the proof resolves to the chains of the proof.** -/
theorem pastChains_honest (hD : D ∉ digestCollision) (hr : M.RecordsFinals h ss wr D) (o : Mg.Obs) :
    ∃ F, M.pastChains D ss o (o.viewChains (W := fun j => (M.comp j).W) (M.chains h ss wr))
        (o.viewDs (M.finals h ss wr)) = some F ∧ ∀ q, o.Sees q → F q = M.chains h ss wr q := by
  set R : Mg.Site → M.Chains := fun s => if Mg.Hides s o then
    (Merges.Obs.sink s : Mg.Obs).viewChains (W := fun j => (M.comp j).W) (M.chains h ss wr)
    else fun _ => []
  refine ⟨o.fill (W := fun j => (M.comp j).W) (o.viewChains (W := fun j => (M.comp j).W)
    (M.chains h ss wr)) R, ?_, fun q hq => ?_⟩
  · unfold pastChains
    rw [show (optAll fun s => if Mg.Hides s o then M.resolveSink D ss
        (o.viewChains (W := fun j => (M.comp j).W) (M.chains h ss wr)) (o.viewDs (M.finals h ss wr)) s
        else some fun _ => []) = some R from optAll_eq_some.2 fun s => by
      by_cases hs : Mg.Hides s o
      · simp only [hs, ↓reduceIte, R]
        exact resolveSink_honest hD hr hs
      · simp [hs, R]]
    rfl
  · by_cases hv : o.Visible q
    · rw [Merges.Obs.fill_of_visible hv, Merges.Obs.viewChains_of_visible _ _ hv]
    · obtain ⟨s, hs, hm⟩ := Merges.Obs.exists_hides_of_sees hq hv
      rw [Merges.Obs.fill_of_hides hs hm]
      simp only [hs, ↓reduceIte, R]
      exact Merges.Obs.viewChains_of_visible _ _ (Merges.visible_sink_of_mem hm)

/-- **The chain input of the proof at a proper prefix translates** to its salted statement and
the full-past compiler's chain input of the same causal past. -/
theorem fullOf_honest (hD : D ∉ digestCollision) (hr : M.RecordsFinals h ss wr D)
    (p : t.Leaf) (l : M.Items p) :
    M.fullOf D (roundContent ss (M.chains h ss wr) (M.finals h ss wr) p l) =
      some (ss, M.enc.encode ss (M.content p (M.ctx h ss wr p) l)) := by
  obtain ⟨F, hF, hFe⟩ := pastChains_honest hD hr (.leaf p)
  simp only [fullOf, fullChain, roundContent, hF, Option.map_some]
  congr 3
  exact M.content_congr (fun q hq => hFe q hq) l

/-- **A chain input of the proof at a proper prefix translates** to the full-past compiler's chain
input of the same causal past. -/
theorem φ_transcript_honest (hD : D ∉ digestCollision) (hr : M.RecordsFinals h ss wr D)
    (p : t.Leaf) {l : M.Items p} (hl : chainWF (P p.label) l) (hlen : l.length < n p.label) :
    M.φ D (.transcript (M.senc.encode (roundContent ss (M.chains h ss wr) (M.finals h ss wr) p l))) =
      some (.transcript (M.enc.encode ss (M.content p (M.ctx h ss wr p) l))) := by
  simp only [φ, M.senc.decode_encode _ (wf_roundContent_chains p hl hlen), Option.bind_some,
    fullOf_honest hD hr p l, Option.map_some]

end Honest

end

end GordieHowe.SPBCS
