-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Realize

@[expose] public section

/-!
# GordieHowe: the realization events from the structural checks alone

The challenge-use rule and the error bound of the realization events (`RealEvent`) read only the
tables (`TableOk`) and the MACs' realizations (`MacRealizable`: key, tag, blind, reads before the
key), not the recognized shapes of the other predicates. `GordieHowe.RealizedProgram.EventsOk`
states exactly those; the theorems here (`challengeUseAt_realEvent_ev`,
`probUniform_realEvent_le_ev`) read only it, so the derivations' validity (`DerivationsValid`)
gives them.
-/

namespace GordieHowe.RealizedProgram

open Export Range IOP ProofSystem.PhaseLayout
open scoped NNReal ENNReal

section

variable {ir : RealizedProgram} {I : Interp} {primeNodes : ℕ → List String}

variable (ir) in
/-- **A cross-field `equal`'s interval-free MAC shape**: hosted (`macHostedCoreB`) or two-tail
(`macTwoCoreB`), with a blind. -/
def macCoreOkB (pid : ℕ) : PredBody → Bool
  | .cross dx x dy y k real =>
    match real.blindX, real.blind with
    | none, some _ => ir.macHostedCoreB pid dx x dy y k real
    | some _, some _ => ir.macTwoCoreB pid x y k real
    | _, _ => false
  | _ => false

/-- **An interval-free MAC shape gives the key, the reads before it and a blind.** -/
theorem macCoreOkB_facts {p dx dy : ℕ} {x y : Expr} {k : CrossKind} {real : MacRealization}
    (h : ir.macCoreOkB p (.cross dx x dy y k real) = true) :
    ir.macKeyB p real = true ∧ ir.macReadsBeforeB x y real = true ∧ ∃ b, real.blind = some b := by
  simp only [macCoreOkB] at h
  split at h
  · rename_i b hbx hbl
    have c := MacHostedCore.of_B h
    exact ⟨c.key, c.before, b, hbl⟩
  · rename_i bx b hbx hbl
    have c := MacTwoCore.of_B h
    exact ⟨c.key, c.before, b, hbl⟩
  · cases h

/-- **A covered MAC realization has the interval-free shape.** -/
theorem macCoreOkB_of_realizable {p dx dy : ℕ} {x y : Expr} {k : CrossKind}
    {real : MacRealization} (h : ir.MacRealizable primeNodes p dx x dy y k real) :
    ir.macCoreOkB p (.cross dx x dy y k real) = true := by
  unfold MacRealizable at h
  simp only [macCoreOkB]
  split at h
  · rename_i hbx
    obtain ⟨b, hbl⟩ : ∃ b, real.blind = some b := by
      obtain ⟨_, -, hb, -⟩ := h.ivls
      unfold macBlindB at hb
      revert hb
      cases real.blind with
      | none => simp
      | some b => exact fun _ => ⟨b, rfl⟩
    rw [hbx, hbl]
    exact macHostedCoreB_of_core h.core
  · rename_i bx b hbx hbl
    rw [hbx, hbl]
    exact macTwoCoreB_of_core h.core
  · exact h.elim

/-- **The values an interval-free MAC shape reads are read before its key.** -/
theorem readsBefore_of_macCore (hwf : ir.WellFormed) {pid dx dy : ℕ} {x y : Expr}
    {k : CrossKind} {real : MacRealization} (hpid : pid < ir.predicates.length)
    (hb : (ir.predicate pid).body = .cross dx x dy y k real)
    (hok : ir.macCoreOkB pid (.cross dx x dy y k real) = true) :
    (∀ v ∈ ir.exprNodes x, ir.ReadsBefore real.key v) ∧
      (∀ v ∈ ir.exprNodes y, ir.ReadsBefore real.key v) ∧
      ir.ReadsBefore real.key (real.blind.getD 0) ∧
      ∀ bx ∈ real.blindX, ir.ReadsBefore real.key bx := by
  have href := hwf.bodyRefsOk (predicate_mem hpid)
  rw [hb] at href
  have hrx : ∀ k ∈ x.refs, k < ir.exprs.length := href (dx, x) (by simp [PredBody.exprs])
  have hry : ∀ k ∈ y.refs, k < ir.exprs.length := href (dy, y) (by simp [PredBody.exprs])
  obtain ⟨-, hbe, b, hbl⟩ := macCoreOkB_facts hok
  simp only [macReadsBeforeB, List.all_eq_true, List.mem_append] at hbe
  refine ⟨fun v hv => ?_, fun v hv => ?_, ?_, fun bx hbx => ?_⟩
  · exact (readsBeforeB_iff hwf _ v).1
      (hbe v (.inl (.inl (.inl ((mem_nodesOf hwf.refsOrdered hrx v).2 hv)))))
  · exact (readsBeforeB_iff hwf _ v).1
      (hbe v (.inl (.inl (.inr ((mem_nodesOf hwf.refsOrdered hry v).2 hv)))))
  · rw [hbl]
    exact (readsBeforeB_iff hwf _ b).1 (hbe b (.inl (.inr (by simp [hbl]))))
  · exact (readsBeforeB_iff hwf _ bx).1 (hbe bx (.inr (Option.mem_toList.2 hbx)))

variable (ir) in
/-- **The structural checks the realization events read**: every table is valid and every
cross-field `equal` has an interval-free MAC shape (`macCoreOkB`: key, tag, lengths, reads before
the key, field, blind). -/
structure EventsOk (primeNodes : ℕ → List String) : Prop where
  /-- Every table is valid. -/
  tables : ∀ t < ir.tables.length, ir.TableOk t
  /-- Every cross-field `equal` has an interval-free MAC shape. -/
  macs : ∀ p < ir.predicates.length, ∀ dx x dy y k real,
    (ir.predicate p).body = .cross dx x dy y k real → ir.macCoreOkB p (.cross dx x dy y k real) = true

theorem EventsOk.macKey (hv : ir.EventsOk primeNodes) {p : ℕ} (hp : p < ir.predicates.length)
    {dx : ℕ} {x : Expr} {dy : ℕ} {y : Expr} {k : CrossKind} {real : MacRealization}
    (hb : (ir.predicate p).body = .cross dx x dy y k real) : ir.macKeyB p real = true :=
  (macCoreOkB_facts (hv.macs p hp _ _ _ _ _ _ hb)).1

/-- **Two environments that agree up to a MAC's key have the same binding event**
(`EventsOk`). -/
theorem macEvent_eq_of_eqUpTo_ev (hwf : ir.WellFormed) (hv : ir.EventsOk primeNodes)
    {pid dx dy : ℕ} {x y : Expr} {k : CrossKind} {real : MacRealization}
    (hpid : pid < ir.predicates.length) (hb : (ir.predicate pid).body = .cross dx x dy y k real)
    {e e' : ir.Env I} (h : Env.EqUpTo real.key e e') :
    ir.macEvent e dx x dy y real = ir.macEvent e' dx x dy y real := by
  obtain ⟨hx, hy, hbl, hbx⟩ := readsBefore_of_macCore hwf hpid hb (hv.macs pid hpid _ _ _ _ _ _ hb)
  exact macEvent_congr h.asg (fun v hv => reader_eq_of_eqUpTo (hx v hv) h)
    (fun v hv => reader_eq_of_eqUpTo (hy v hv) h) (reader_eq_of_eqUpTo hbl h)
    fun b hb => reader_eq_of_eqUpTo (hbx b hb) h

/-- **Setting a MAC's key leaves its binding event unchanged** (`EventsOk`). -/
theorem macEvent_setChal_ev (hwf : ir.WellFormed) (hv : ir.EventsOk primeNodes)
    {pid dx dy : ℕ} {x y : Expr} {k : CrossKind} {real : MacRealization}
    (hpid : pid < ir.predicates.length) (hb : (ir.predicate pid).body = .cross dx x dy y k real)
    (e : ir.Env I) (c : ir.ChalVal I real.key) :
    ir.macEvent (e.setChal real.key c) dx x dy y real = ir.macEvent e dx x dy y real := by
  obtain ⟨hx, hy, hbl, hbx⟩ := readsBefore_of_macCore hwf hpid hb (hv.macs pid hpid _ _ _ _ _ _ hb)
  exact macEvent_congr rfl (fun v hv => reader_setChal (hx v hv) e c)
    (fun v hv => reader_setChal (hy v hv) e c) (reader_setChal hbl e c)
    fun b hb => reader_setChal (hbx b hb) e c

/-- **A table's challenge keys no MAC** (`EventsOk`): a table's challenge is drawn avoiding
the table (`TableOk.sampler`), a MAC's key from the whole field (`macKeyB`). -/
theorem not_macEvent_alpha_ev (hv : ir.EventsOk primeNodes) {t : ℕ} (ht : t < ir.tables.length)
    (e : ir.Env I) : ¬ ir.MacEvent (ir.alphaOf t) e := fun ⟨p, hp, dx, x, dy, y, k, real, hb, hk, _⟩ => by
  have h1 := hv.macKey hp hb
  simp only [macKeyB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h1
  have h2 := (hv.tables t ht).sampler
  rw [← hk, h1.1.1.2] at h2
  cases h2

/-- **A realization event's challenge is a challenge of a phase the program has**
(`EventsOk`): a table's challenge (`TableOk.alpha`) or a MAC's key (`macKeyB`). -/
theorem isPhaseChal_of_realEvent_ev (hv : ir.EventsOk primeNodes) {j : ℕ} {e : ir.Env I}
    (h : ir.RealEvent j e) : ir.IsPhaseChal j := by
  rcases h with ⟨t, ht, rfl, -⟩ | ⟨p, hp, dx, x, dy, y, k, real, hb, rfl, -⟩
  · exact (hv.tables t ht).alpha
  · have h1 := hv.macKey hp hb
    simp only [macKeyB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h1
    exact h1.1.1.1.1

/-- **The challenge-use rule for the realization events** (`EventsOk`): the event at `j`
reads only the needles and histograms of the groups at `j`, all read before `j`, the binding events
of the MACs keyed by `j`, read before `j` (`macEvent_eq_of_eqUpTo_ev`), and `j`'s coordinate `0`. -/
theorem challengeUseAt_realEvent_ev (hwf : ir.WellFormed) (hv : ir.EventsOk primeNodes) :
    ChallengeUseAt ir I ir.RealEvent := by
  intro j e e' h
  unfold RealEvent
  refine or_congr ?_ ?_
  · unfold LookupEvent
    refine exists_congr fun t => and_congr_right fun ht => and_congr_right fun hj => ?_
    subst hj
    refine exists_congr fun g => and_congr_right fun hg => ?_
    rw [groupEvent_congr (hv.tables t ht) hg _ fun v hr => reader_eq_of_eqUpTo hr h,
      h.chal _ (Or.inr ⟨rfl, le_rfl⟩)]
  · unfold MacEvent
    refine exists_congr fun p => and_congr_right fun hp => ?_
    refine exists_congr fun dx => exists_congr fun x => exists_congr fun dy => exists_congr
      fun y => exists_congr fun k => exists_congr fun real => ?_
    refine and_congr_right fun hb => and_congr_right fun hk => ?_
    subst hk
    rw [macEvent_eq_of_eqUpTo_ev hwf hv hp hb h, h.chal _ (Or.inr ⟨rfl, le_rfl⟩)]

/-- **The MAC event of one predicate at challenge `j` has probability at most its chunks over
`|F|`** (`EventsOk`): for a cross-field `equal` keyed by `j`, its binding polynomial is
fixed before the key (`macEvent_setChal_ev`), of degree `chunks`, and the key is uniform in the MAC
field, the field of `j` (`probUniform_macBad_le`); for any other predicate the event is empty. -/
theorem probUniform_macEventOf_le_ev (hwf : ir.WellFormed) (hv : ir.EventsOk primeNodes)
    {j p : ℕ} (hp : p < ir.predicates.length) (e : ir.Env I) :
    Pr[c ← ir.ChalVal I j : ∃ dx x dy y k real,
        (ir.predicate p).body = .cross dx x dy y k real ∧ real.key = j ∧
          (ir.macEvent (e.setChal j c) dx x dy y real).BadAt (castElt ((e.setChal j c).chal j 0))] ≤
      ((((ir.macChunksOf j p).getD 0 : ℕ) : ℝ≥0) / Fintype.card (I (ir.chalField j)).K : ℝ≥0) := by
  have hempty : ∀ (P : ir.ChalVal I j → Prop), (∀ c, ¬ P c) → ∀ b : ℝ≥0,
      Pr[c ← ir.ChalVal I j : P c] ≤ (b : ℝ≥0∞) := fun P hP b => by
    have : {c : ir.ChalVal I j | P c} = ∅ := Set.eq_empty_iff_forall_notMem.2 hP
    simp [probUniform, this]
  by_cases hc : ∃ dx x dy y k real, (ir.predicate p).body = .cross dx x dy y k real ∧ real.key = j
  · obtain ⟨dx, x, dy, y, k, real, hb, rfl⟩ := hc
    have hok := hv.macKey hp hb
    have hkf : ir.chalField real.key = real.macField := by
      have h1 := hok
      simp only [macKeyB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h1
      exact h1.1.2
    have hiff : ∀ c : ir.ChalVal I real.key,
        (∃ dx' x' dy' y' k' real', (ir.predicate p).body = .cross dx' x' dy' y' k' real' ∧
          real'.key = real.key ∧ (ir.macEvent (e.setChal real.key c) dx' x' dy' y' real').BadAt
            (castElt ((e.setChal real.key c).chal real.key 0))) ↔
          (ir.macEvent e dx x dy y real).BadAt (castElt ((e.setChal real.key c).chal real.key 0)) := by
      intro c
      constructor
      · rintro ⟨dx', x', dy', y', k', real', hb', -, hbad⟩
        rw [hb] at hb'
        cases hb'
        rwa [macEvent_setChal_ev hwf hv hp hb] at hbad
      · intro hbad
        exact ⟨dx, x, dy, y, k, real, hb, rfl, by rwa [macEvent_setChal_ev hwf hv hp hb]⟩
    have hP : (fun c : ir.ChalVal I real.key => ∃ dx' x' dy' y' k' real',
        (ir.predicate p).body = .cross dx' x' dy' y' k' real' ∧ real'.key = real.key ∧
          (ir.macEvent (e.setChal real.key c) dx' x' dy' y' real').BadAt
            (castElt ((e.setChal real.key c).chal real.key 0))) =
        fun c => (ir.macEvent e dx x dy y real).BadAt
          (castElt ((e.setChal real.key c).chal real.key 0)) := funext fun c => propext (hiff c)
    have hval : ((ir.macChunksOf real.key p).getD 0 : ℕ) = real.chunks := by
      rw [macChunksOf, hb]
      simp
    rw [hP, hval]
    refine (probUniform_macBad_le hok (ir.macEvent e dx x dy y real) e).trans ?_
    rw [macEvent_deg, Fintype.card_congr (Equiv.cast (congrArg (fun f => (I f).K) hkf))]
  · push Not at hc
    exact hempty _ (fun c ⟨dx, x, dy, y, k, real, hb, hk, _⟩ => hc dx x dy y k real hb hk) _

/-- **The MAC events at challenge `j` have probability at most the chunks of the MACs keyed by `j`
over `|F|`** (`probUniform_macEventOf_le_ev` and the union bound). -/
theorem probUniform_macEvent_le_ev (hwf : ir.WellFormed) (hv : ir.EventsOk primeNodes)
    (j : ℕ) (e : ir.Env I) :
    Pr[c ← ir.ChalVal I j : ir.MacEvent j (e.setChal j c)] ≤
      (((((ir.macChunksAt j).sum : ℕ) : ℝ≥0) / Fintype.card (I (ir.chalField j)).K : ℝ≥0) :
        ℝ≥0∞) := by
  have key : ∀ l : List ℕ, (∀ p ∈ l, p < ir.predicates.length) →
      Pr[c ← ir.ChalVal I j : ∃ p ∈ l, ∃ dx x dy y k real,
        (ir.predicate p).body = .cross dx x dy y k real ∧ real.key = j ∧
          (ir.macEvent (e.setChal j c) dx x dy y real).BadAt (castElt ((e.setChal j c).chal j 0))] ≤
      ((((l.map fun p => (ir.macChunksOf j p).getD 0).sum : ℕ) : ℝ≥0) /
        Fintype.card (I (ir.chalField j)).K : ℝ≥0) := by
    intro l hl
    induction l with
    | nil =>
      have : {c : ir.ChalVal I j | ∃ p ∈ ([] : List ℕ), ∃ dx x dy y k real,
          (ir.predicate p).body = .cross dx x dy y k real ∧ real.key = j ∧
            (ir.macEvent (e.setChal j c) dx x dy y real).BadAt
              (castElt ((e.setChal j c).chal j 0))} = ∅ := by simp
      simp only [probUniform, this, MeasureTheory.measure_empty]
      exact zero_le
    | cons p l ih =>
      simp only [List.mem_cons, exists_eq_or_imp]
      refine (probUniform_or_le_add
        (probUniform_macEventOf_le_ev hwf hv (hl p List.mem_cons_self) e)
        (ih fun q hq => hl q (List.mem_cons_of_mem _ hq))).trans (le_of_eq ?_)
      rw [List.map_cons, List.sum_cons, Nat.cast_add, add_div]
  have hev : ∀ c : ir.ChalVal I j, ir.MacEvent j (e.setChal j c) ↔
      ∃ p ∈ List.range ir.predicates.length, ∃ dx x dy y k real,
        (ir.predicate p).body = .cross dx x dy y k real ∧ real.key = j ∧
          (ir.macEvent (e.setChal j c) dx x dy y real).BadAt
            (castElt ((e.setChal j c).chal j 0)) := by
    intro c
    simp only [MacEvent, List.mem_range]
  simp only [hev]
  refine (key _ fun p hp => List.mem_range.1 hp).trans (le_of_eq ?_)
  rw [macChunksAt, sum_filterMap_eq_sum_map_getD]

/-- **The realization event at challenge `j` has probability at most `realError`** over `j`
(`EventsOk`): at a table's challenge, the lookup polynomials are fixed before `j` is drawn
and `j` is uniform outside `[0, tmax)` (no MAC is keyed by a table's challenge,
`not_macEvent_alpha_ev`); at any other challenge, the MACs keyed by `j` have their binding polynomials
fixed before `j` and `j` is uniform in the MAC field (`probUniform_macEvent_le_ev`). -/
theorem probUniform_realEvent_le_ev (hwf : ir.WellFormed) (hv : ir.EventsOk primeNodes)
    (hI : I.Registered ir) (j : ℕ) (e : ir.Env I) :
    Pr[c ← ir.ChalVal I j : ir.RealEvent j (e.setChal j c)] ≤ ir.realError I j := by
  by_cases hex : ∃ t < ir.tables.length, ir.alphaOf t = j
  · obtain ⟨t₀, ht₀, rfl⟩ := hex
    have hev : ∀ c : ir.ChalVal I (ir.alphaOf t₀),
        ir.RealEvent (ir.alphaOf t₀) (e.setChal (ir.alphaOf t₀) c) ↔
          ∃ tg ∈ ir.realGroups (ir.alphaOf t₀),
            (ir.groupEvent (ir.reader e) (ir.chalField (ir.alphaOf t₀)) tg.1 tg.2).BadAt
              ((e.setChal (ir.alphaOf t₀) c).chal (ir.alphaOf t₀) 0) := by
      intro c
      rw [RealEvent, or_iff_left (not_macEvent_alpha_ev hv ht₀ _)]
      simp only [LookupEvent, mem_realGroups]
      constructor
      · rintro ⟨t, ht, hj, g, hg, hbad⟩
        refine ⟨(t, g), ⟨ht, hj, hg⟩, ?_⟩
        rwa [groupEvent_congr (hv.tables t ht) hg _ fun v hr =>
          reader_setChal (hj ▸ hr) e c] at hbad
      · rintro ⟨⟨t, g⟩, ⟨ht, hj, hg⟩, hbad⟩
        refine ⟨t, ht, hj, g, hg, ?_⟩
        simp only at hbad
        rwa [groupEvent_congr (hv.tables t ht) hg _ fun v hr =>
          reader_setChal (hj ▸ hr) e c]
    simp only [hev]
    refine (probUniform_exists_logupBad_le (hv.tables t₀ ht₀) hI _ _ e).trans ?_
    rw [realError_eq]
    refine ENNReal.coe_le_coe.2 (div_le_div_of_nonneg_right ?_ zero_le)
    have heq : ((ir.realGroups (ir.alphaOf t₀)).map fun tg =>
        (ir.groupEvent (ir.reader e) (ir.chalField (ir.alphaOf t₀)) tg.1 tg.2).deg).sum =
        (((ir.realGroups (ir.alphaOf t₀)).map fun tg => (ir.groupCount tg.1 tg.2 +
          ir.tableSize tg.1 - 1, ir.tmaxOf (ir.alphaOf t₀))).map Prod.fst).sum := by
      simp only [List.map_map]
      refine congrArg List.sum (List.map_congr_left fun tg _ => ?_)
      simp only [Function.comp_apply, groupEvent_deg]
    rw [realErrorTerms, List.map_append, List.sum_append, ← heq]
    exact_mod_cast Nat.le_add_right _ _
  · push Not at hex
    have hnl : ∀ c : ir.ChalVal I j, ¬ ir.LookupEvent j (e.setChal j c) :=
      fun c ⟨t, ht, hj, _⟩ => hex t ht hj
    have hgroups : ir.realGroups j = [] := by
      simp only [realGroups, List.flatMap_eq_nil_iff, List.mem_filter, List.mem_range,
        decide_eq_true_eq, List.map_eq_nil_iff, List.range_eq_nil]
      intro t ⟨ht, hj⟩
      exact absurd hj (hex t ht)
    simp only [RealEvent, hnl, false_or]
    refine (probUniform_macEvent_le_ev hwf hv j e).trans ?_
    by_cases hm : ∃ p < ir.predicates.length, ∃ dx x dy y k real,
        (ir.predicate p).body = .cross dx x dy y k real ∧ real.key = j
    · obtain ⟨p, hp, dx, x, dy, y, k, real, hb, rfl⟩ := hm
      have htmax : ir.tmaxOf real.key = 0 := by
        have h1 := hv.macKey hp hb
        simp only [macKeyB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h1
        simp only [tmaxOf, h1.1.1.2]
      rw [realError_eq, realErrorTerms, hgroups, htmax]
      have hfst : (ir.macChunksAt real.key).map (Prod.fst ∘ fun n => (n, 0)) =
          ir.macChunksAt real.key := List.map_id _
      simp only [List.map_nil, List.nil_append, List.map_map, Nat.sub_zero, hfst]
      exact le_rfl
    · push Not at hm
      have hnil : ir.macChunksAt j = [] := by
        simp only [macChunksAt, List.filterMap_eq_nil_iff, List.mem_range]
        intro p hp
        unfold macChunksOf
        split
        · rename_i dx x dy y k real hb
          exact if_neg (hm p hp dx x dy y k real hb)
        · rfl
      rw [hnil]
      simp

end

end GordieHowe.RealizedProgram
