-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Derivation.Rules
public import GordieHowe.Language.Realizations.Derivation.Disjoint
public import GordieHowe.Language.Realizations.Derivation.FieldMod
public import GordieHowe.Language.Realizations.Derivation.LinOp
public import GordieHowe.Language.Realizations.Derivation.Solve
public import GordieHowe.Language.Realizations.Derivation.OpIvl
public import GordieHowe.Language.Realizations.Derivation.Events
public import GordieHowe.Language.RealizedProgram.IvlSource
public import GordieHoweNative.Language.RealizedProgram.Structure
public import GordieHowe.Language.Realizations.Derivation.Mac
public import GordieHowe.Language.Realizations.Derivation.Grouped
public import GordieHowe.Language.Realizations.Derivation.ProductMod
public import GordieHowe.Language.Realizations.Derivation.TableKernel
public import GordieHoweNative.Language.Realizations.Derivation

@[expose] public section

/-!
# GordieHowe: derivations, the realization check as a proof checker

A derivation is the compiler's proof that a source predicate follows from the realized program,
up to charged challenge events, as a list of steps of a fixed rule set (`CERTIFYING_COMPILER.md`,
"Derivations: the realization check as a proof checker"). This file holds the rule set, its checker
and the checker's soundness.

* **Facts** (`GordieHowe.RealizedProgram.Fact`, `GordieHowe.RealizedProgram.Fact.HoldsWith`): a field
  equation `eq d e₁ e₂`, a range `nat d e N` (every coordinate the cast of a natural below `N`), an
  interval `ivl d e lo hi` (every coordinate's integer reading in `[lo, hi]`, casting to its value),
  an integer equation `intEq d e₁ e₂`, a divisibility `dvd d e q` (every coordinate's integer reading
  a multiple of `q`), the rows `inRows t e` of table `t`, and a predicate's body `holds p`.
* **Steps** (`GordieHowe.RealizedProgram.Step`): each names its premises by index into the facts of the
  derivation's earlier steps, and program items by id in named fields; the domain of every fact a
  step concludes is the domain `d` of the derivation's predicate (`PredBody.dom`), except where a
  step reads it off a predicate it names (`realized`, `holdsIn`).
* **The checker** (`GordieHowe.RealizedProgram.stepFact`, `GordieHowe.RealizedProgram.derivB`): one pass over the
  steps, each step's conclusion computed from its premises' facts with its side conditions checked
  locally; the derivation checks when its last fact is `holds pid`.
* **Soundness**: each rule is sound at the reader of a sampled environment of the realized program
  (`GordieHowe.RealizedProgram.stepFact_sound`); the lookup rule's conclusion holds or the group's
  challenge is a root of its lookup polynomial (`GordieHowe.RealizedProgram.lookupFact_sound`, from
  `GordieHowe.RealizedProgram.needlesIn_or_logupBad`). A derivation that checks gives its predicate or a
  realization event (`GordieHowe.RealizedProgram.derivB_sound`), and derivations for every predicate give the
  program (`GordieHowe.RealizedProgram.satAt_or_realEvent_of_derivs`).

The rule `mac` is declared (the format the emitter writes) and concludes nothing yet: a derivation
using it fails. `ivlSolve` (solving an integer equation for one atom's interval) is in
`GordieHowe/Language/Realizations/Derivation/Solve.lean`. The linear-operator rule `linop`
(congruence through an operator, a core-language operator's signed sparse rows, the spectral
convolution, the transforms' identities) is in
`GordieHowe/Language/Realizations/Derivation/LinOp.lean` and `Derivation/Ntt.lean`. The intervals
of operator applications (batched numbers from digits, negacyclic products) and of Logic builders
on bits (`ivlApply`, `ivlLogic`) are in `Derivation/OpIvl.lean`. The interval sources `opaqueBit`, `quadRoot` and
`rootSet` read their rules in `GordieHowe/Language/Realizations/Derivation/Roots.lean`, the root
equations through the realized program's field `equal`s. `conclude` concludes field `equal`s, `in`s into a range and `mod_0`s;
`congr` concludes a `mod_q` from a `dvd` fact, which `lift` gives from the field equation
`e − e' = q · Q + C`, the interval of `e − e'` and the quotient's range. The interval of a
shared expression's integer reading is that of its entry's (`evalIntWith_ref`), so an interval
from a range (`ivlNat`, `src … (.nat k)`) is stated only for a leaf whose integer reading is its
natural. `ivlExpr` walks its expression in pre-order consuming its premises in order
(`ivlWalk`): sums, differences, products, constant multiples, views, concatenations and shared
expressions.

The definitions are in `GordieHoweNative/Language/Realizations/Derivation.lean`
(the compiled library `GordieHoweNative`); this module has their lemmas.
-/

namespace GordieHowe.RealizedProgram

open Export Range IOP

section

variable (ir : RealizedProgram) {I : Interp}

/-- **`fieldRowOkB` gives the field row** of a field-form `mod_q` with `q ≠ 0`. -/
theorem fieldRowOkB_sound {S : Structure} {pid d q : ℕ} {e e' : Expr} {real : ModRealization}
    (hb : (ir.predicate pid).body = .mod d q e e' real)
    (h : ir.fieldRowOkB S pid (ir.predicate pid).body = true) (hq : q ≠ 0)
    (hf : real.form = .field) :
    q = ir.charOf (ir.domainField d) ∧ 2 < q ∧
      ir.predicates.any (fun p => ir.fieldRowB d e e' p.body) = true := by
  rw [hb] at h
  simp only [fieldRowOkB, fieldRowOkE, hf, decide_true, Bool.and_true,
    bne_iff_ne, ne_eq, hq, not_false_eq_true, ↓reduceIte, Twin.okB_seqE, Twin.okB_guardE,
    Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨hq1, hq2⟩, hp⟩ := h
  obtain ⟨r, hr⟩ := ir.exists_fieldRowAtB_of_ptr hp
  exact ⟨hq1, hq2, ir.any_fieldRowB_of_fieldRowAtB hb hr⟩

/-- **The derivations are valid**: aligned with the predicates, every predicate's derivation and
every shared entry checks at its rank (`Derivations.ctx`). -/
structure DerivationsValid (primeNodes : ℕ → List String) (sr : List (ℕ × ℕ))
    (D : Derivations) : Prop where
  /-- Every predicate's derivation checks (`Derivations.stepsOf`). -/
  checks : ∀ pid < ir.predicates.length,
    ir.derivB primeNodes sr D.ctx pid (ir.predicate pid).body (D.stepsOf pid) = true
  /-- Every `mod_0`'s derivation cites intervals of both its sides, by shared entries whose
  steps hold at the honest prover's reader (`modCiteB`; the completeness part). -/
  mods : ∀ pid < ir.predicates.length,
    modCiteB D.shared (ir.predicate pid).body (D.stepsOf pid) = true
  /-- Every shared entry checks. -/
  shared : ∀ k < D.shared.length, ir.entryB primeNodes sr D.ctx k (D.shared.getD k default) = true
  /-- Every table is valid (the structural part the events read). -/
  tables : ∀ t < ir.tables.length, ir.TableOk t
  /-- Every cross-field `equal` has a covered MAC realization (the structural part the events
  read). -/
  macs : ∀ p < ir.predicates.length, derivCrossB (ir.predicate p).body = true →
    ir.macOkB p (ir.predicate p).body = true
  /-- Every lookup `in` has its interval-free shape (the structural part the honest prover's
  histograms read). -/
  lookups : ∀ pid < ir.predicates.length, ∀ d recs set r,
    (ir.predicate pid).body = .mem d recs set (.lookup r) → ir.LookupCore pid d recs set r
  /-- Every value bound to its digits reads committed values and constants. -/
  bound : ∀ v < ir.values.length, ir.BoundOk v
  /-- Every `mod_q` in the field form has its field equation as a row (`fieldRowOkB`; the honest
  prover's placed predicates read it). -/
  fieldRows : ∀ pid < ir.predicates.length, ∀ d q e e' real,
    (ir.predicate pid).body = .mod d q e e' real → q ≠ 0 → real.form = .field →
      q = ir.charOf (ir.domainField d) ∧ 2 < q ∧
        ir.predicates.any (fun p => ir.fieldRowB d e e' p.body) = true
  /-- Every product-form `mod_q` passes the structural check (`productOkB`) in a field of
  characteristic above `2` (the honest prover's placed equation reads it). -/
  products : ∀ pid < ir.predicates.length, ∀ d q e e' real,
    (ir.predicate pid).body = .mod d q e e' real → real.form.isProduct = true →
      ir.productOkB (.mod d q e e' real) = true ∧ 2 < ir.charOf (ir.domainField d)

/-- **The realization step has valid derivations** (`DerivationsValid`): the realization
condition of a program, at the plan's prime-subfield nodes `primeNodes` and the value ranges
`sr`. -/
def Derivable (primeNodes : ℕ → List String) (sr : List (ℕ × ℕ)) : Prop :=
  ∃ D, ir.DerivationsValid primeNodes sr D

end

section Sound

variable {ir : RealizedProgram} {I : Interp} {primeNodes : ℕ → List String}

/-- **Every rule is sound** at the reader of a sampled environment of the realized program at a
realized assignment (`hB`) within the value ranges `sr` (`hS`), where what the derivation cites
holds (`hc`): the step's fact holds where its premises' do, or (`lookup`, `mac`, `src … tableKernel`)
a realization event happens. -/
theorem stepFact_sound (hM : ir.DerivModel I primeNodes) {sr : List (ℕ × ℕ)} {e : ir.Env I}
    (he : Env.Sampled ir e) (h : ir.RealizedAt e)
    (hS : ∀ vN ∈ sr, ∀ i < (ir.value vN.1).size,
      ∃ n < vN.2, ir.reader e vN.1 i = ((n : ℕ) : (I (ir.valueField vN.1)).K))
    (hB : ir.BoundReads (ir.reader e)) {ctx : DerivCtx} {self pid : ℕ} {body : PredBody}
    (hown : OwnBody ir pid body) (hc : CitesHold e ctx self)
    {fs : List Fact} (hfs : ∀ f ∈ fs, f.Holds e)
    {s : Step} {f : Fact} (hf : ir.stepFact primeNodes sr ctx self pid body fs s = some f) :
    f.Holds e ∨ ∃ j, ir.RealEvent j e := by
  have hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      ir.reader e v i = (I (ir.valueField v)).decode (es.getD i 0) :=
    fun _ _ hk i => reader_of_constant e hk i
  induction s generalizing body f with
  | realized p =>
    simp only [stepFact] at hf
    split_ifs at hf
    · rcases hown with ⟨hpid, hpb⟩ | ⟨d, rfl⟩
      · rw [← hpb] at hf
        exact .inl (realizedOf_sound h (predicate_mem hpid) hf)
      · simp [realizedOf, entryBody] at hf
    · exact .inl (realizedFact_sound h hf)
  | subst e₁ e₂ => exact .inl (substFact_sound hM.wf hB hf)
  | linear cs e₁ e₂ => exact .inl (linearFact_sound hK hM.wf hM.registered hM.lawful hfs hf)
  | lookup ms => exact lookupFact_sound hM.registered hM.tables he h hf
  | ivlNat k => exact .inl (ivlNatFact_sound hM.wf hM.lawful hfs hf)
  | ivlSolve k ks a j lo hi => exact .inl (ivlSolveFact_sound hM.registered hM.wf hfs hf)
  | ivlApply k a e lo hi => exact .inl (ivlApplyFact_sound hM.wf hM.registered hM.lawful hfs hf)
  | ivlLogic ks e => exact .inl (ivlLogicFact_sound hfs hf)
  | ivlMeet a b => exact .inl (ivlMeetFact_sound hfs hf)
  | ivlDisjoint a b => exact .inl (ivlDisjointFact_sound hfs hf)
  | fieldDvd k a b => exact .inl (fieldDvdFact_sound hM.wf hM.registered hfs hf)
  | natIvl k => exact .inl (natIvlFact_sound hfs hf)
  | transport k j => exact .inl (transportFact_sound hfs hf)
  | natComp k j => exact .inl (natCompFact_sound hM.wf hM.registered hM.lawful hK hfs hf)
  | natBool p => exact .inl (natBoolFact_sound h hf)
  | natLin k ks => exact .inl (natLinFact_sound hM.wf hM.registered hM.lawful hK hfs hf)
  | liftConst k a => exact .inl (liftConstFact_sound hM.wf hM.registered hM.lawful hK hfs hf)
  | rangeNat k => exact .inl (rangeNatFact_sound hfs hf)
  | holdsIn k => exact .inl (holdsInFact_sound hfs hf)
  | src v s =>
    simp only [stepFact] at hf
    split_ifs at hf with hg
    rcases Option.or_eq_some_iff.1 hf with hf | ⟨-, hf⟩
    · exact .inl (srcFact_sound hM.wf hM.registered hM.lawful h hS hfs hg hf)
    · exact tableKernelFact_sound hM.wf hM.registered hM.lawful hS hc hf
  | ivlExpr ks x lo hi => exact .inl (ivlExprFact_sound hM.wf hM.registered hM.lawful hK hfs hf)
  | lift k a b => exact .inl (liftFact_sound hM.wf hM.registered hM.lawful hK hfs hf)
  | digits k ds T => exact .inl (digitsFact_sound hM.wf hM.registered hM.lawful hK hfs hf)
  | congr k =>
    rcases hown with ⟨-, hpb⟩ | ⟨d, rfl⟩
    · exact .inl (congrFact_sound hfs hpb hf)
    · simp [stepFact, congrFact, entryBody] at hf
      split at hf <;> simp_all
  | mac ts hh ivs =>
    exact macFact_sound hM.wf hM.registered hM.lawful hM.mac h hown hc hfs hf
  | linop s => exact .inl (linopFact_sound hM.wf hM.registered hM.lawful hK hfs hf)
  | conclude k =>
    rcases hown with ⟨-, hpb⟩ | ⟨d, rfl⟩
    · exact .inl (concludeFact_sound hfs hpb hf)
    · simp [stepFact, concludeFact, entryBody] at hf
      split at hf <;> simp_all
  | hyp q =>
    simp only [stepFact] at hf
    split_ifs at hf with hq
    cases hf
    exact .inl (hc.1 q hq.1 hq.2)
  | fact k =>
    simp only [stepFact] at hf
    split_ifs at hf with hk
    exact .inl (hc.2 k f hk hf)
  | inDom d s ih =>
    simp only [stepFact] at hf
    exact ih (.inr ⟨d, rfl⟩) hf
  | groupedMod rows ivs =>
    exact .inl (groupedFact_sound hM.wf hM.registered hM.lawful hown hc hfs hf)
  | productMod ks =>
    exact .inl (productModFact_sound hM.wf hM.registered hM.lawful h hS hfs hown hf)
  | circuitAssert k => simp [stepFact] at hf
  | inputPremise k => simp [stepFact] at hf

/-- **The facts of a derivation hold**, or a realization event happens. -/
theorem runSteps_sound (hM : ir.DerivModel I primeNodes) {sr : List (ℕ × ℕ)} {e : ir.Env I}
    (he : Env.Sampled ir e) (h : ir.RealizedAt e)
    (hS : ∀ vN ∈ sr, ∀ i < (ir.value vN.1).size,
      ∃ n < vN.2, ir.reader e vN.1 i = ((n : ℕ) : (I (ir.valueField vN.1)).K))
    (hB : ir.BoundReads (ir.reader e)) {ctx : DerivCtx} {self pid : ℕ} {body : PredBody}
    (hown : OwnBody ir pid body) (hc : CitesHold e ctx self) :
    ∀ {fs : List Fact} {ss : List Step} {fs' : List Fact},
      ((∀ f ∈ fs, f.Holds e) ∨ ∃ j, ir.RealEvent j e) →
      ir.runSteps primeNodes sr ctx self pid body fs ss = some fs' →
        (∀ f ∈ fs', f.Holds e) ∨ ∃ j, ir.RealEvent j e
  | fs, [], fs', h0, hr => by
    simp only [runSteps, Option.some.injEq] at hr
    subst hr
    exact h0
  | fs, s :: ss, fs', h0, hr => by
    simp only [runSteps, Option.bind_eq_some_iff] at hr
    obtain ⟨f, hf, hr⟩ := hr
    refine runSteps_sound hM he h hS hB hown hc ?_ hr
    rcases h0 with h0 | h0
    · rcases stepFact_sound hM he h hS hB hown hc h0 hf with h1 | h1
      · refine .inl fun g hg => ?_
        rcases List.mem_append.1 hg with hg | hg
        · exact h0 g hg
        · rw [List.mem_singleton.1 hg]
          exact h1
      · exact .inr h1
    · exact .inr h0

/-- **Steps that check give their predicate, or a realization event** (`derivStepsB`). -/
theorem derivStepsB_sound (hM : ir.DerivModel I primeNodes) {sr : List (ℕ × ℕ)} {e : ir.Env I}
    (he : Env.Sampled ir e) (h : ir.RealizedAt e)
    (hS : ∀ vN ∈ sr, ∀ i < (ir.value vN.1).size,
      ∃ n < vN.2, ir.reader e vN.1 i = ((n : ℕ) : (I (ir.valueField vN.1)).K))
    (hB : ir.BoundReads (ir.reader e)) {ctx : DerivCtx} {self pid : ℕ}
    (hpid : pid < ir.predicates.length) (hc : CitesHold e ctx self) {steps : List Step}
    (hd : ir.derivStepsB primeNodes sr ctx self pid (ir.predicate pid).body steps = true) :
    ir.HoldsAt e (ir.predicate pid).body ∨ ∃ j, ir.RealEvent j e := by
  unfold derivStepsB at hd
  split at hd
  · rename_i fs hfs
    split at hd
    · rename_i p hl
      obtain rfl := beq_iff_eq.1 hd
      rcases runSteps_sound hM he h hS hB (.inl ⟨hpid, rfl⟩) hc
          (.inl fun _ h => absurd h List.not_mem_nil) hfs with h1 | h1
      · exact .inl (h1 _ (List.mem_of_getLast? hl))
      · exact .inr h1
    · cases hd
  · cases hd

/-- **A shared entry that checks has its fact**, or a realization event happens. -/
theorem entryB_sound (hM : ir.DerivModel I primeNodes) {sr : List (ℕ × ℕ)} {e : ir.Env I}
    (he : Env.Sampled ir e) (h : ir.RealizedAt e)
    (hS : ∀ vN ∈ sr, ∀ i < (ir.value vN.1).size,
      ∃ n < vN.2, ir.reader e vN.1 i = ((n : ℕ) : (I (ir.valueField vN.1)).K))
    (hB : ir.BoundReads (ir.reader e)) {ctx : DerivCtx} {k : ℕ} {en : SharedEntry}
    (hc : CitesHold e ctx (ctx.srank k)) (hd : ir.entryB primeNodes sr ctx k en = true) :
    en.fact.Holds e ∨ ∃ j, ir.RealEvent j e := by
  unfold entryB at hd
  split at hd
  · rename_i fs hfs
    rcases runSteps_sound hM he h hS hB (.inr ⟨_, rfl⟩) hc
        (.inl fun _ h => absurd h List.not_mem_nil) hfs with h1 | h1
    · cases hl : fs.getLast? with
      | none => rw [hl] at hd; cases hd
      | some g =>
        rw [hl] at hd
        simp only [Option.map_some, Option.getD_some] at hd
        rw [← Fact.eq_of_beq hd]
        exact .inl (h1 _ (List.mem_of_getLast? hl))
    · exact .inr h1
  · cases hd

/-- **The merged derivation checker leaves only entries from `pid` on.** -/
theorem allDerivsB_ge {sr : List (ℕ × ℕ)} {ctx : DerivCtx} {sh : List SharedEntry} :
    ∀ {pid : ℕ} {ps : List Predicate}
    {ds : List (ℕ × List Step)}, ir.allDerivsB primeNodes sr ctx sh pid ps ds = true →
      ∀ d ∈ ds, pid ≤ d.1
  | _, [], [], _ => by simp
  | _, [], _ :: _, h => by simp [allDerivsB] at h
  | _, _ :: _, [], _ => by simp
  | pid, pr :: ps, d :: ds, h => by
    unfold allDerivsB at h
    split_ifs at h with hq
    · simp only [Bool.and_eq_true] at h
      have := allDerivsB_ge h.2
      intro d' hd'
      rcases List.mem_cons.1 hd' with rfl | hd'
      · omega
      · have := this d' hd'
        omega
    · simp only [Bool.and_eq_true] at h
      have := allDerivsB_ge h.2
      intro d' hd'
      have := this d' hd'
      omega

/-- **`defaultSteps` derive a field `equal`**: `realized pid` gives its field equation, which
`conclude 0` matches against its sides. -/
theorem derivB_default_of_equal (primeNodes : ℕ → List String) (sr : List (ℕ × ℕ))
    (ctx : DerivCtx) (sh : List SharedEntry) (pid : ℕ) {body : PredBody}
    (h : defaultOkB body = true) :
    ir.derivB primeNodes sr ctx pid body (defaultSteps pid) = true ∧
      modCiteB sh body (defaultSteps pid) = true := by
  cases body with
  | equal d a b r =>
    refine ⟨?_, rfl⟩
    simp [derivB, derivStepsB, defaultSteps, runSteps, stepFact, realizedOf, concludeFact,
      Expr.beq_self]
  | _ => cases h

/-- **The merged derivation checker checks each predicate's derivation** (`sparseSteps`). -/
theorem allDerivsB_sound {sr : List (ℕ × ℕ)} {ctx : DerivCtx} {sh : List SharedEntry} :
    ∀ {pid : ℕ} {ps : List Predicate}
    {ds : List (ℕ × List Step)}, ir.allDerivsB primeNodes sr ctx sh pid ps ds = true →
      ∀ k < ps.length,
        ir.derivB primeNodes sr ctx (pid + k) (ps.getD k default).body
          (sparseSteps ds (pid + k)) = true ∧
        modCiteB sh (ps.getD k default).body (sparseSteps ds (pid + k)) = true
  | _, [], _, _ => fun k hk => absurd hk (Nat.not_lt_zero k)
  | pid, pr :: ps, [], h => by
    simp only [allDerivsB, Bool.and_eq_true] at h
    intro k hk
    rcases k with _ | k
    · simpa [sparseSteps] using derivB_default_of_equal (ir := ir) primeNodes sr ctx sh pid h.1
    · have := allDerivsB_sound h.2 k (by simpa using hk)
      rw [show pid + (k + 1) = pid + 1 + k by omega]
      simpa using this
  | pid, pr :: ps, d :: ds, h => by
    have hge := allDerivsB_ge h
    unfold allDerivsB at h
    split_ifs at h with hq
    · simp only [Bool.and_eq_true] at h
      have hge' := allDerivsB_ge h.2
      intro k hk
      rcases k with _ | k
      · simpa [sparseSteps, hq] using h.1
      · have := allDerivsB_sound h.2 k (by simpa using hk)
        rw [show pid + (k + 1) = pid + 1 + k by omega]
        have hne : d.1 ≠ pid + 1 + k := by omega
        simpa [sparseSteps, hne] using this
    · simp only [Bool.and_eq_true] at h
      have hge' := allDerivsB_ge h.2
      intro k hk
      rcases k with _ | k
      · have hd : sparseSteps (d :: ds) pid = defaultSteps pid := by
          simp only [sparseSteps, if_neg hq]
          exact sparseSteps_of_lt fun d' hd' => by
            have := hge' d' (by simp [hd'])
            omega
        simpa [hd] using derivB_default_of_equal (ir := ir) primeNodes sr ctx sh pid h.1
      · have := allDerivsB_sound h.2 k (by simpa using hk)
        rw [show pid + (k + 1) = pid + 1 + k by omega]
        simpa using this

/-- **`derivsB` decides `DerivationsValid`** (one direction). -/
theorem derivationsValid_of_derivsB (hwf : ir.WellFormed) {sr : List (ℕ × ℕ)} {S : Structure}
    {D : Derivations} (h : ir.derivsB primeNodes sr S D = true) :
    ir.DerivationsValid primeNodes sr D := by
  unfold derivsB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  have hk := allDerivsB_sound h1
  rw [allIdx_iff] at h5
  rw [allIdx_values_iff] at h6
  rw [allIdx_iff] at h7
  rw [allIdx_iff] at h8
  refine ⟨fun pid hpid => by simpa [predicate_eq_getD, Derivations.stepsOf] using (hk pid hpid).1,
    fun pid hpid => by simpa [predicate_eq_getD, Derivations.stepsOf] using (hk pid hpid).2,
    fun k hk' => ?_,
    fun t ht => (tableOkB_iff hwf t).1 (List.all_eq_true.1 h3 t (List.mem_range.2 ht)),
    fun p hp hc => ?_, fun pid hpid d recs set r hb => ?_,
    fun v hv => (boundOkV_iff hwf v).1 (h6 v hv), fun pid hpid d q e e' real hb hq hf => ?_,
    fun pid hpid d q e e' real hb hf => ?_⟩
  · have := List.all_eq_true.1 h2 (D.shared[k], k) (List.mem_iff_getElem.2
      ⟨k, by simpa using hk', by simp⟩)
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk'] using this
  · have := List.all_eq_true.1 h4 ((ir.predicate p), p) (List.mem_iff_getElem.2
      ⟨p, by simpa using hp, by simp [predicate_eq_getD, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hp]⟩)
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at this
    rcases this with h0 | h0
    · rw [hc] at h0
      cases h0
    · exact h0
  · have := h5 pid hpid
    simp only [Nat.zero_add] at this
    rw [← predicate_eq_getD] at this
    change ir.lookupCoreB pid (ir.predicate pid).body = true at this
    rw [hb] at this
    simp only [lookupCoreB] at this
    unfold LookupCore
    revert this
    cases r.kind <;> simp only [Bool.false_eq_true, imp_false, not_false_eq_true,
      decide_eq_true_eq, imp_self]
    exact (directOkB_iff hwf _ _ _ _ _).1
  · have := h7 pid hpid
    simp only [Nat.zero_add] at this
    rw [← predicate_eq_getD] at this
    change ir.fieldRowOkB S pid (ir.predicate pid).body = true at this
    exact ir.fieldRowOkB_sound hb this hq hf
  · have := h8 pid hpid
    rw [← predicate_eq_getD] at this
    change ir.productValidB (ir.predicate pid).body = true at this
    rw [hb] at this
    simp only [productValidB, PredBody.isProductMod, hf, Bool.not_true, Bool.false_or,
      Bool.and_eq_true, PredBody.dom] at this
    exact ⟨this.1, of_decide_eq_true this.2⟩

/-- **Valid derivations give the structural checks the events read** (`EventsOk`). -/
theorem DerivationsValid.eventsOk {sr : List (ℕ × ℕ)} {D : Derivations}
    (hv : ir.DerivationsValid primeNodes sr D) : ir.EventsOk primeNodes := by
  refine ⟨hv.tables, fun p hp dx x dy y k real hb => ?_⟩
  have h := hv.macs p hp (by rw [hb]; rfl)
  rw [hb] at h
  exact h

/-- **Derivable realizations have valid tables** (`DerivationsValid.tables`). -/
theorem Derivable.tables {sr : List (ℕ × ℕ)} (hv : ir.Derivable primeNodes sr) :
    ∀ t < ir.tables.length, ir.TableOk t :=
  hv.elim fun _ hD => hD.tables

/-- **At derivable realizations every bound value reads committed values and constants**
(`DerivationsValid.bound`). -/
theorem Derivable.bound {sr : List (ℕ × ℕ)} (hv : ir.Derivable primeNodes sr) :
    ∀ v < ir.values.length, ir.BoundOk v :=
  hv.elim fun _ hD => hD.bound

/-- **Derivable realizations give the structural checks the events read**
(`DerivationsValid.eventsOk`). -/
theorem Derivable.eventsOk {sr : List (ℕ × ℕ)} (hv : ir.Derivable primeNodes sr) :
    ir.EventsOk primeNodes :=
  hv.elim fun _ hD => hD.eventsOk

/-- **The challenge-use rule for the realization events**, from valid derivations
(`challengeUseAt_realEvent_ev` at their structural checks). -/
theorem challengeUseAt_realEvent_of_derivs (hwf : ir.WellFormed) {sr : List (ℕ × ℕ)}
    {D : Derivations} (hv : ir.DerivationsValid primeNodes sr D) :
    ChallengeUseAt ir I ir.RealEvent :=
  challengeUseAt_realEvent_ev hwf hv.eventsOk

/-- **The realization event at challenge `j` has probability at most `realError`**, from valid
derivations (`probUniform_realEvent_le_ev` at their structural checks) and the selections' bound
(`SelSound`). -/
theorem probUniform_realEvent_le_of_derivs (hwf : ir.WellFormed) {sr : List (ℕ × ℕ)}
    {D : Derivations} (hv : ir.DerivationsValid primeNodes sr D) (hI : I.Registered ir)
    (hsel : ir.SelSound I) (j : ℕ) (e : ir.Env I) :
    Pr[c ← ir.ChalVal I j : ir.RealEvent j (e.setChal j c)] ≤ ir.realError I j :=
  probUniform_realEvent_le_ev hwf hv.eventsOk hI hsel j e

/-- **The realized program gives the program, or a realization event**, where every predicate has
a derivation that checks (`DerivationsValid`): in a sampled environment of the realized program at
a realized assignment (`hB`) within the value ranges `sr`, with every table valid (`DerivModel`).
By induction on the rank: a derivation cites only predicates and shared entries of smaller rank.
The events are the `RealEvent`s. -/
theorem satAt_or_realEvent_of_derivs {sr : List (ℕ × ℕ)} {D : Derivations}
    (hv : ir.DerivationsValid primeNodes sr D) (hM : ir.DerivModel I primeNodes)
    {e : ir.Env I} (he : Env.Sampled ir e) (h : ir.RealizedAt e)
    (hS : ∀ vN ∈ sr, ∀ i < (ir.value vN.1).size,
      ∃ n < vN.2, ir.reader e vN.1 i = ((n : ℕ) : (I (ir.valueField vN.1)).K))
    (hB : ir.BoundReads (ir.reader e)) : ir.SatAt e ∨ ∃ j, ir.RealEvent j e := by
  by_cases hev : ∃ j, ir.RealEvent j e
  · exact .inr hev
  push Not at hev
  have hno : ∀ {P : Prop}, (P ∨ ∃ j, ir.RealEvent j e) → P := fun h =>
    h.resolve_right fun ⟨j, hj⟩ => hev j hj
  -- the predicates and shared entries of rank below `n` hold
  have hgood : ∀ n, CitesHold e D.ctx n := by
    intro n
    induction n with
    | zero => exact ⟨fun _ _ h => absurd h (Nat.not_lt_zero _), fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
    | succ n ih =>
      have hpred : ∀ pid < ir.predicates.length, D.ctx.rank pid = n →
          ir.HoldsAt e (ir.predicate pid).body := fun pid hpid hrk =>
        hno (derivStepsB_sound hM he h hS hB hpid (hrk ▸ ih) (hv.checks pid hpid))
      refine ⟨fun q hq hlt => ?_, fun k f hlt hf => ?_⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with hlt | heq
        · exact ih.1 q hq hlt
        · exact hpred q hq heq
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with hlt | heq
        · exact ih.2 k f hlt hf
        · have hk : k < D.shared.length := by
            by_contra hk
            simp [Derivations.ctx, List.getElem?_eq_none (Nat.le_of_not_lt hk)] at hf
          have hf' : (D.shared.getD k default).fact = f := by
            simp only [Derivations.ctx, List.getElem?_eq_getElem hk, Option.map_some,
              Option.some.injEq] at hf
            simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk] using hf
          rw [← hf']
          exact hno (entryB_sound hM he h hS hB (heq ▸ ih) (hv.shared k hk))
  refine .inl ⟨fun p hp => ?_, h.types⟩
  obtain ⟨pid, hpid, rfl⟩ := exists_index_of_mem hp
  exact (hgood (D.ctx.rank pid + 1)).1 pid hpid (Nat.lt_succ_self _)

end Sound

/-! ## The check in ranges

`derivsB` splits into checks of ranges of predicates `[i, j)` (`DerivsPredsIn`, each from a walk,
`derivsPredsB`) and of shared entries (`derivsSharedIn`), which join with no re-check and give the
check from `[0, n)`, `n` at least the list's length (`derivsB_of_parts`), with the tables, the values
bound to their digits (`derivsRestB`) and the order of the listed derivations (`derivsOrderB`). A
range of predicates is checked in one walk of the predicates from `i` (`dropK`) merged with the
listed derivations from the first one at `i` or later (`dropLtK`); the order of the listed
derivations, checked once, makes the walk's merge read each predicate's listed steps. -/

/-- **The listed steps of predicate `pid`**: those of the first derivation listed for it. -/
def listedSteps : List (ℕ × List Step) → ℕ → Option (List Step)
  | [], _ => none
  | d :: ds, pid => if d.1 = pid then some d.2 else listedSteps ds pid

theorem sparseSteps_eq_listed :
    ∀ (ds : List (ℕ × List Step)) (pid : ℕ),
      sparseSteps ds pid = (listedSteps ds pid).getD (defaultSteps pid)
  | [], _ => rfl
  | d :: ds, pid => by
    by_cases h : d.1 = pid
    · simp [sparseSteps, listedSteps, h]
    · simp only [sparseSteps, listedSteps, h, if_false]
      exact sparseSteps_eq_listed ds pid

theorem listedSteps_of_lt : ∀ {ds : List (ℕ × List Step)} {pid : ℕ}, (∀ d ∈ ds, pid < d.1) →
    listedSteps ds pid = none
  | [], _, _ => rfl
  | d :: ds, pid, h => by
    have h1 := h d (by simp)
    simp only [listedSteps, if_neg (Nat.ne_of_gt h1)]
    exact listedSteps_of_lt fun d' hd' => h d' (by simp [hd'])

/-- **The listed derivations from the first one at `i` or later**, by the recursor
(`dropLtK_eq`). -/
noncomputable def dropLtK (i : ℕ) (ds : List (ℕ × List Step)) : List (ℕ × List Step) :=
  @List.rec (ℕ × List Step) (fun _ => List (ℕ × List Step)) []
    (fun d ds' ih => cond (Nat.blt d.1 i) ih (d :: ds')) ds

/-- **The listed derivations from the first one at `i` or later**: the code compiled for
`dropLtK`. -/
def dropLtC (i : ℕ) (ds : List (ℕ × List Step)) : List (ℕ × List Step) :=
  ds.dropWhile fun d => Nat.blt d.1 i

theorem dropLtK_eq (i : ℕ) : ∀ ds : List (ℕ × List Step), dropLtK i ds = dropLtC i ds
  | [] => rfl
  | d :: ds => by
    change cond (Nat.blt d.1 i) (dropLtK i ds) (d :: ds) = _
    rw [dropLtC, List.dropWhile_cons]
    cases Nat.blt d.1 i
    · rfl
    · exact dropLtK_eq i ds

@[csimp] theorem dropLtK_csimp : @dropLtK = @dropLtC := by
  funext i ds
  exact dropLtK_eq i ds

theorem listedSteps_dropLtC {i pid : ℕ} (hi : i ≤ pid) :
    ∀ ds : List (ℕ × List Step), listedSteps (dropLtC i ds) pid = listedSteps ds pid
  | [] => rfl
  | d :: ds => by
    rw [dropLtC, List.dropWhile_cons]
    by_cases h : d.1 < i
    · have hb : Nat.blt d.1 i = true := by rw [Nat.blt_eq]; exact h
      simp only [hb, listedSteps, show d.1 ≠ pid by omega, ite_true, ite_false]
      exact listedSteps_dropLtC hi ds
    · have hb : Nat.blt d.1 i = false := by
        rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]; exact h
      simp [hb]

theorem dropLtC_ge {i : ℕ} :
    ∀ {ds : List (ℕ × List Step)}, ds.Pairwise (fun a b => a.1 < b.1) →
      ∀ e ∈ dropLtC i ds, i ≤ e.1
  | [], _ => by simp [dropLtC]
  | d :: ds, hs => by
    rw [dropLtC, List.dropWhile_cons]
    rw [List.pairwise_cons] at hs
    by_cases h : d.1 < i
    · have hb : Nat.blt d.1 i = true := by rw [Nat.blt_eq]; exact h
      simp only [hb, ite_true]
      exact dropLtC_ge hs.2
    · have hb : Nat.blt d.1 i = false := by
        rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]; exact h
      simp only [hb, Bool.false_eq_true, ite_false, List.mem_cons, forall_eq_or_imp]
      exact ⟨by omega, fun e he => by have := hs.1 e he; omega⟩

theorem dropLtC_pairwise {i : ℕ} :
    ∀ {ds : List (ℕ × List Step)}, ds.Pairwise (fun a b => a.1 < b.1) →
      (dropLtC i ds).Pairwise (fun a b => a.1 < b.1)
  | [], _ => by simp [dropLtC]
  | d :: ds, hs => by
    rw [dropLtC, List.dropWhile_cons]
    cases Nat.blt d.1 i
    · exact hs
    · exact dropLtC_pairwise (List.pairwise_cons.1 hs).2

/-- **The listed derivations are in increasing order of predicate**, as a check. -/
def chainLtB : List (ℕ × List Step) → Bool
  | d :: e :: ds => Nat.blt d.1 e.1 && chainLtB (e :: ds)
  | _ => true

theorem pairwise_of_chainLtB :
    ∀ {ds : List (ℕ × List Step)}, chainLtB ds = true → ds.Pairwise (fun a b => a.1 < b.1)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | d :: e :: ds, h => by
    simp only [chainLtB, Bool.and_eq_true, Nat.blt_eq] at h
    have ih := pairwise_of_chainLtB h.2
    refine List.Pairwise.cons (fun x hx => ?_) ih
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact Nat.lt_trans h.1 ((List.pairwise_cons.1 ih).1 x hx)

section

variable (ir : RealizedProgram)

/-- **The listed derivations are in increasing order of predicate, each of a predicate of the
program**, as a check. -/
def derivsOrderB (D : Derivations) : Bool :=
  chainLtB D.derivs && D.derivs.all fun d => Nat.blt d.1 ir.predicates.length

/-- **A predicate's derivation checks** (`allDerivsB`'s step): its listed steps `o`, or else a
field `equal` (`defaultOkB`). -/
def derivStepB (primeNodes : ℕ → List String) (sr : List (ℕ × ℕ)) (D : Derivations) (pid : ℕ)
    (pr : Predicate) : Option (List Step) → Bool
  | some s => ir.derivB primeNodes sr D.ctx pid pr.body s && modCiteB D.shared pr.body s
  | none => defaultOkB pr.body

/-- **`derivsB`'s checks at predicate `pid`** (`pr`), with its listed steps `o`: its derivation,
its MAC realization, its lookup's shape, its field row and its product form. -/
def derivPredB (primeNodes : ℕ → List String) (sr : List (ℕ × ℕ)) (S : Structure)
    (D : Derivations) (pid : ℕ) (pr : Predicate) (o : Option (List Step)) : Bool :=
  ir.derivStepB primeNodes sr D pid pr o && (!derivCrossB pr.body || ir.macOkB pid pr.body) &&
    ir.lookupCoreB pid pr.body && ir.fieldRowOkB S pid pr.body && ir.productValidB pr.body

/-- **`n` predicates' checks from `pid` on**, the predicates `ps` merged with the listed
derivations `ds` (from the first at `pid` or later), by the recursors (`derivsWalkN_eq`): a
derivation listed at `pid` gives its steps, else none is, its head being of a later predicate. -/
noncomputable def derivsWalkN (primeNodes : ℕ → List String) (sr : List (ℕ × ℕ)) (S : Structure)
    (D : Derivations) (n : ℕ) : List Predicate → List (ℕ × List Step) → ℕ → Bool :=
  @Nat.rec (fun _ => List Predicate → List (ℕ × List Step) → ℕ → Bool) (fun _ _ _ => true)
    (fun _ ih ps ds pid => @List.casesOn Predicate (fun _ => Bool) ps true fun pr ps' =>
      @List.casesOn (ℕ × List Step) (fun _ => Bool) ds
        (ir.derivPredB primeNodes sr S D pid pr none && ih ps' [] (pid + 1))
        fun d ds' => cond (Nat.beq d.1 pid)
          (ir.derivPredB primeNodes sr S D pid pr (some d.2) && ih ps' ds' (pid + 1))
          (Nat.blt pid d.1 && ir.derivPredB primeNodes sr S D pid pr none &&
            ih ps' (d :: ds') (pid + 1))) n

/-- **`derivsWalkN`, by structural recursion**: the code compiled for it. -/
def derivsWalkC (primeNodes : ℕ → List String) (sr : List (ℕ × ℕ)) (S : Structure)
    (D : Derivations) : ℕ → List Predicate → List (ℕ × List Step) → ℕ → Bool
  | 0, _, _, _ => true
  | _ + 1, [], _, _ => true
  | n + 1, pr :: ps, [], pid =>
    ir.derivPredB primeNodes sr S D pid pr none && derivsWalkC primeNodes sr S D n ps [] (pid + 1)
  | n + 1, pr :: ps, d :: ds, pid =>
    cond (Nat.beq d.1 pid)
      (ir.derivPredB primeNodes sr S D pid pr (some d.2) &&
        derivsWalkC primeNodes sr S D n ps ds (pid + 1))
      (Nat.blt pid d.1 && ir.derivPredB primeNodes sr S D pid pr none &&
        derivsWalkC primeNodes sr S D n ps (d :: ds) (pid + 1))

theorem derivsWalkN_eq (primeNodes : ℕ → List String) (sr : List (ℕ × ℕ)) (S : Structure)
    (D : Derivations) : ∀ n ps ds pid,
      ir.derivsWalkN primeNodes sr S D n ps ds pid = ir.derivsWalkC primeNodes sr S D n ps ds pid
  | 0, _, _, _ => rfl
  | _ + 1, [], _, _ => rfl
  | n + 1, pr :: ps, [], pid => by
    change (ir.derivPredB primeNodes sr S D pid pr none &&
      ir.derivsWalkN primeNodes sr S D n ps [] (pid + 1)) = _
    rw [derivsWalkN_eq primeNodes sr S D n, derivsWalkC]
  | n + 1, pr :: ps, d :: ds, pid => by
    change cond (Nat.beq d.1 pid)
      (ir.derivPredB primeNodes sr S D pid pr (some d.2) &&
        ir.derivsWalkN primeNodes sr S D n ps ds (pid + 1))
      (Nat.blt pid d.1 && ir.derivPredB primeNodes sr S D pid pr none &&
        ir.derivsWalkN primeNodes sr S D n ps (d :: ds) (pid + 1)) = _
    rw [derivsWalkN_eq primeNodes sr S D n, derivsWalkN_eq primeNodes sr S D n, derivsWalkC]

@[csimp] theorem derivsWalkN_csimp : @derivsWalkN = @derivsWalkC := by
  funext ir primeNodes sr S D n ps ds pid
  exact ir.derivsWalkN_eq primeNodes sr S D n ps ds pid

/-- **`derivsB`'s checks of the predicates `[i, j)`**, in one walk (`derivsWalkN`). -/
def derivsPredsB (primeNodes : ℕ → List String) (sr : List (ℕ × ℕ)) (S : Structure)
    (D : Derivations) (i j : ℕ) : Bool :=
  ir.derivsWalkN primeNodes sr S D (j - i) (dropK i ir.predicates) (dropLtK i D.derivs) i

/-- **`derivsB`'s checks hold at the predicates `[i, j)`**, each with its listed steps. -/
def DerivsPredsIn (primeNodes : ℕ → List String) (sr : List (ℕ × ℕ)) (S : Structure)
    (D : Derivations) (i j : ℕ) : Prop :=
  ∀ pid, i ≤ pid → pid < j → pid < ir.predicates.length →
    ir.derivPredB primeNodes sr S D pid (ir.predicates.getD pid default)
      (listedSteps D.derivs pid) = true

/-- **`derivsB`'s check of the shared entries `[i, j)`.** -/
def derivsSharedIn (primeNodes : ℕ → List String) (sr : List (ℕ × ℕ)) (D : Derivations)
    (i j : ℕ) : Bool :=
  allIdxIn (fun k e => ir.entryB primeNodes sr D.ctx k e) D.shared i j

/-- **`derivsB`'s checks of the tables and of the values bound to their digits.** -/
def derivsRestB : Bool :=
  (List.range ir.tables.length).all ir.tableOkB && allIdx (fun _ x => ir.boundOkV x) ir.values 0

end

section

variable {ir : RealizedProgram} {primeNodes : ℕ → List String} {sr : List (ℕ × ℕ)}
  {S : Structure} {D : Derivations}

theorem derivsWalkC_sound :
    ∀ {n : ℕ} {ps : List Predicate} {ds : List (ℕ × List Step)} {pid : ℕ},
      ds.Pairwise (fun a b => a.1 < b.1) → (∀ e ∈ ds, pid ≤ e.1) →
      ir.derivsWalkC primeNodes sr S D n ps ds pid = true →
      ∀ k < n, k < ps.length →
        ir.derivPredB primeNodes sr S D (pid + k) (ps.getD k default)
          (listedSteps ds (pid + k)) = true
  | 0, _, _, _, _, _, _, k, hk, _ => absurd hk (Nat.not_lt_zero k)
  | _ + 1, [], _, _, _, _, _, k, _, hk => absurd hk (Nat.not_lt_zero k)
  | n + 1, pr :: ps, [], pid, _, _, h, k, hkn, hkl => by
    rw [derivsWalkC, Bool.and_eq_true] at h
    rcases k with _ | k
    · exact h.1
    · have := derivsWalkC_sound List.Pairwise.nil (by simp) h.2 k (by omega) (by simpa using hkl)
      rw [show pid + (k + 1) = pid + 1 + k by omega]
      simpa [listedSteps] using this
  | n + 1, pr :: ps, d :: ds, pid, hs, hge, h, k, hkn, hkl => by
    rw [derivsWalkC] at h
    have hs' := List.pairwise_cons.1 hs
    by_cases hq : d.1 = pid
    · rw [show Nat.beq d.1 pid = true by rw [Nat.beq_eq]; exact hq, Bool.cond_true,
        Bool.and_eq_true] at h
      rcases k with _ | k
      · simpa [listedSteps, hq] using h.1
      · have := derivsWalkC_sound hs'.2 (fun e he => by have := hs'.1 e he; omega) h.2 k
          (by omega) (by simpa using hkl)
        rw [show pid + (k + 1) = pid + 1 + k by omega]
        have hne : d.1 ≠ pid + 1 + k := by omega
        simpa [listedSteps, hne] using this
    · rw [show Nat.beq d.1 pid = false by rw [Bool.eq_false_iff, ne_eq, Nat.beq_eq]; exact hq,
        Bool.cond_false,
        Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq] at h
      obtain ⟨⟨hlt, h0⟩, h1⟩ := h
      rcases k with _ | k
      · have hn : listedSteps (d :: ds) pid = none :=
          listedSteps_of_lt fun e he => by
            rcases List.mem_cons.1 he with rfl | he
            · exact hlt
            · exact Nat.lt_trans hlt (hs'.1 e he)
        simpa [hn] using h0
      · have := derivsWalkC_sound hs (fun e he => by
          rcases List.mem_cons.1 he with rfl | he
          · omega
          · have := hs'.1 e he; omega) h1 k (by omega) (by simpa using hkl)
        rw [show pid + (k + 1) = pid + 1 + k by omega]
        simpa using this

/-- **A range's walk gives its predicates' checks**, the listed derivations in order. -/
theorem derivsPredsIn_of_B {i j : ℕ} (ho : ir.derivsOrderB D = true)
    (h : ir.derivsPredsB primeNodes sr S D i j = true) : ir.DerivsPredsIn primeNodes sr S D i j := by
  have hs := pairwise_of_chainLtB (Bool.and_eq_true _ _ ▸ ho).1
  unfold derivsPredsB at h
  rw [derivsWalkN_eq, dropK_eq, dropLtK_eq] at h
  intro pid hi hj hl
  have := derivsWalkC_sound (dropLtC_pairwise hs) (fun e he => dropLtC_ge hs e he) h (pid - i)
    (by omega) (by simp; omega)
  rw [Nat.add_sub_cancel' hi, listedSteps_dropLtC hi, List.getD_eq_getElem?_getD,
    List.getElem?_drop, Nat.add_sub_cancel' hi] at this
  rwa [List.getD_eq_getElem?_getD]

/-- **Two consecutive ranges of predicates** check as one. -/
theorem DerivsPredsIn.append {i j k : ℕ} (h₁ : ir.DerivsPredsIn primeNodes sr S D i j)
    (h₂ : ir.DerivsPredsIn primeNodes sr S D j k) : ir.DerivsPredsIn primeNodes sr S D i k :=
  fun pid hi hk hl => if hj : pid < j then h₁ pid hi hj hl else h₂ pid (by omega) hk hl

theorem derivsSharedIn_append {i j k : ℕ} (h₁ : ir.derivsSharedIn primeNodes sr D i j = true)
    (h₂ : ir.derivsSharedIn primeNodes sr D j k = true) :
    ir.derivsSharedIn primeNodes sr D i k = true :=
  allIdxIn_append h₁ h₂

theorem zipIdx_all_eq_allIdx {α : Type} (g : α × ℕ → Bool) :
    ∀ (l : List α) (n : ℕ), (l.zipIdx n).all g = allIdx (fun k x => g (x, k)) l n
  | [], _ => rfl
  | x :: xs, n => by
    rw [List.zipIdx_cons, List.all_cons, allIdx_cons, zipIdx_all_eq_allIdx g xs (n + 1)]

theorem allDerivsB_of_forall :
    ∀ {pid : ℕ} {ps : List Predicate} {ds : List (ℕ × List Step)},
      ds.Pairwise (fun a b => a.1 < b.1) → (∀ e ∈ ds, pid ≤ e.1 ∧ e.1 < pid + ps.length) →
      (∀ k < ps.length, ir.derivStepB primeNodes sr D (pid + k) (ps.getD k default)
        (listedSteps ds (pid + k)) = true) →
      ir.allDerivsB primeNodes sr D.ctx D.shared pid ps ds = true
  | _, [], [], _, _, _ => by simp [allDerivsB]
  | pid, [], d :: _, _, hr, _ => by
    have := hr d (by simp)
    simp at this
    omega
  | pid, pr :: ps, [], _, _, hk => by
    have h0 := hk 0 (by simp)
    simp only [listedSteps, derivStepB, List.getD_cons_zero] at h0
    rw [allDerivsB, h0, Bool.true_and]
    refine allDerivsB_of_forall List.Pairwise.nil (by simp) fun k hkl => ?_
    have := hk (k + 1) (by simpa using hkl)
    rw [show pid + (k + 1) = pid + 1 + k by omega] at this
    simpa [listedSteps] using this
  | pid, pr :: ps, d :: ds, hs, hr, hk => by
    have hs' := List.pairwise_cons.1 hs
    have hd := hr d (by simp)
    unfold allDerivsB
    by_cases hq : d.1 = pid
    · simp only [hq, ↓reduceIte]
      have h0 := hk 0 (by simp)
      simp only [Nat.add_zero, listedSteps, hq, ite_true, derivStepB, List.getD_cons_zero] at h0
      rw [h0, Bool.true_and]
      refine allDerivsB_of_forall hs'.2 (fun e he => ?_) fun k hkl => ?_
      · have := hs'.1 e he
        have := hr e (by simp [he])
        simp only [List.length_cons] at this
        omega
      · have := hk (k + 1) (by simpa using hkl)
        rw [show pid + (k + 1) = pid + 1 + k by omega] at this
        have hne : d.1 ≠ pid + 1 + k := by omega
        simpa [listedSteps, hne] using this
    · simp only [hq, ↓reduceIte]
      have hlt : pid < d.1 := by omega
      have h0 := hk 0 (by simp)
      have hn : listedSteps (d :: ds) pid = none :=
        listedSteps_of_lt fun e he => by
          rcases List.mem_cons.1 he with rfl | he
          · exact hlt
          · exact Nat.lt_trans hlt (hs'.1 e he)
      simp only [Nat.add_zero, hn, derivStepB, List.getD_cons_zero] at h0
      rw [h0, Bool.true_and]
      refine allDerivsB_of_forall hs (fun e he => ?_) fun k hkl => ?_
      · have h1 := hr e he
        simp only [List.length_cons] at h1
        rcases List.mem_cons.1 he with rfl | he
        · omega
        · have := hs'.1 e he
          omega
      · have := hk (k + 1) (by simpa using hkl)
        rw [show pid + (k + 1) = pid + 1 + k by omega] at this
        simpa using this

/-- **`derivsB` from its checks of the predicates and of the shared entries**, each on `[0, n)`
for `n` at least the list's length, of the tables and the bound values, and of the order of the
listed derivations. -/
theorem derivsB_of_parts {np ns : ℕ} (ho : ir.derivsOrderB D = true)
    (h : ir.derivsRestB = true) (hp : ir.DerivsPredsIn primeNodes sr S D 0 np)
    (hnp : ir.predicates.length ≤ np) (hs : ir.derivsSharedIn primeNodes sr D 0 ns = true)
    (hns : D.shared.length ≤ ns) : ir.derivsB primeNodes sr S D = true := by
  unfold derivsOrderB at ho
  rw [Bool.and_eq_true, List.all_eq_true] at ho
  have hpw := pairwise_of_chainLtB ho.1
  have hp' : ∀ k < ir.predicates.length, ir.derivPredB primeNodes sr S D k
      (ir.predicates.getD k default) (listedSteps D.derivs k) = true :=
    fun k hk => hp k (Nat.zero_le _) (by omega) hk
  have hpart : ∀ k < ir.predicates.length,
      ir.derivStepB primeNodes sr D k (ir.predicates.getD k default)
          (listedSteps D.derivs k) = true ∧
        (!derivCrossB (ir.predicates.getD k default).body ||
          ir.macOkB k (ir.predicates.getD k default).body) = true ∧
        ir.lookupCoreB k (ir.predicates.getD k default).body = true ∧
        ir.fieldRowOkB S k (ir.predicates.getD k default).body = true ∧
        ir.productValidB (ir.predicates.getD k default).body = true := fun k hk => by
    have := hp' k hk
    simp only [derivPredB, Bool.and_eq_true] at this
    exact ⟨this.1.1.1.1, this.1.1.1.2, this.1.1.2, this.1.2, this.2⟩
  have h1 : ir.allDerivsB primeNodes sr D.ctx D.shared 0 ir.predicates D.derivs = true :=
    allDerivsB_of_forall hpw (fun e he => by
      have := ho.2 e he
      rw [Nat.blt_eq] at this
      omega) fun k hk => by simpa using (hpart k hk).1
  have hall : ∀ (f : ℕ → Predicate → Bool),
      (∀ k < ir.predicates.length, f k (ir.predicates.getD k default) = true) →
        allIdx f ir.predicates 0 = true := fun f hf => by
    rw [allIdx_iff]
    intro k hk
    simpa using hf k hk
  have h2 : (D.shared.zipIdx.all fun ek => ir.entryB primeNodes sr D.ctx ek.2 ek.1) = true := by
    rw [zipIdx_all_eq_allIdx]
    exact allIdx_of_allIdxIn hs hns
  have h4 : (ir.predicates.zipIdx.all fun pq => !derivCrossB pq.1.body || ir.macOkB pq.2 pq.1.body)
      = true := by
    rw [zipIdx_all_eq_allIdx]
    exact hall (fun k p => !derivCrossB p.body || ir.macOkB k p.body) fun k hk => (hpart k hk).2.1
  have h5 : allIdx (fun pid p => ir.lookupCoreB pid p.body) ir.predicates 0 = true :=
    hall _ fun k hk => (hpart k hk).2.2.1
  have h7 : allIdx (fun pid p => ir.fieldRowOkB S pid p.body) ir.predicates 0 = true :=
    hall _ fun k hk => (hpart k hk).2.2.2.1
  have h8 : allIdx (fun _ p => ir.productValidB p.body) ir.predicates 0 = true :=
    hall _ fun k hk => (hpart k hk).2.2.2.2
  simp only [derivsRestB, Bool.and_eq_true] at h
  unfold derivsB
  simp only [h1, h2, h.1, h4, h.2, h5, h7, h8, Bool.and_self]

end

end GordieHowe.RealizedProgram
