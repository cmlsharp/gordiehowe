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
public import GordieHowe.Language.Realizations.Derivation.Mac
public import GordieHowe.Language.Realizations.Derivation.Grouped

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
-/

namespace GordieHowe.RealizedProgram

open Export Range IOP

section

variable (ir : RealizedProgram) {I : Interp}

/-- **The conclusion of a step** of a derivation of rank `self`, for predicate `pid` of body `body`
(a shared entry: `entryBody d`, which no rule concludes), from the facts `fs` of the earlier
steps, its side conditions checked; `none` when it does not check. -/
def stepFact (primeNodes : ℕ → List String) (sr : List (ℕ × ℕ)) (ctx : DerivCtx) (self pid : ℕ)
    (body : PredBody) (fs : List Fact) : Step → Option Fact
  | .realized p => if p = pid then realizedOf body else ir.realizedFact p
  | .subst e₁ e₂ => ir.substFact body.dom e₁ e₂
  | .linear cs e₁ e₂ => ir.linearFact fs body.dom cs e₁ e₂
  | .lookup ms => ir.lookupFact ms
  | .rangeNat k => ir.rangeNatFact fs body.dom k
  | .holdsIn k => ir.holdsInFact fs k
  | .src v s => if ir.srcGuard body.dom v = true then ir.srcFact primeNodes sr fs body.dom v s else none
  | .ivlNat k => ir.ivlNatFact fs body.dom k
  | .ivlExpr ks x lo hi => ir.ivlExprFact fs body.dom ks x lo hi
  | .ivlSolve k ks a j lo hi => ir.ivlSolveFact fs body.dom k ks a j lo hi
  | .ivlApply k a e lo hi => ir.ivlApplyFact fs body.dom k a e lo hi
  | .ivlLogic ks e => ir.ivlLogicFact fs body.dom ks e
  | .ivlMeet a b => ivlMeetFact fs a b
  | .ivlDisjoint a b => ir.ivlDisjointFact fs body.dom a b
  | .fieldDvd k a b => ir.fieldDvdFact fs body.dom k a b
  | .natIvl k => natIvlFact fs k
  | .transport k j => ir.transportFact fs k j
  | .natComp k j => ir.natCompFact fs body.dom k j
  | .natBool p => ir.natBoolFact p
  | .natLin k ks => ir.natLinFact fs body.dom k ks
  | .liftConst k a => ir.liftConstFact fs body k a
  | .lift k a b => ir.liftFact fs k a b
  | .digits k ds T => ir.digitsFact fs body.dom k ds T
  | .congr k => congrFact fs pid body k
  | .mac ts h ivs => ir.macFact primeNodes ctx self pid body fs ts h ivs
  | .linop s => ir.linopFact fs body.dom s
  | .conclude k => ir.concludeFact fs pid body k
  | .hyp q => if q < ir.predicates.length ∧ ctx.rank q < self then some (.holds q) else none
  | .fact k => if ctx.srank k < self then ctx.sfact k else none
  | .inDom d s => stepFact primeNodes sr ctx self pid (entryBody d) fs s
  | .groupedMod rows ivs => ir.groupedFact ctx self pid body fs rows ivs

/-- **The facts of a derivation**: one pass over the steps, each step's fact appended. -/
def runSteps (primeNodes : ℕ → List String) (sr : List (ℕ × ℕ)) (ctx : DerivCtx) (self pid : ℕ)
    (body : PredBody) : List Fact → List Step → Option (List Fact)
  | fs, [] => some fs
  | fs, s :: ss =>
    (ir.stepFact primeNodes sr ctx self pid body fs s).bind fun f =>
      runSteps primeNodes sr ctx self pid body (fs ++ [f]) ss

/-- **The steps `steps` of predicate `pid`, of body `body` and rank `self`, check**: every step
checks and the last fact is `holds pid`. -/
def derivStepsB (primeNodes : ℕ → List String) (sr : List (ℕ × ℕ)) (ctx : DerivCtx)
    (self pid : ℕ) (body : PredBody) (steps : List Step) : Bool :=
  match ir.runSteps primeNodes sr ctx self pid body [] steps with
  | some fs =>
    match fs.getLast? with
    | some (.holds p) => p == pid
    | _ => false
  | none => false

/-- **A cross-field `equal` has a valid MAC realization** (`MacRealizable`: hosted or two-tail,
its tails and H predicate among the program's). -/
def macOkB (pid : ℕ) (body : PredBody) : Bool := ir.macCoreOkB pid body

/-- Whether a predicate body is a cross-field `equal`. -/
def derivCrossB : PredBody → Bool
  | .cross _ _ _ _ _ _ => true
  | _ => false

/-- **The derivation `steps` of predicate `pid`, of body `body`, checks** at its rank
(`derivStepsB`; a cross-field `equal` by its `mac` step). -/
def derivB (primeNodes : ℕ → List String) (sr : List (ℕ × ℕ)) (ctx : DerivCtx) (pid : ℕ)
    (body : PredBody) (steps : List Step) : Bool :=
  ir.derivStepsB primeNodes sr ctx (ctx.rank pid) pid body steps

/-- **Shared entry `k` checks**: its steps, at its rank, conclude its fact. -/
def entryB (primeNodes : ℕ → List String) (sr : List (ℕ × ℕ)) (ctx : DerivCtx) (k : ℕ)
    (en : SharedEntry) : Bool :=
  match ir.runSteps primeNodes sr ctx (ctx.srank k) ir.predicates.length (entryBody en.fact.dom)
      [] en.steps with
  | some fs => (fs.getLast?.map fun f => f.beq en.fact).getD false
  | none => false

/-- **An interval source that holds at the honest prover's reader**: a constant's entries, a
declared bound, a `nat` premise. -/
def honestSrcB : IvlSrc → Bool
  | .const => true
  | .declared _ => true
  | .nat _ => true
  | _ => false

/-- **An interval source that holds at the reader of a typed environment where every equality
predicate holds**: a value of a prime node (`prime`, its type), an opaque bit (`opaqueBit`, the
opaque call's evaluation), a root of cited equalities (`quadRoot`, `rootSet`), and a leaf whose
sum with a constant is a range (`shift`). -/
def typedSrcB : IvlSrc → Bool
  | .prime => true
  | .opaqueBit => true
  | .quadRoot _ _ => true
  | .rootSet _ => true
  | .shift _ => true
  | _ => false

/-- **A step whose fact holds at the honest prover's reader**: the reader-generic rules, a lookup
(every needle is a row of its table), a cited predicate (`hyp`, every predicate holds) and the
facts read from one (`holdsIn`, `natBool`); never `realized`, `mac`, `congr`, `conclude`, `fact`
or `groupedMod`. -/
def honestStepB : Step → Bool
  | .subst _ _ => true
  | .linear _ _ _ => true
  | .lookup _ => true
  | .rangeNat _ => true
  | .holdsIn _ => true
  | .src _ s => honestSrcB s || typedSrcB s
  | .ivlNat _ => true
  | .ivlExpr _ _ _ _ => true
  | .ivlSolve _ _ _ _ _ _ => true
  | .ivlApply _ _ _ _ _ => true
  | .ivlLogic _ _ => true
  | .ivlMeet _ _ => true
  | .ivlDisjoint _ _ => true
  | .fieldDvd _ _ _ => true
  | .natIvl _ => true
  | .transport _ _ => true
  | .natComp _ _ => true
  | .natBool _ => true
  | .natLin _ _ => true
  | .liftConst _ _ => true
  | .lift _ _ _ => true
  | .digits _ _ _ => true
  | .linop _ => true
  | .hyp _ => true
  | .inDom _ s => honestStepB s
  | _ => false

/-- **The steps `ss` cite a shared entry of `sh` concluding an interval of `x` in domain `d`**
(`fact k`), whose steps all hold at the honest prover's reader (`honestStepB`). -/
def citesIvlB (sh : List SharedEntry) (d : ℕ) (x : Expr) : List Step → Bool
  | [] => false
  | .fact k :: ss =>
    (match sh[k]? with
      | some en =>
        (match en.fact with
          | .ivl d' x' _ _ => d' == d && x'.beq x
          | _ => false) && en.steps.all honestStepB
      | none => false) || citesIvlB sh d x ss
  | _ :: ss => citesIvlB sh d x ss

/-- **The derivation `ss` of a `mod_0` cites intervals of both sides** (`citesIvlB`); `true` off
`mod_0`s. -/
def modCiteB (sh : List SharedEntry) : PredBody → List Step → Bool
  | .mod d q a b _, ss => q != 0 || (citesIvlB sh d a ss && citesIvlB sh d b ss)
  | _, _ => true

/-- **An unlisted predicate's body**: a field `equal`, which `defaultSteps` derive
(`derivB_default_of_equal`). -/
def defaultOkB : PredBody → Bool
  | .equal _ _ _ _ => true
  | _ => false

/-- **The derivations of the predicates `ps` from `pid` on check**: one pass merging `ps` with the
sparse list `ds` (sorted by predicate); a listed predicate checks its steps, an unlisted one is a
field `equal` (`defaultOkB`, which `defaultSteps` derive); an entry out of order or out of range is
left over and fails. -/
def allDerivsB (primeNodes : ℕ → List String) (sr : List (ℕ × ℕ)) (ctx : DerivCtx)
    (sh : List SharedEntry) : ℕ → List Predicate → List (ℕ × List Step) → Bool
  | _, [], [] => true
  | _, [], _ :: _ => false
  | pid, pr :: ps, [] => defaultOkB pr.body && allDerivsB primeNodes sr ctx sh (pid + 1) ps []
  | pid, pr :: ps, d :: ds =>
    if d.1 = pid then
      ir.derivB primeNodes sr ctx pid pr.body d.2 && modCiteB sh pr.body d.2 &&
        allDerivsB primeNodes sr ctx sh (pid + 1) ps ds
    else defaultOkB pr.body && allDerivsB primeNodes sr ctx sh (pid + 1) ps (d :: ds)

/-- **A lookup `in`'s interval-free shape** (`LookupCore`), as a Boolean; `true` off lookups. -/
def lookupCoreB (pid : ℕ) : PredBody → Bool
  | .mem d recs set (.lookup r) =>
    match r.kind with
    | .direct => ir.directOkB pid d recs set r
    | .digits => decide (ir.DigitsOk pid d recs set r)
    | .twoSided => decide (ir.TwoSidedOk pid d recs set r)
    | .complement => decide (ir.ComplementCore pid d recs set r)
    | _ => false
  | _ => true

/-- **A `mod_q` in the field form has its field equation as a row**: the modulus is the
characteristic `p > 2` and the field equation `e − e' = 0` is a field `equal` of the program
(`fieldRowB`); `true` on every other predicate. -/
def fieldRowOkB : PredBody → Bool
  | .mod d q e e' real =>
    !(q != 0 && decide (real.form = .field)) ||
      (q == ir.charOf (ir.domainField d) && decide (2 < q) &&
        ir.predicates.any fun p => ir.fieldRowB d e e' p.body)
  | _ => true

/-- **The checker of `DerivationsValid`**: one derivation per predicate and every shared entry,
each checking at its rank. -/
def derivsB (primeNodes : ℕ → List String) (sr : List (ℕ × ℕ)) (D : Derivations) : Bool :=
  ir.allDerivsB primeNodes sr D.ctx D.shared 0 ir.predicates D.derivs &&
    (D.shared.zipIdx.all fun ek => ir.entryB primeNodes sr D.ctx ek.2 ek.1) &&
    (List.range ir.tables.length).all ir.tableOkB &&
    (ir.predicates.zipIdx.all fun pq => !derivCrossB pq.1.body || ir.macOkB pq.2 pq.1.body) &&
    allIdx (fun pid p => ir.lookupCoreB pid p.body) ir.predicates 0 &&
    allIdx (fun _ x => ir.boundOkV x) ir.values 0 &&
    allIdx (fun _ p => ir.fieldRowOkB p.body) ir.predicates 0

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
holds (`hc`): the step's fact holds where its premises' do, or (`lookup`) a realization event
happens. -/
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
    exact .inl (srcFact_sound hM.wf hM.registered hM.lawful h hS hfs hg hf)
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
theorem derivationsValid_of_derivsB (hwf : ir.WellFormed) {sr : List (ℕ × ℕ)} {D : Derivations}
    (h : ir.derivsB primeNodes sr D = true) : ir.DerivationsValid primeNodes sr D := by
  unfold derivsB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  have hk := allDerivsB_sound h1
  rw [allIdx_iff] at h5
  rw [allIdx_values_iff] at h6
  rw [allIdx_iff] at h7
  refine ⟨fun pid hpid => by simpa [predicate, Derivations.stepsOf] using (hk pid hpid).1,
    fun pid hpid => by simpa [predicate, Derivations.stepsOf] using (hk pid hpid).2,
    fun k hk' => ?_,
    fun t ht => (tableOkB_iff hwf t).1 (List.all_eq_true.1 h3 t (List.mem_range.2 ht)),
    fun p hp hc => ?_, fun pid hpid d recs set r hb => ?_,
    fun v hv => (boundOkV_iff hwf v).1 (h6 v hv), fun pid hpid d q e e' real hb hq hf => ?_⟩
  · have := List.all_eq_true.1 h2 (D.shared[k], k) (List.mem_iff_getElem.2
      ⟨k, by simpa using hk', by simp⟩)
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk'] using this
  · have := List.all_eq_true.1 h4 ((ir.predicate p), p) (List.mem_iff_getElem.2
      ⟨p, by simpa using hp, by simp [predicate, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hp]⟩)
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at this
    rcases this with h0 | h0
    · rw [hc] at h0
      cases h0
    · exact h0
  · have := h5 pid hpid
    simp only [Nat.zero_add] at this
    change ir.lookupCoreB pid (ir.predicate pid).body = true at this
    rw [hb] at this
    simp only [lookupCoreB] at this
    unfold LookupCore
    revert this
    cases r.kind <;> simp only [Bool.false_eq_true, imp_false, not_false_eq_true,
      decide_eq_true_eq, imp_self]
    exact (directOkB_iff hwf _ _ _ _ _).1
  · have := h7 pid hpid
    change ir.fieldRowOkB (ir.predicate pid).body = true at this
    rw [hb] at this
    simpa [fieldRowOkB, hq, hf, and_assoc] using this

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
derivations (`probUniform_realEvent_le_ev` at their structural checks). -/
theorem probUniform_realEvent_le_of_derivs (hwf : ir.WellFormed) {sr : List (ℕ × ℕ)}
    {D : Derivations} (hv : ir.DerivationsValid primeNodes sr D) (hI : I.Registered ir) (j : ℕ)
    (e : ir.Env I) :
    Pr[c ← ir.ChalVal I j : ir.RealEvent j (e.setChal j c)] ≤ ir.realError I j :=
  probUniform_realEvent_le_ev hwf hv.eventsOk hI j e

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

end GordieHowe.RealizedProgram
