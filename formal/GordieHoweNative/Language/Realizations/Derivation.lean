-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.Realizations.Derivation.Disjoint
public import GordieHoweNative.Language.Realizations.Derivation.FieldMod
public import GordieHoweNative.Language.Realizations.Derivation.Grouped
public import GordieHoweNative.Language.Realizations.Derivation.Mac
public import GordieHoweNative.Language.Realizations.Derivation.OpIvl
public import GordieHoweNative.Language.Realizations.Derivation.Solve
public import GordieHoweNative.Language.Realizations.Derivation.TableKernel

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.Realizations.Derivation`

The definitions of `GordieHowe.Language.Realizations.Derivation` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/Realizations/Derivation.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export

section

variable (ir : RealizedProgram)

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
  | .src v s =>
    if ir.srcGuard body.dom v = true then
      (ir.srcFact primeNodes sr fs body.dom v s).or (ir.tableKernelFact sr ctx self body.dom v s)
    else none
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
  | .productMod ks => ir.productModFact fs pid body ks
  | .circuitAssert _ => none
  | .inputPremise _ => none

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

/-- **The derivation `ss` of a `mod_0` cites intervals of both sides at its first two steps**: its
step `0` cites an interval of the left side and its step `1` of the right side (`citesIvlB` on the
one step at each position; the compiler emits the two citations first); `true` off `mod_0`s. -/
def modCiteB (sh : List SharedEntry) : PredBody → List Step → Bool
  | .mod d q a b _, ss =>
    q != 0 || (citesIvlB sh d a (ss.take 1) && citesIvlB sh d b ((ss.drop 1).take 1))
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

/-- **A `mod_q` `pid` in the field form has its field equation as a row**, as a check whose
failure names `pid`: the modulus is the characteristic `p > 2` (slot `0`), and the structure
records' `modField` record of `pid` names its row (`fieldRowPtrE`: the field equation
`e − e' = 0`, of role `realization pid`); `.ok` on every other predicate. -/
def fieldRowOkE (S : Structure) (pid : ℕ) : PredBody → Except StructFailure Unit
  | .mod d q _ _ real =>
    if q != 0 && decide (real.form = .field) then
      Twin.seqE (Twin.guardE (q == ir.charOf (ir.domainField d) && decide (2 < q))
        ⟨pid, 0, .slotMismatch⟩) (ir.fieldRowPtrE S pid)
    else .ok ()
  | _ => .ok ()

/-- **`fieldRowOkE` as a `Bool`.** -/
def fieldRowOkB (S : Structure) (pid : ℕ) (b : PredBody) : Bool := Twin.okB (ir.fieldRowOkE S pid b)

/-- **A product-form `mod_q` passes the structural check** (`productOkB`) in a field of
characteristic above `2`; any other predicate body needs nothing. -/
def productValidB (b : PredBody) : Bool :=
  !b.isProductMod || (ir.productOkB b && decide (2 < ir.charOf (ir.domainField b.dom)))

/-- **The checker of `DerivationsValid`**: one derivation per predicate and every shared entry,
each checking at its rank, and the field rows at the structure records' pointers (`S`). -/
def derivsB (primeNodes : ℕ → List String) (sr : List (ℕ × ℕ)) (S : Structure)
    (D : Derivations) : Bool :=
  ir.allDerivsB primeNodes sr D.ctx D.shared 0 ir.predicates D.derivs &&
    (D.shared.zipIdx.all fun ek => ir.entryB primeNodes sr D.ctx ek.2 ek.1) &&
    (List.range ir.tables.length).all ir.tableOkB &&
    (ir.predicates.zipIdx.all fun pq => !derivCrossB pq.1.body || ir.macOkB pq.2 pq.1.body) &&
    allIdx (fun pid p => ir.lookupCoreB pid p.body) ir.predicates 0 &&
    allIdx (fun _ x => ir.boundOkV x) ir.values 0 &&
    allIdx (fun pid p => ir.fieldRowOkB S pid p.body) ir.predicates 0 &&
    allIdx (fun _ p => ir.productValidB p.body) ir.predicates 0

end

end GordieHowe.RealizedProgram
