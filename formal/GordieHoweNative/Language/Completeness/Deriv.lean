-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.Completeness.Reader
public import GordieHoweNative.Language.Completeness.Spectral

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.Completeness.Deriv`

The definitions of `GordieHowe.Language.Completeness.Deriv` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/Completeness/Deriv.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export

/-- **A step of a completeness derivation**: premises are indices into the facts of the earlier
steps; program items are ids. -/
inductive CStep where
  /-- A soundness step whose rule reads only its premises and the program (`pureStepFact`). -/
  | pure (s : Step)
  /-- The fact `k` is the body of the derivation's predicate (`concludeFact`). -/
  | conclude (k : ℕ)
  /-- The derivation's predicate is a source predicate, and holds. -/
  | source
  /-- The derivation's predicate is the quotient's `in` of the one-digit `mod_q` `m`, whose honest
  quotient lies in its range (`oneDigitQuotAtB` at the source values' intervals). -/
  | quotIn (m : ℕ)
  /-- The derivation's predicate is the reconstruction or top row of the two-sided or digit lookup
  `p`, whose digits are generated as its digits (`digitRowB`). -/
  | digitRow (p : ℕ)
  /-- The derivation's predicate plays role `role` (`macRoleAtB`) in the MAC of site `i` of the
  `macSite` structure record `g` (`macSiteAt`), whose MAC, tail (a grouped, a one-digit or an
  ungrouped digit tail) and interval facts check (`macBaseCB`, `macTailCB`, `macIvlB`). -/
  | macRow (g i : ℕ) (role : MacRole)
  /-- The derivation's predicate is the Boolean check of a pad copy (`padCopyBoolB`). -/
  | padBool
  /-- The derivation's predicate is the digit lookup whose record is quotient digit `j` of the
  committed-digits `mod_q` `m`, its digits generated as committed digits (`commLookupCB`), `m` with
  its honest-quotient facts (`commModCB`). -/
  | commIn (m j : ℕ)
  /-- The derivation's predicate is the field equation of the committed-digits `mod_q` `m`, whose
  quotient digit `j` is the record of the lookup `lks[j]` (`commRowCB`). -/
  | commRow (m : ℕ) (lks : List ℕ)
  /-- The body of predicate `q` holds: `q`'s derivation has a smaller rank. -/
  | hyp (q : ℕ)
  /-- The derivation's predicate is the products predicate of the spectrally realized convolution
  `k` of `RealizedProgram.convs`, whose honest facts check (`specHonestCB`). -/
  | specProd (k : ℕ)
  /-- The derivation's predicate realizes the field equation of the source predicate `m` through
  the spectrally realized convolutions (`specRowCB`). -/
  | specRow (m : ℕ)
  /-- The derivation's predicate is the field equation of a source field-form `mod_q`
  (`fieldRowRealB`). -/
  | fieldRow
  /-- The derivation's predicate is the tail of the MAC check over a field of characteristic `2` of
  site `i` of the `macSite` structure record `g` (`macSiteAt`, `twoTail`), whose facts check
  (`twoMacCB`). -/
  | twoTail (g i : ℕ)
  deriving Repr, Inhabited

/-- **The completeness derivations of a program**: one per predicate (aligned with the
predicates), and the predicates' ranks packed into one natural (`packRanks`, read by `rankOf`), so
reading a rank costs one shift. -/
structure CDerivations where
  /-- One derivation per predicate. -/
  derivs : List (List CStep)
  /-- The predicates' ranks, packed. -/
  ranks : ℕ
  deriving Repr, Inhabited

section

variable (ir : RealizedProgram)

/-- **Predicate `pr` is a row of the two-sided or digit lookup `p`** whose facts hold at the
generators `G` (`DigitLookupFactsC`): the reconstruction or the top row of a two-sided lookup, the
reconstruction row of a digit lookup. -/
def digitRowB (G : Gens) (p : ℕ) (pr : Predicate) : Bool :=
  match (ir.predicate p).body with
  | .mem d [rec] (.range N) (.lookup r) =>
    decide (ir.DigitLookupFactsC G p d rec N r) &&
      ((r.kind == .twoSided && (ir.reconMatch d rec r pr.body || ir.topMatch d N rec r pr.body)) ||
        (r.kind == .digits && ir.reconMatch d rec r pr.body))
  | _ => false

/-- **The conclusion of a step** of the completeness derivation of predicate `pid` (`pr`, zipped
with the derivations) at rank `self`, with packed ranks `P`, from the facts `fs` of the earlier
steps, reading the structure records `S`, at a certificate reader (the MAC sites' and the
committed-digits `mod_q`s' facts its shared verdicts); `none` when it does not check. -/
def CReader.cstepFact (ir : RealizedProgram) [r : CReader] (primeNodes : ℕ → List String) (S : Structure) (G : Gens)
    (P self pid : ℕ) (pr : Predicate) (fs : List Fact) : CStep → Option Fact
  | .pure s => ir.pureStepFact primeNodes [] pr.body fs s
  | .conclude k => ir.concludeFact fs pid pr.body k
  | .source => if ir.inSource pr = true then some (.holds pid) else none
  | .quotIn m =>
    if ir.oneDigitQuotAtB (ir.srcLeafIvl primeNodes S) m pid = true ∧
        PReader.noGenPredB ir pr.body = true
    then some (.holds pid) else none
  | .digitRow p =>
    if ir.digitRowB G p pr = true ∧ PReader.noGenPredB ir pr.body = true then some (.holds pid)
    else none
  | .macRow g i role =>
    match ir.macSiteAt S g i with
    | some st =>
      if r.site .base g i = true ∧ r.site .tail g i = true ∧ r.site .ivl g i = true ∧
          ir.macRoleAtB primeNodes S st role pid = true
      then some (.holds pid) else none
    | none => none
  | .padBool =>
    if ir.padCopyBoolB pid = true ∧ PReader.noGenPredB ir pr.body = true then some (.holds pid)
    else none
  | .commIn m j =>
    if ir.commLookupCB G pid m j = true ∧ r.commMod m = true ∧
        PReader.noGenPredB ir pr.body = true
    then some (.holds pid) else none
  | .commRow m lks =>
    if CReader.commRowCB ir G m lks pr = true ∧ PReader.noGenPredB ir pr.body = true
    then some (.holds pid) else none
  | .hyp q => if q < r.nPreds ∧ rankOf P q < self then some (.holds q) else none
  | .specProd k =>
    if (ir.convs[k]?.map (·.products)) = some pid ∧
        ir.specHonestCB primeNodes S G k = true ∧ PReader.noGenPredB ir pr.body = true
    then some (.holds pid) else none
  | .specRow m =>
    if ir.specRowCB primeNodes S G m pid = true ∧ PReader.noGenPredB ir pr.body = true
    then some (.holds pid) else none
  | .fieldRow =>
    if ir.fieldRowRealB pid = true ∧ PReader.noGenPredB ir pr.body = true then some (.holds pid)
    else none
  | .twoTail g i =>
    match ir.macSiteAt S g i with
    | some st =>
      if r.site .two g i = true ∧ pid = ir.twoTail st then some (.holds pid) else none
    | none => none

/-- **The conclusion of a step** of the completeness derivation of predicate `pid` (`pr`, zipped
with the derivations) at rank `self`, with packed ranks `P`, from the facts `fs` of the earlier
steps, reading the structure records `S` (`CReader.cstepFact` at the program); `none` when it does
not check. -/
def cstepFact (primeNodes : ℕ → List String) (S : Structure) (G : Gens) (P self pid : ℕ)
    (pr : Predicate) (fs : List Fact) (s : CStep) : Option Fact :=
  @CReader.cstepFact ir (CReader.ofProgram ir primeNodes S G) primeNodes S G P self pid pr fs s

/-- **Run the steps** of a completeness derivation, accumulating their facts, at a certificate
reader. -/
def CReader.runCSteps (ir : RealizedProgram) [r : CReader] (primeNodes : ℕ → List String) (S : Structure) (G : Gens)
    (P self pid : ℕ) (pr : Predicate) : List Fact → List CStep → Option (List Fact)
  | fs, [] => some fs
  | fs, s :: ss =>
    (CReader.cstepFact ir primeNodes S G P self pid pr fs s).bind fun f =>
      CReader.runCSteps ir primeNodes S G P self pid pr (fs ++ [f]) ss

/-- **Run the steps** of a completeness derivation, accumulating their facts
(`CReader.runCSteps` at the program). -/
def runCSteps (primeNodes : ℕ → List String) (S : Structure) (G : Gens) (P self pid : ℕ)
    (pr : Predicate) (fs : List Fact) (ss : List CStep) : Option (List Fact) :=
  @CReader.runCSteps ir (CReader.ofProgram ir primeNodes S G) primeNodes S G P self pid pr fs ss

/-- **The completeness derivation `steps` of predicate `pid` (`pr`) checks** at rank `self`, at a
certificate reader: every step checks and the last fact is `holds pid`. -/
def CReader.cderivStepsB (ir : RealizedProgram) [CReader] (primeNodes : ℕ → List String) (S : Structure) (G : Gens)
    (P self pid : ℕ) (pr : Predicate) (steps : List CStep) : Bool :=
  match CReader.runCSteps ir primeNodes S G P self pid pr [] steps with
  | some fs =>
    match fs.getLast? with
    | some (.holds p) => p == pid
    | _ => false
  | none => false

/-- **The completeness derivation `steps` of predicate `pid` (`pr`) checks** at rank `self`
(`CReader.cderivStepsB` at the program): every step checks and the last fact is `holds pid`. -/
def cderivStepsB (primeNodes : ℕ → List String) (S : Structure) (G : Gens) (P self pid : ℕ)
    (pr : Predicate) (steps : List CStep) : Bool :=
  @CReader.cderivStepsB ir (CReader.ofProgram ir primeNodes S G) primeNodes S G P self pid pr steps

/-- **The completeness derivations `ds` of the predicates `ps` from `pid` on check**, the two
lists zipped, at a certificate reader. -/
def CReader.allCDerivsB (ir : RealizedProgram) [CReader] (primeNodes : ℕ → List String) (S : Structure) (G : Gens)
    (P : ℕ) : ℕ → List Predicate → List (List CStep) → Bool
  | _, [], [] => true
  | pid, pr :: ps, s :: ds =>
    CReader.cderivStepsB ir primeNodes S G P (rankOf P pid) pid pr s &&
      CReader.allCDerivsB ir primeNodes S G P (pid + 1) ps ds
  | _, _, _ => false

/-- **The completeness derivations `ds` of the predicates `ps` from `pid` on check**, the two
lists zipped (`CReader.allCDerivsB` at the program). -/
def allCDerivsB (primeNodes : ℕ → List String) (S : Structure) (G : Gens) (P pid : ℕ)
    (ps : List Predicate) (ds : List (List CStep)) : Bool :=
  @CReader.allCDerivsB ir (CReader.ofProgram ir primeNodes S G) primeNodes S G P pid ps ds

/-- **The checker of the completeness derivations** at a certificate reader: one per predicate,
each checking at its rank, the MAC steps read at the structure records `S`. -/
def CReader.cderivsB (ir : RealizedProgram) [r : CReader] (primeNodes : ℕ → List String) (S : Structure) (G : Gens)
    (D : CDerivations) : Bool :=
  CReader.allCDerivsB ir primeNodes S G D.ranks 0 ir.predicates D.derivs

/-- **The checker of the completeness derivations** (`CReader.cderivsB` at the program): one per
predicate, each checking at its rank, the MAC steps read at the structure records `S`. -/
def cderivsB (primeNodes : ℕ → List String) (S : Structure) (G : Gens) (D : CDerivations) :
    Bool :=
  @CReader.cderivsB ir (CReader.ofProgram ir primeNodes S G) primeNodes S G D

end

end GordieHowe.RealizedProgram
