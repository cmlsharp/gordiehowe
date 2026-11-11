-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.Completeness.CommDigits
public import GordieHoweNative.Language.Completeness.MacCheck

/-!
# GordieHowe: the certificate reader of the compiled completeness checker

The completeness checker reads, beside the program (`PReader`), the verdicts of checks that several
derivations and groups share: the facts of each MAC site (its MAC, tail and interval facts, read by
the five derivations of its rows, its cross-field `equal`'s predicate check and its mixed groups'
late members) and the honest-quotient facts of each committed-digits `mod_q` (read by the
derivations of its `in` predicates and of its field equation). A **certificate reader**
(`CReader`) adds them as fields:

* `CReader.ofProgram ir primeNodes S G` computes each verdict where it is read, as the kernel
  definitions do;
* `CReader.ofCtx (CCtx.build ir primeNodes S G)` reads them from a table of thunks built once per
  check, each verdict computed at its first read.

The two readers are equal (`CReader.ofCtx_build`, in
`GordieHowe/Language/Completeness/Reader.lean`).
-/

local notation "ℕ" => Nat

public section

namespace GordieHowe.RealizedProgram

open Export

/-- **A check of a MAC site** whose verdict the completeness checker shares: its MAC facts, tail
facts and interval facts, the MAC check over a field of characteristic `2`, and the ungrouped and
one-digit tails' facts. -/
inductive SiteCheck where
  | base
  | tail
  | ivl
  | two
  | digits
  | oneDigit

/-- **The checks of a MAC site, in order** (`SiteCheck.idx`). -/
@[expose] def SiteCheck.all : List SiteCheck := [.base, .tail, .ivl, .two, .digits, .oneDigit]

/-- **The position of a check in `SiteCheck.all`.** -/
@[expose] def SiteCheck.idx : SiteCheck → ℕ
  | .base => 0
  | .tail => 1
  | .ivl => 2
  | .two => 3
  | .digits => 4
  | .oneDigit => 5

/-- **Check `k` at MAC site `st`**, at the nodes `primeNodes`, the structure records `S` and the
generators `G`. -/
@[expose] def SiteCheck.eval (ir : RealizedProgram) (primeNodes : ℕ → List String) (S : Structure)
    (G : Gens) : SiteCheck → MacSite → Bool
  | .base, st => ir.macBaseCB primeNodes S G st
  | .tail, st => ir.macTailCB G st
  | .ivl, st => ir.macIvlB primeNodes S st
  | .two, st => ir.twoMacCB primeNodes G st
  | .digits, st => ir.digitsMacCB G st
  | .oneDigit, st => ir.oneDigitMacCB G st

/-- **Check `k` at site `i` of `macSite` record `g`** (`macSiteAt`); `false` without a site. -/
@[expose] def siteCheckAt (ir : RealizedProgram) (primeNodes : ℕ → List String) (S : Structure)
    (G : Gens) (k : SiteCheck) (g i : ℕ) : Bool :=
  match ir.macSiteAt S g i with
  | some st => k.eval ir primeNodes S G st
  | none => false

/-- **Check `k` at MAC site `st`**, at a program reader: the MAC, ungrouped digit tail and interval
facts through the reader (`PReader.macBaseB`, `PReader.digitsMacB`, `PReader.macIvlAtB`), the
other checks at the program (`SiteCheck.eval`). -/
@[expose] def SiteCheck.evalR (ir : RealizedProgram) [r : PReader] (primeNodes : ℕ → List String) (S : Structure)
    (G : Gens) : SiteCheck → MacSite → Bool
  | .base, st => PReader.macBaseB ir primeNodes S G st
  | .tail, st =>
    if (ir.macTailParts st).real.grouped.isSome then ir.groupedMacCB G st
    else if (ir.macTailParts st).real.isOneDigitTail then ir.oneDigitMacCB G st
    else PReader.digitsMacB ir G st
  | .ivl, st => PReader.macIvlAtB (ir.srcLeafIvl primeNodes S) ir st
  | .digits, st => PReader.digitsMacB ir G st
  | k, st => k.eval ir primeNodes S G st

/-- **Check `k` at site `i` of `macSite` record `g`** (`siteCheckAt`), at a program reader. -/
@[expose] def siteCheckAtR (ir : RealizedProgram) [r : PReader] (primeNodes : ℕ → List String) (S : Structure)
    (G : Gens) (k : SiteCheck) (g i : ℕ) : Bool :=
  match ir.macSiteAt S g i with
  | some st => SiteCheck.evalR ir primeNodes S G k st
  | none => false

/-- **A certificate reader**: a program reader with the verdicts the completeness checker
shares. -/
class CReader extends PReader where
  /-- Check `k` at site `i` of `macSite` record `g` (`siteCheckAt`). -/
  site : SiteCheck → ℕ → ℕ → Bool
  /-- The honest-quotient facts of the committed-digits `mod_q` `m` (`commModCB`). -/
  commMod : ℕ → Bool

/-- **The certificate reader of the kernel definitions**: each verdict computed where it is
read. -/
@[expose, instance_reducible] def CReader.ofProgram (ir : RealizedProgram)
    (primeNodes : ℕ → List String) (S : Structure) (G : Gens) : CReader where
  toPReader := PReader.ofProgram ir
  site := siteCheckAt ir primeNodes S G
  commMod := ir.commModCB primeNodes S

/-- **The context of a compiled completeness check**: the program's context, and the shared
verdicts as thunks (`site[g][i][k.idx]`, `commMod[m]`) with the functions they evaluate, which
also answer reads outside the tables. -/
structure CCtx where
  /-- The program's context. -/
  base : PCtx
  /-- The site checks. -/
  siteFn : SiteCheck → ℕ → ℕ → Bool
  /-- The site checks of every slot of every structure record, by record, slot and check. -/
  site : Array (Array (Array (Thunk Bool)))
  /-- The committed-digits `mod_q` checks. -/
  commModFn : ℕ → Bool
  /-- The committed-digits `mod_q` checks of every predicate. -/
  commMod : Array (Thunk Bool)

/-- **A thunk table's entry**, `f ()` where the table has none (`f` evaluated only then). -/
@[expose] def thunkAt (t : Array (Thunk Bool)) (j : ℕ) (f : Unit → Bool) : Bool :=
  match t[j]? with
  | some x => x.get
  | none => f ()

/-- **The certificate reader of a context**: the shared verdicts read from its thunks. -/
@[expose, instance_reducible] def CReader.ofCtx (c : CCtx) : CReader where
  toPReader := PReader.ofCtx c.base
  site k g i :=
    match c.site[g]? with
    | some a =>
      match a[i]? with
      | some t => thunkAt t k.idx fun _ => c.siteFn k g i
      | none => c.siteFn k g i
    | none => c.siteFn k g i
  commMod m := thunkAt c.commMod m fun _ => c.commModFn m

/-- **The thunks of `f` at `0, …, n − 1`.** -/
@[expose] def thunks (f : ℕ → Bool) (n : ℕ) : Array (Thunk Bool) :=
  ((List.range n).map fun j => Thunk.mk fun _ => f j).toArray

/-- **The context of a completeness check** of program `ir` at the nodes `primeNodes`, the structure
records `S` and the generators `G`: the program's context (`PCtx.build`), a thunk for each check of
each slot of each structure record, and one for each predicate's committed-digits check. -/
@[expose] def CCtx.build (ir : RealizedProgram) (primeNodes : ℕ → List String) (S : Structure)
    (G : Gens) : CCtx :=
  let base := PCtx.build ir
  let f := @siteCheckAtR ir (PReader.ofCtx base) primeNodes S G
  -- The interval inputs are shared and computed only when a committed-digit check reads them.
  let intervals := Thunk.mk fun _ => S.ivlTrie
  let ranges := Thunk.mk fun _ => ir.declaredRanges
  let cm := @PReader.commModCB (ir.ivlTab primeNodes intervals.get ranges.get) ir (PReader.ofCtx base)
  { base := base
    siteFn := f
    site := ((List.range S.gadgets.length).map fun g =>
      ((List.range ((S.gadgets[g]?.map (·.preds.length)).getD 0)).map fun i =>
        (SiteCheck.all.map fun k => Thunk.mk fun _ => f k g i).toArray).toArray).toArray
    commModFn := cm
    commMod := thunks cm ir.predicates.length }

namespace CReader

variable (ir : RealizedProgram) [r : CReader]

/-- **Predicate `pr` is the field equation of the committed-digits `mod_q` `m`** whose quotient
digit `j` is the record of the lookup `lks[j]`, as a check at a certificate reader: `m` has its
honest-quotient facts (the shared verdict `commMod`), `pr` is its field equation (`commRowB`), and
`lks` names one lookup per quotient digit with its facts (`commRecCB`). -/
@[expose] def commRowCB (G : Gens) (m : ℕ) (lks : List ℕ) (pr : Predicate) : Bool :=
  match (r.predicate m).body with
  | .mod d q e e' real =>
    r.commMod m && ir.commRowB d q e e' real pr.body &&
      lks.length == real.digits.length &&
      (List.range lks.length).all fun j => ir.commRecCB G (lks.getD j 0) m j
  | _ => false

/-- **A late member `m` of a mixed group at the late histogram `v` of table `t` reads a digit of the
tail of the MAC of site `st`**, site `i` of record `g` (`mixedMemberCB`), as a check at a
certificate reader: the site's MAC and interval facts (shared verdicts), and the needle is the lower
or the top digit of an ungrouped digit tail or the quotient of a one-digit tail. -/
@[expose] def mixedMemberCB (g i t v : ℕ) (st : MacSite) (m : Member) : Bool :=
  r.site .base g i && r.site .ivl g i &&
    ((r.site .digits g i && ir.lateMemberAtB st t v m &&
        decide (ir.macTopMax st < (r.value v).size)) ||
      (r.site .oneDigit g i && ir.lateMemberOneAtB st t m &&
        decide (ir.macQuotMax st < (r.value v).size)))

end CReader

variable (ir : RealizedProgram) (primeNodes : ℕ → List String) in
/-- **Predicate `pr` is the field equation of the committed-digits `mod_q` `m`** whose quotient
digit `j` is the record of the lookup `lks[j]`, as a check (`CReader.commRowCB` at the program):
`m` has its honest-quotient facts (`commModCB`), `pr` is its field equation (`commRowB`), and `lks`
names one lookup per quotient digit with its facts (`commRecCB`). -/
@[expose] def commRowCB (S : Structure) (G : Gens) (m : ℕ) (lks : List ℕ) (pr : Predicate) :
    Bool :=
  @CReader.commRowCB ir (CReader.ofProgram ir primeNodes S G) G m lks pr

end GordieHowe.RealizedProgram
