-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.RealizedProgram.Source
public import GordieHoweNative.Language.RealizedProgram.Reader

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.RealizedProgram.SourceCheck`

The definitions of `GordieHowe.Language.RealizedProgram.SourceCheck` that the source part's checks
run (the source values as a bit set, the dependencies through the closure table), in the
Mathlib-free library `GordieHoweNative`, which Lake compiles to a shared library
(`precompileModules`): native mode runs the checkers as compiled code. The declarations keep their
names. Their lemmas are in `GordieHowe/Language/RealizedProgram/SourceCheck.lean`, which imports
this module.

**The compiled checker.** The source part's four checks (`sourceChecksB`) read the source values'
bit set (`nonSourceBits`) and the flags of the shared expressions' closures (`closFlagBits`), tables
the kernel evaluates once, closed terms, and compiled code would evaluate at every read. A **source
reader** (`SReader`) adds their reads to a program reader (`PReader`): `SReader.ofProgram ir` reads
them as the kernel definitions do, `SReader.ofCtx (SCtx.build ir)` from a context built once per
check. Each check is its generic form here at `ofProgram`, by definition; the two readers are equal
(`SReader.ofCtx_build`), and compiled code runs the checks at the context (`sourceChecksBC`, the code
of `sourceChecksB` by `sourceChecksB_csimp`; both in
`GordieHowe/Language/RealizedProgram/SourceCheck.lean`).
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export

section

variable (ir : RealizedProgram)

/-- **The values the definition of a value `x` reads, through the table**: `valueDepsM` at a
value read from the walk (`valueDepsM_eq`). -/
def valueDepsOf (x : Value) : List ℕ :=
  match x.kind with
  | .pub (.expr e) => ir.nodesOf e
  | .pub (.opaque _ args) => args
  | .bits w _ => [w]
  | _ => []

/-- **The values of another role than `source`**, as a bit set (`failBits`): bit `v` set when value
`v` exists and its role is not `source`. -/
def nonSourceBits : ℕ := failBits (fun _ (x : Value) => x.role == .source) ir.values 0

/-- **Value `v` is a source value, as a test**: its bit is clear in `nonSourceBits` (`srcB_iff`). A
value past the end is the default value, of role `source`, as `IsSourceValue` reads it. -/
def srcB (v : ℕ) : Bool := bitTest ir.nonSourceBits ir.values.length true v

/-- **`inSource` with the value read by `srcB`** (`inSourceB_eq`). -/
def inSourceB (p : Predicate) : Bool :=
  match p.role with
  | .source => true
  | .type v => ir.srcB v
  | .realization _ => false

/-- **`SourceRead` as a test**, a late value read by `srcB` (`srcReadB_iff`). -/
def srcReadB : Read → Bool
  | .chal c => ir.chalIsSource c
  | .late u => ir.srcB u
  | .pad _ => false

/-- **The source part's four checks** (`SourceValid.of_sourceChecksB`): the challenges' roles, the
source predicates' values (each expression's through the flags' table `closFlag`), the source values'
dependencies (`valueDepsOf`) and run reads (`readsL`), every value read tested by `srcB`. -/
def sourceChecksB : Bool :=
  (List.range ir.challenges.length).all ir.chalRoleOk &&
    ir.predicates.all (fun p => !ir.inSourceB p ||
      (p.body.exprs.all (ir.closFlag Expr.directNodes ir.srcB ·.2) &&
        (ir.tableCols p.body).all ir.srcB)) &&
    allIdx (fun _ x => !(x.role == .source) || (ir.valueDepsOf x).all ir.srcB) ir.values 0 &&
    allIdx (fun _ xr => !(xr.1.role == .source) || xr.2.all ir.srcReadB)
      (ir.values.zip ir.readsL) 0

end

/-- **A source reader**: what the compiled source checks read of a program, the program reader's
reads, the source values' test and the shared expressions' closure flags. -/
class SReader extends PReader where
  /-- Value `v` is a source value (`srcB`). -/
  src : ℕ → Bool
  /-- Every value an expression reads is a source value (`closFlag Expr.directNodes srcB`). -/
  srcFlag : Expr → Bool

/-- **The source reader of the kernel definitions**: the tables where they are read. -/
@[instance_reducible] def SReader.ofProgram (ir : RealizedProgram) : SReader where
  toPReader := PReader.ofProgram ir
  src := ir.srcB
  srcFlag := ir.closFlag Expr.directNodes ir.srcB

/-- **The context of a compiled source check**: the program reader's context, the source values'
bit set and the closure flags' bit set, each computed once (`SCtx.build`). -/
structure SCtx where
  /-- The program reader's context. -/
  base : PCtx
  /-- The number of values. -/
  n : ℕ
  /-- `nonSourceBits`. -/
  srcBits : ℕ
  /-- `closFlagBits Expr.directNodes srcB`. -/
  flagBits : ℕ
  /-- The number of the closure flags (`closFlagL`). -/
  nFlags : ℕ

/-- **The source reader of a context**: the program reader's arrays and the context's bit sets. -/
@[instance_reducible] def SReader.ofCtx (c : SCtx) : SReader where
  toPReader := PReader.ofCtx c.base
  src v := bitTest c.srcBits c.n true v
  srcFlag e := (e.directNodes.all fun v => bitTest c.srcBits c.n true v) &&
    e.refs.all (bitTest c.flagBits c.nFlags false)

/-- **The context of program `ir`**: the program reader's context and the bit sets, the closure
flags read through the source values' bit set built first. -/
def SCtx.build (ir : RealizedProgram) : SCtx :=
  let n := ir.values.length
  let srcBits := ir.nonSourceBits
  let src := fun v => bitTest srcBits n true v
  let fl := ir.closFlagL Expr.directNodes src
  { base := PCtx.build ir
    n := n
    srcBits := srcBits
    flagBits := failBits (fun _ b => b) fl 0
    nFlags := fl.length }

namespace SReader

variable (ir : RealizedProgram) [r : SReader]

/-- `inSourceB`, at the reader. -/
def inSourceB (p : Predicate) : Bool :=
  match p.role with
  | .source => true
  | .type v => r.src v
  | .realization _ => false

/-- `srcReadB`, at the reader. -/
def srcReadB : Read → Bool
  | .chal c => ir.chalIsSource c
  | .late u => r.src u
  | .pad _ => false

/-- `valueDepsOf`, at the reader: a public expression's values through the closure table. -/
def valueDepsOf (x : Value) : List ℕ :=
  match x.kind with
  | .pub (.expr e) => PReader.nodesOf e
  | .pub (.opaque _ args) => args
  | .bits w _ => [w]
  | _ => []

/-- `sourceChecksB`, at the reader. -/
def sourceChecksB : Bool :=
  (List.range ir.challenges.length).all ir.chalRoleOk &&
    ir.predicates.all (fun p => !inSourceB p ||
      (p.body.exprs.all (r.srcFlag ·.2) && (ir.tableCols p.body).all r.src)) &&
    allIdx (fun _ x => !(x.role == .source) || (valueDepsOf x).all r.src) ir.values 0 &&
    allIdx (fun _ xr => !(xr.1.role == .source) || xr.2.all (srcReadB ir))
      (ir.values.zip r.readsL) 0

end SReader

/-- **The source part's checks at a context built once**: the code compiled for `sourceChecksB`
(`sourceChecksB_csimp`). -/
def sourceChecksBC (ir : RealizedProgram) : Bool :=
  let c := SCtx.build ir
  @SReader.sourceChecksB ir (SReader.ofCtx c)

end GordieHowe.RealizedProgram
