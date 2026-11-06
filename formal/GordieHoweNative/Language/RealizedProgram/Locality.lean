-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.Realizations.RealizeGrouped

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.RealizedProgram.Locality`

The definitions of `GordieHowe.Language.RealizedProgram.Locality` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/RealizedProgram/Locality.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export

section

variable (ir : RealizedProgram)

/-- **What of the committed assignment value `v` reads**, with `n` levels (as `RealizedProgram.read`): a
committed value, a pad copy or a late value itself, a value bound to its digits the values of its
expression, a public expression, an opaque value or a bit view what the values it reads read;
nothing for a message, a statement value, a constant or a challenge. -/
def asgReads : ℕ → ℕ → List ℕ
  | 0, _ => []
  | n + 1, v =>
    match (ir.value v).kind with
    | .priv => [v]
    | .padCopy _ _ => [v]
    | .late => [v]
    | .bound e => ir.exprNodes e
    | .pub (.expr e) => (ir.exprNodes e).flatMap (asgReads n)
    | .pub (.opaque _ args) => args.flatMap (asgReads n)
    | .bits w _ => asgReads n w
    | _ => []

variable {ir I}

variable (ir) in
/-- **The step of `asgReads`.** -/
def asgReadsStep (r : ℕ → List ℕ) (v : ℕ) : List ℕ :=
  match (ir.value v).kind with
  | .priv => [v]
  | .padCopy _ _ => [v]
  | .late => [v]
  | .bound e => ir.exprNodes e
  | .pub (.expr e) => (ir.exprNodes e).flatMap r
  | .pub (.opaque _ args) => args.flatMap r
  | .bits w _ => r w
  | _ => []

variable (ir) in
/-- **The step of `asgReadsT`**: what value `v` reads of the committed assignment, from what the
values it reads read (`r`). -/
def asgStep (r : ℕ → List ℕ) (v : ℕ) (x : Value) : List ℕ :=
  match x.kind with
  | .priv => [v]
  | .padCopy _ _ => [v]
  | .late => [v]
  | .bound e => ir.exprNodes e
  | .pub (.expr e) => insertAll [] ((ir.nodesOf e).flatMap r)
  | .pub (.opaque _ args) => insertAll [] (args.flatMap r)
  | .bits w _ => r w
  | _ => []

variable (ir) in
/-- **The table of what each value reads of the committed assignment** (`asgReads`). -/
def asgReadsT : NatTrie (List ℕ) := memo ir.asgStep [] ir.values

/-- The assignment-read table is the memoized assignment recurrence. -/
theorem asgReadsT_eq_memo (ir : RealizedProgram) :
    ir.asgReadsT = memo ir.asgStep [] ir.values := rfl

end

/-- **The domain of a predicate body**: a field `equal`'s, an `in`'s or a `mod_q`'s; none for a
cross-field `equal`, which relates two domains. -/
def PredBody.domain? : PredBody → Option ℕ
  | .equal d .. => some d
  | .mem d .. => some d
  | .mod d .. => some d
  | .cross .. => none

/-- **The value of an input block**: a public, committed, pad or view block's; none for a
realization input, filler or batch pads. -/
def InputBlock.value? : InputBlock → Option ℕ
  | .pub u _ _ => some u
  | .committed u _ _ => some u
  | .pad u _ _ => some u
  | .view u _ _ => some u
  | _ => none

section

variable (ir : RealizedProgram)

/-- **The values the rows of table `t` read** (`RealizedProgram.tableRow`): none for a range, the first
column for a committed table, the values the expression reads for a table of an expression's
coordinates. -/
def tableNodes (t : ℕ) : List ℕ :=
  match (ir.table t).rows with
  | .range _ => []
  | .columns cols => [cols.headD 0]
  | .expr e' => ir.exprNodes e'

/-- **The values the LogUp identity of group `g` of table `t` reads, the challenges' values
read through `ch`**: the value holding the table's challenge, the values of its members' needles,
its histograms, and the values its rows read (`tableNodes`). -/
def logupNodesWith (ch : ℕ → Option ℕ) (t g : ℕ) : List ℕ :=
  (ch (ir.alphaOf t)).toList ++
    (ir.members t g).flatMap (fun m => ir.exprNodes (ir.needleExpr m.pred m.needle)) ++
    (ir.groupOf t g).staticMult.toList ++ (ir.groupOf t g).lateMult.toList ++
    ir.tableNodes t

/-- **The values the H half of cross-field `equal` `p` reads, the challenges' values read through
`ch`** (`MacHHolds`): the value holding the key, the tag, the values of the H operand. -/
def macHNodesWith (ch : ℕ → Option ℕ) (p : ℕ) : List ℕ :=
  match (ir.predicate p).body with
  | .cross _ x _ _ _ real => (ch real.key).toList ++ real.tag :: ir.exprNodes x
  | _ => []

/-- **The values outside domain `d`**, as a bit set (`failBits`), for `inDomB`. -/
def domFailBits (d : ℕ) : ℕ := failBits (fun _ (x : Value) => x.domain == d) ir.values 0

/-- **Value `u` is of domain `d`, as a test** (`inDomB_eq`): one `Nat.testBit` of `domFailBits`, where
`(ir.value u).domain` looks the value up in the values' trie. -/
def inDomB (d u : ℕ) : Bool :=
  bitTest (ir.domFailBits d) ir.values.length ((default : Value).domain == d) u

/-- **What each value reads of the committed assignment, in value order** (`asgReadsT`'s entries,
`getD_memoList`), for a walk of them. -/
def asgReadsL : List (List ℕ) := memoList ir.asgStep [] ir.values

/-- The assignment-read rows are the memoized assignment recurrence in order. -/
theorem asgReadsL_eq_memoList :
    ir.asgReadsL = memoList ir.asgStep [] ir.values := rfl

/-- **The values reading the committed assignment outside domain `d`**, as a bit set (`failBits`
over `asgReadsL`, each read tested by `inDomB`). -/
def readsInFail (d : ℕ) : ℕ := failBits (fun _ rs => rs.all (ir.inDomB d)) ir.asgReadsL 0

/-- **`ReadsIn`, through the tables** (`readsInB_eq`): a value of the program whose bit is clear in
`readsInFail`, one `Nat.testBit` where a lookup of the reads' table and of each value read costs a
walk down a trie. -/
def readsInB (d v : ℕ) : Bool :=
  decide (v < ir.values.length) && bitTest (ir.readsInFail d) ir.asgReadsL.length true v

end

end GordieHowe.RealizedProgram
