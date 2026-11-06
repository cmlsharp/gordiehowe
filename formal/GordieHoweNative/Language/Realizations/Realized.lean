-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.Realizations.ProductForm

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.Realizations.Realized`

The definitions of `GordieHowe.Language.Realizations.Realized` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/Realizations/Realized.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export
/-- **A member of a table group's LogUp sum**: `(pred, needle, first, count)`, the coordinates
`[first, first + count)` of needle `needle` (an index into the `in` predicate's needles) of the `in`
predicate `pred` (`TableGroup.members`). -/
abbrev Member : Type := ℕ × ℕ × ℕ × ℕ

namespace Member

/-- The `in` predicate of a member. -/
def pred (m : Member) : ℕ := m.1

/-- The needle of a member, an index into its predicate's needles. -/
def needle (m : Member) : ℕ := m.2.1

/-- The first coordinate of a member. -/
def first (m : Member) : ℕ := m.2.2.1

/-- The number of coordinates of a member. -/
def count (m : Member) : ℕ := m.2.2.2

end Member

section

variable (ir : RealizedProgram)

/-- **The lookup realization of a predicate body**: an `in` realized by lookups. -/
def lookupOf? : PredBody → Option LookupRealization
  | .mem _ _ _ (.lookup r) => some r
  | _ => none

/-- **Needle `n` of predicate `p`**, an expression of its lookup realization (a default expression
when `p` has none). -/
def needleExpr (p n : ℕ) : Expr :=
  ((lookupOf? (ir.predicate p).body).map fun r => r.needles.getD n default).getD default

/-- **The size `T` of table `t`**: the range `[0, T)`, the size of a committed table's first
column (the one a single-record `in` reads, `RealizedProgram.InRows`), or the length of the expression whose
coordinates are the rows. -/
def tableSize (t : ℕ) : ℕ :=
  match (ir.table t).rows with
  | .range T => T
  | .columns cols => (ir.value (cols.headD 0)).size
  | .expr e' => ir.exprLen e'

/-- **The challenge `α` of table `t`.** -/
def alphaOf (t : ℕ) : ℕ := (ir.table t).alpha

/-- **Group `g` of table `t`.** -/
def groupOf (t g : ℕ) : TableGroup := (ir.table t).groups.getD g default

/-- **The members of group `g` of table `t`**, in the order its LogUp sum reads them. -/
def members (t g : ℕ) : List Member := (ir.groupOf t g).members

/-- **The number of needles of group `g` of table `t`**: the coordinates of its members. -/
def groupCount (t g : ℕ) : ℕ := ((ir.members t g).map Member.count).sum

/-- **The number of groups of table `t`.** -/
def groupCountOf (t : ℕ) : ℕ := (ir.table t).groups.length

/-- **The largest table challenge `j` avoids**: `tmax` for the sampler `fieldMinusTables (range
tmax)`, `0` otherwise. -/
def tmaxOf (j : ℕ) : ℕ :=
  match (ir.challenge j).sampler with
  | .fieldMinusTables (.range T) => T
  | _ => 0

/-- Whether a predicate body is a field `equal`. -/
def _root_.GordieHowe.RealizedProgram.PredBody.isEqual : PredBody → Bool
  | .equal _ _ _ _ => true
  | _ => false

/-- Whether a predicate body is a `mod_q` in the product form (`ModForm.isProduct`). -/
def _root_.GordieHowe.RealizedProgram.PredBody.isProductMod : PredBody → Bool
  | .mod _ _ _ _ real => real.form.isProduct
  | _ => false

/-- **The parameters of a public-table selection** (`lib/gordiehowe/lib/table.h`, `select_row`):
the domain; the record's values a product form's kernel reads (`records`), each a run of blocks of
`n` coordinates; the table's value of `rows` rows of `width` entries; the row map's leaf transform
on a block (the transform of length `n` at the root `psi`, in natural order when `natural`, else in
scheme order); and the challenge `chal`
of the selection's fingerprint with the fingerprint's degree `deg` in it. A record of one block
(`records = [v]`, `v` of `n` coordinates, `width = n`) is the single-leaf selection. -/
structure SelShape where
  /-- The domain. -/
  domain : ℕ
  /-- The record's values a kernel reads. -/
  records : List ℕ
  /-- The table's value. -/
  table : ℕ
  /-- The table's rows. -/
  rows : ℕ
  /-- The entries of a row. -/
  width : ℕ
  /-- The leaf transform's length. -/
  n : ℕ
  /-- The leaf transform's root. -/
  psi : ℕ
  /-- Whether the leaf transform is in natural order. -/
  natural : Bool
  /-- The fingerprint's challenge. -/
  chal : ℕ
  /-- The fingerprint's degree in its challenge. -/
  deg : ℕ
  deriving Repr, DecidableEq, Inhabited

/-- **The table, rows and width of a selection's digests** in a value's kind, for blocks of `n`:
the first summand `rowDot T R W x` of the digests' expression with `W` a positive multiple of `n`
(the fingerprint of row `r` of table `T` under the row map): `(T, R, W)`. -/
def digestKind? (n : ℕ) : Kind → Option (ℕ × ℕ × ℕ)
  | .pub (.expr x) =>
    x.summands.findSome? fun t =>
      match t with
      | .apply (.rowDot T R W) _ => if 0 < W ∧ W % n = 0 then some (T, R, W) else none
      | _ => none
  | _ => none

/-- **Whether value `v` holds the spectra of a product form's kernel part** (`kernelPart?`). -/
def isKernelValue (v : ℕ) : Bool :=
  ir.predicates.any fun p =>
    match p.body with
    | .mod _ _ P N real =>
      real.form.isProduct &&
        ((P.deepParts ++ N.deepParts).filterMap ir.kernelPart?).any (·.value == v)
    | _ => false

/-- **The first kernel part of a product form reading value `v`.** -/
def kernelOfValue? (v : ℕ) : Option KernelPart :=
  ir.predicates.findSome? fun p =>
    match p.body with
    | .mod _ _ P N real =>
      if real.form.isProduct then
        ((P.deepParts ++ N.deepParts).filterMap ir.kernelPart?).find? (·.value == v)
      else none
    | _ => none

/-- **The selection a predicate states** (`select_row`'s fingerprint equation `F − sel(digests) = 0`,
`F = Σ_m record_m γ^m`): the kernel values `F` reads (`records`), the block length `n`, root and
order of the first one's kernel, the table, rows and width of the digests a value its
selected side reads holds (`digestKind?`), and its one challenge with its exported degree. -/
def selShape? (q : ℕ) : Option SelShape :=
  match (ir.predicate q).body, (ir.predicate q).degree with
  | .equal d (.add F (.scale _ s)) _ _, [(j, D)] =>
    let recs := ((ir.exprNodes F).filter ir.isKernelValue).eraseDups
    match recs.head?.bind ir.kernelOfValue? with
    | some κ =>
      if 0 < κ.blocks then
        let n := (ir.value κ.value).size / κ.blocks
        match (ir.exprNodes s).findSome? fun u => digestKind? n (ir.value u).kind with
        | some (T, R, W) => some ⟨d, recs, T, R, W, n, κ.psi, κ.natural, j, D⟩
        | none => none
      else none
    | none => none
  | _, _ => none

/-- **The blocks of a selection's record value `v`**: `|v| / n`. -/
def recBlocks (sh : SelShape) (v : ℕ) : ℕ := (ir.value v).size / sh.n

/-- **The first block of record `i` in the row**: the blocks of the records before it. -/
def blockStart (sh : SelShape) (i : ℕ) : ℕ := ((sh.records.take i).map (ir.recBlocks sh)).sum

/-- **The records tile the row**: every record value is whole blocks of `n`, and the records'
blocks, in order, are the row's `width` entries exactly. -/
def tilesB (sh : SelShape) : Bool :=
  sh.records.all (fun v => (ir.value v).size % sh.n == 0) &&
    (sh.records.map (ir.recBlocks sh)).sum * sh.n == sh.width

/-- **The selection of predicate `q` whose record a product form's kernel reads** (`selShape?`): its
records tile the row (`tilesB`), and its challenge is one of a phase the program has. -/
def kernelSel? (q : ℕ) : Option SelShape :=
  (ir.selShape? q).filter fun sh =>
    !sh.records.isEmpty && ir.tilesB sh && decide (ir.IsPhaseChal sh.chal)

/-- **The selection error terms at challenge `j`**: per selection a product form's kernel reads
with its fingerprint at `j` (`kernelSel?`), the fingerprint's degree. -/
def selErrorTerms (j : ℕ) : List (ℕ × ℕ) :=
  (List.range ir.predicates.length).filterMap fun q =>
    (ir.kernelSel? q).bind fun sh => if sh.chal = j then some (sh.deg, ir.tmaxOf j) else none

/-- **A read fixed when challenge `j` is drawn**: a challenge drawn no later than `j`
(`ChalBefore`, `j` itself included), a late value of a phase before `j`'s, or a pad. -/
def ReadFixedAt (j : ℕ) : Read → Prop
  | .chal c => ir.ChalBefore c j
  | .late u => (ir.value u).phase < (ir.challenge j).phase
  | .pad _ => True

/-- A read fixed when a challenge is drawn is decidable. -/
instance (j : ℕ) (rd : Read) : Decidable (ir.ReadFixedAt j rd) := by
  cases rd <;> unfold ReadFixedAt <;> try unfold ChalBefore
  all_goals infer_instance

end

/-- Whether a predicate body is a `mod_0` (an integer equality). -/
def _root_.GordieHowe.RealizedProgram.PredBody.isIntEq : PredBody → Bool
  | .mod _ 0 _ _ _ => true
  | _ => false

/-- **Whether a predicate body is a `mod_q` in the field form**: `isFieldForm` at a predicate read
from a walk of the predicates (`isFieldForm_eq`). -/
def PredBody.isFieldForm : PredBody → Bool
  | .mod _ _ _ _ real => real.form == .field
  | _ => false

end GordieHowe.RealizedProgram
