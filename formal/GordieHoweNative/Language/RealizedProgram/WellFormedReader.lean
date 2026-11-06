-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.RealizedProgram.Annotations
public import GordieHoweNative.Language.RealizedProgram.Reader

/-!
# GordieHowe: the compiled well-formedness check through the annotations

`wellFormedA` (`Annotations.lean`) reads values by index (`valueT`) and the numbers of values and
of shared expressions inside its per-node tests, each a walk of a list in compiled code. Here it is
written against a program reader (`PReader`), the numbers read once: `PReader.wellFormedA` at the
kernel's reader is `wellFormedA` by definition, and compiled code runs it at the program's context
built once (`wellFormedAC`, the code of `wellFormedA` by `wellFormedA_csimp`, in
`GordieHowe/Language/RealizedProgram/WellFormedReader.lean`).
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

namespace PReader

variable (ir : RealizedProgram) [r : PReader] (a : ExprAnn)

/-- `valueFieldT`, at the reader. -/
def valueFieldT (v : ℕ) : ℕ := ir.fieldOfV (r.value v)

/-- `isPublicT`, at the reader. -/
def isPublicT (v : ℕ) : Bool := !(r.value v).isCommittedB && !(r.value v).kind.isLate

/-- **An annotation's reads**: its bounds, field sets, lengths and public mask by entry. -/
structure AnnReads where
  /-- `ExprAnn.maxAt`. -/
  maxAt : ℕ → ℕ
  /-- `ExprAnn.fieldsAt`. -/
  fieldsAt : ℕ → ℕ
  /-- `ExprAnn.lenAt`. -/
  lenAt : ℕ → ℕ
  /-- `ExprAnn.pub`'s bits. -/
  pubAt : ℕ → Bool

/-- **The reads of annotation `a`**, from its packed tables. -/
def AnnReads.ofAnn : AnnReads := ⟨a.maxAt, a.fieldsAt, a.lenAt, a.pub.testBit⟩

/-- **An annotation's tables as arrays**: its first entries' bounds, field sets and lengths and
its mask's first bits, unpacked once (`AnnArrays.build`). -/
structure AnnArrays where
  /-- The annotation. -/
  ann : ExprAnn
  /-- `maxAt`'s first entries. -/
  maxA : Array ℕ
  /-- `fieldsAt`'s first entries. -/
  fieldsA : Array ℕ
  /-- `lenAt`'s first entries. -/
  lenA : Array ℕ
  /-- The mask's first bits. -/
  pubA : Array Bool

/-- **Annotation `a`'s first `n` entries, unpacked.** -/
def AnnArrays.build (n : ℕ) : AnnArrays :=
  ⟨a, ((List.range n).map a.maxAt).toArray, ((List.range n).map a.fieldsAt).toArray,
    ((List.range n).map a.lenAt).toArray, ((List.range n).map a.pub.testBit).toArray⟩

/-- **An array's entry `j`**, `f j` past its end. -/
def arrayOr {α : Type} (arr : Array α) (f : ℕ → α) (j : ℕ) : α :=
  if h : j < arr.size then arr[j] else f j

/-- **The reads of an annotation's arrays.** -/
def AnnArrays.reads (t : AnnArrays) : AnnReads :=
  ⟨arrayOr t.maxA t.ann.maxAt, arrayOr t.fieldsA t.ann.fieldsAt, arrayOr t.lenA t.ann.lenAt,
    arrayOr t.pubA t.ann.pub.testBit⟩

variable (A : AnnReads)

/-- `belowA`, at the annotation's reads. -/
def belowA (b : ℕ) (e : Expr) : Bool :=
  e.directNodes.all (· < b) && e.refs.all fun j => A.maxAt j ≤ b

/-- `exprOkF`, at the reader and the annotation's reads, the number of shared expressions `ne`
given. -/
def exprOkF (ne f : ℕ) (e : Expr) : Bool :=
  e.refs.all (· < ne) &&
    Expr.walk3 (· < r.nValues) (fun v => valueFieldT ir v == f) isPublicT e &&
    e.refs.all (fun j => A.maxAt j ≤ r.nValues &&
      (A.fieldsAt j == 0 || A.fieldsAt j == 1 <<< f) && A.pubAt j) &&
    ir.shapeOkV A.lenAt e

/-- `kindOkA`, at the reader and the annotation's reads. -/
def kindOkA (ne v : ℕ) : Kind → Bool
  | .pub (.expr e) => exprOkF ir A ne (valueFieldT ir v) e && belowA A v e
  | .bound e => exprOkF ir A ne (valueFieldT ir v) e && belowA A r.nValues e
  | k => ir.kindOkB v k

/-- `lensOkA`, at the annotation's reads. -/
def lensOkA : PredBody → Bool
  | .equal _ e e' _ => ir.lenV A.lenAt e == ir.lenV A.lenAt e'
  | .mem _ _ _ _ => true
  | .mod _ _ e e' _ => ir.lenV A.lenAt e == ir.lenV A.lenAt e'
  | .cross _ x _ y _ _ => ir.lenV A.lenAt x == ir.lenV A.lenAt y

/-- `predOkA`, at the reader and the annotation's reads. -/
def predOkA (ne : ℕ) (b : PredBody) : Bool :=
  b.exprs.all (fun de => de.1 < ir.domains.length && exprOkF ir A ne (ir.domainField de.1) de.2) &&
    lensOkA ir A b

/-- `wellFormedA`, at the reader and the annotation's reads, the number of shared expressions read
once. -/
def wellFormedA : Bool :=
  let ne := ir.exprs.length
  decide (∀ d ∈ ir.domains, d.field < ir.fields.length) &&
    allIdx (fun v x => x.domain < ir.domains.length && kindOkA ir A ne v x.kind) ir.values 0 &&
    allIdx (fun _ e => ir.shapeOkV A.lenAt e) ir.exprs 0 &&
    ir.predicates.all (fun p => predOkA ir A ne p.body) &&
    decide (∀ c ∈ ir.challenges, ir.ChallengeOk c) &&
    allIdx (fun _ x => ir.fieldOkV x) ir.values 0

end PReader

/-- **`wellFormedA` at the program's context and the annotation's arrays, built once**: the code compiled for `wellFormedA`
(`wellFormedA_csimp`). -/
def wellFormedAC (ir : RealizedProgram) (a : ExprAnn) : Bool :=
  let c := PCtx.build ir
  let t := PReader.AnnArrays.build a ir.exprs.length
  @PReader.wellFormedA ir (PReader.ofCtx c) t.reads

end GordieHowe.RealizedProgram
