-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.Realizations.Derivation.Events
public import GordieHoweNative.Language.Realizations.Derivation.ProductMod

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.Realizations.Derivation.TableKernel`

The definitions of `GordieHowe.Language.Realizations.Derivation.TableKernel` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/Realizations/Derivation/TableKernel.lean`, which imports this module.
-/

local notation "ℕ" => Nat
local notation "ℤ" => Int

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export

section

variable (ir : RealizedProgram)

/-- **Value `v` reads only what is fixed when challenge `j` is drawn** (`ReadFixedAt`), through
the reads table. -/
def readsFixedB (j v : ℕ) : Bool :=
  (ir.readsT.getD v []).all fun rd => decide (ir.ReadFixedAt j rd)

/-- **The side conditions of `tableKernel`** for the kernel fact of block `b` of value `v` in domain
`d` from selection `sh` of predicate `q` and hull `[lo, hi]`, at a derivation of rank `self`: `v` is
one of the selection's record values and `b` one of its blocks of `n`, the selection's domain is `d`,
the records and the table read in `d`'s field and are fixed when the fingerprint's challenge is
drawn, the table's rows lie within its value, the table's value has a declared range `[0, B)` with
`[0, B − 1] ⊆ [lo, hi]`, the hull is within `(−p/2, p/2)`, the transform's root is a primitive
`2n`-th root of unity, and every field `equal` has rank below `self`. -/
def tableKernelOkB (sr : List (ℕ × ℕ)) (ctx : DerivCtx) (self d v q b : ℕ) (lo hi : ℤ)
    (sh : SelShape) : Bool :=
  decide (v ∈ sh.records ∧ b < (ir.value v).size / sh.n ∧ sh.domain = d ∧
    d < ir.domains.length ∧ q < ir.predicates.length ∧
    ir.valueField v = ir.domainField d ∧ ir.valueField sh.table = ir.domainField d ∧
    sh.rows * sh.width ≤ (ir.value sh.table).size ∧ lo ≤ 0 ∧
    2 * max lo (-lo) < (ir.charOf (ir.domainField d) : ℤ) ∧ 2 * max hi (-hi) < (ir.charOf (ir.domainField d) : ℤ)) &&
    sh.records.all (ir.readsFixedB sh.chal) && ir.readsFixedB sh.chal sh.table &&
    sr.any (fun vN => vN.1 == sh.table && decide ((vN.2 : ℤ) - 1 ≤ hi)) &&
    rootOkB (ir.charOf (ir.domainField d)) sh.n sh.psi &&
    (List.range ir.predicates.length).all fun p =>
      !(ir.predicate p).body.isEqual || decide (ctx.rank p < self)

/-- **The rule `tableKernel`** for value `v` in domain `d` at a derivation of rank `self`: from the
selection of predicate `qs[0]` whose record a product form's kernel reads (`kernelSel?`), its side
conditions checked (`tableKernelOkB`), the kernel fact of block `b` of `v`: the coefficients of the
polynomial whose spectrum (in the selection's order at its root) the block holds lie in
`[lo, hi]`; none for any other source. -/
def tableKernelFact (sr : List (ℕ × ℕ)) (ctx : DerivCtx) (self d v : ℕ) : IvlSrc → Option Fact
  | .tableKernel _ b (q :: _) lo hi =>
    match ir.kernelSel? q with
    | some sh =>
      if ir.tableKernelOkB sr ctx self d v q b lo hi sh = true then
        some (.kernel d v b sh.n sh.psi sh.natural lo hi)
      else none
    | none => none
  | _ => none

end

end GordieHowe.RealizedProgram
