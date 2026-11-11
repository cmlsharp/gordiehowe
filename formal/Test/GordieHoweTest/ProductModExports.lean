-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.ProgramCheck
public import GordieHowe.Language.Realizations.Circuit.LoadNative
public import GordieHoweTest.Data.ProductModScalar.Data
public import GordieHoweTest.Data.ProductModScalarDirect.Data
public import GordieHoweTest.Data.ModOperator.Data
public import GordieHoweTest.Data.ModOperatorDirect.Data
public import GordieHoweTest.Data.ProductModConvBatch.Data
public import GordieHoweTest.Data.ConvEqualBatch.Data
public import GordieHoweTest.Data.ConvMulBatch.Data
public import GordieHoweTest.Data.ProductModConv.Data
public import GordieHoweTest.Data.ConvEqualDirect.Data
public import GordieHoweTest.Data.ConvIntEqualDirect.Data
public import GordieHoweTest.Data.ConvIntMulBatch.Data
public import GordieHoweTest.Data.FieldModScalar.Data
public import GordieHoweTest.Data.FieldModConv.Data
public import GordieHoweTest.Data.FieldModAffine.Data
-- The native checks run the data's compiled code.
meta import GordieHoweTest.Data.ProductModScalar.Program
meta import GordieHoweTest.Data.ProductModScalar.Plan
meta import GordieHoweTest.Data.ProductModScalar.Structure
meta import GordieHoweTest.Data.ProductModScalar.Cert
meta import GordieHoweTest.Data.ProductModScalar.Derivs
meta import GordieHoweTest.Data.ProductModScalar.Honest.Nodes
meta import GordieHoweTest.Data.ProductModScalar.GKR.A
meta import GordieHoweTest.Data.ProductModScalar.FieldTable
meta import GordieHoweTest.Data.ProductModScalar.Tableau
meta import GordieHoweTest.Data.ProductModScalar.Data
meta import GordieHoweTest.Data.ProductModScalarDirect.Program
meta import GordieHoweTest.Data.ProductModScalarDirect.Plan
meta import GordieHoweTest.Data.ProductModScalarDirect.Structure
meta import GordieHoweTest.Data.ProductModScalarDirect.Cert
meta import GordieHoweTest.Data.ProductModScalarDirect.Derivs
meta import GordieHoweTest.Data.ProductModScalarDirect.Honest.Nodes
meta import GordieHoweTest.Data.ProductModScalarDirect.GKR.A
meta import GordieHoweTest.Data.ProductModScalarDirect.FieldTable
meta import GordieHoweTest.Data.ProductModScalarDirect.Tableau
meta import GordieHoweTest.Data.ProductModScalarDirect.Data
meta import GordieHoweTest.Data.ModOperator.Program
meta import GordieHoweTest.Data.ModOperator.Plan
meta import GordieHoweTest.Data.ModOperator.Structure
meta import GordieHoweTest.Data.ModOperator.Cert
meta import GordieHoweTest.Data.ModOperator.Derivs
meta import GordieHoweTest.Data.ModOperator.Honest.Nodes
meta import GordieHoweTest.Data.ModOperator.GKR.A
meta import GordieHoweTest.Data.ModOperator.FieldTable
meta import GordieHoweTest.Data.ModOperator.Tableau
meta import GordieHoweTest.Data.ModOperator.Data
meta import GordieHoweTest.Data.ModOperatorDirect.Program
meta import GordieHoweTest.Data.ModOperatorDirect.Plan
meta import GordieHoweTest.Data.ModOperatorDirect.Structure
meta import GordieHoweTest.Data.ModOperatorDirect.Cert
meta import GordieHoweTest.Data.ModOperatorDirect.Derivs
meta import GordieHoweTest.Data.ModOperatorDirect.Honest.Nodes
meta import GordieHoweTest.Data.ModOperatorDirect.GKR.A
meta import GordieHoweTest.Data.ModOperatorDirect.FieldTable
meta import GordieHoweTest.Data.ModOperatorDirect.Tableau
meta import GordieHoweTest.Data.ModOperatorDirect.Data
meta import GordieHoweTest.Data.ProductModConvBatch.Program
meta import GordieHoweTest.Data.ProductModConvBatch.Plan
meta import GordieHoweTest.Data.ProductModConvBatch.Structure
meta import GordieHoweTest.Data.ProductModConvBatch.Cert
meta import GordieHoweTest.Data.ProductModConvBatch.Derivs
meta import GordieHoweTest.Data.ProductModConvBatch.Honest.Nodes
meta import GordieHoweTest.Data.ProductModConvBatch.GKR.A
meta import GordieHoweTest.Data.ProductModConvBatch.FieldTable
meta import GordieHoweTest.Data.ProductModConvBatch.Tableau
meta import GordieHoweTest.Data.ProductModConvBatch.Data
meta import GordieHoweTest.Data.ConvEqualBatch.Program
meta import GordieHoweTest.Data.ConvEqualBatch.Plan
meta import GordieHoweTest.Data.ConvEqualBatch.Structure
meta import GordieHoweTest.Data.ConvEqualBatch.Cert
meta import GordieHoweTest.Data.ConvEqualBatch.Derivs
meta import GordieHoweTest.Data.ConvEqualBatch.Honest.Nodes
meta import GordieHoweTest.Data.ConvEqualBatch.GKR.A
meta import GordieHoweTest.Data.ConvEqualBatch.FieldTable
meta import GordieHoweTest.Data.ConvEqualBatch.Tableau
meta import GordieHoweTest.Data.ConvEqualBatch.Data
meta import GordieHoweTest.Data.ConvMulBatch.Program
meta import GordieHoweTest.Data.ConvMulBatch.Plan
meta import GordieHoweTest.Data.ConvMulBatch.Structure
meta import GordieHoweTest.Data.ConvMulBatch.Cert
meta import GordieHoweTest.Data.ConvMulBatch.Derivs
meta import GordieHoweTest.Data.ConvMulBatch.Honest.Nodes
meta import GordieHoweTest.Data.ConvMulBatch.GKR.A
meta import GordieHoweTest.Data.ConvMulBatch.FieldTable
meta import GordieHoweTest.Data.ConvMulBatch.Tableau
meta import GordieHoweTest.Data.ConvMulBatch.Data
meta import GordieHoweTest.Data.ProductModConv.Program
meta import GordieHoweTest.Data.ProductModConv.Plan
meta import GordieHoweTest.Data.ProductModConv.Structure
meta import GordieHoweTest.Data.ProductModConv.Cert
meta import GordieHoweTest.Data.ProductModConv.Derivs
meta import GordieHoweTest.Data.ProductModConv.Honest.Nodes
meta import GordieHoweTest.Data.ProductModConv.GKR.A
meta import GordieHoweTest.Data.ProductModConv.FieldTable
meta import GordieHoweTest.Data.ProductModConv.Tableau
meta import GordieHoweTest.Data.ProductModConv.Data
meta import GordieHoweTest.Data.ConvEqualDirect.Program
meta import GordieHoweTest.Data.ConvEqualDirect.Plan
meta import GordieHoweTest.Data.ConvEqualDirect.Structure
meta import GordieHoweTest.Data.ConvEqualDirect.Cert
meta import GordieHoweTest.Data.ConvEqualDirect.Derivs
meta import GordieHoweTest.Data.ConvEqualDirect.Honest.Nodes
meta import GordieHoweTest.Data.ConvEqualDirect.GKR.A
meta import GordieHoweTest.Data.ConvEqualDirect.FieldTable
meta import GordieHoweTest.Data.ConvEqualDirect.Tableau
meta import GordieHoweTest.Data.ConvEqualDirect.Data
meta import GordieHoweTest.Data.ConvIntEqualDirect.Program
meta import GordieHoweTest.Data.ConvIntEqualDirect.Plan
meta import GordieHoweTest.Data.ConvIntEqualDirect.Structure
meta import GordieHoweTest.Data.ConvIntEqualDirect.Cert
meta import GordieHoweTest.Data.ConvIntEqualDirect.Derivs
meta import GordieHoweTest.Data.ConvIntEqualDirect.Honest.Nodes
meta import GordieHoweTest.Data.ConvIntEqualDirect.GKR.A
meta import GordieHoweTest.Data.ConvIntEqualDirect.FieldTable
meta import GordieHoweTest.Data.ConvIntEqualDirect.Tableau
meta import GordieHoweTest.Data.ConvIntEqualDirect.Data
meta import GordieHoweTest.Data.ConvIntMulBatch.Program
meta import GordieHoweTest.Data.ConvIntMulBatch.Plan
meta import GordieHoweTest.Data.ConvIntMulBatch.Structure
meta import GordieHoweTest.Data.ConvIntMulBatch.Cert
meta import GordieHoweTest.Data.ConvIntMulBatch.Derivs
meta import GordieHoweTest.Data.ConvIntMulBatch.Honest.Nodes
meta import GordieHoweTest.Data.ConvIntMulBatch.GKR.A
meta import GordieHoweTest.Data.ConvIntMulBatch.FieldTable
meta import GordieHoweTest.Data.ConvIntMulBatch.Tableau
meta import GordieHoweTest.Data.ConvIntMulBatch.Data
meta import GordieHoweTest.Data.FieldModScalar.Program
meta import GordieHoweTest.Data.FieldModScalar.Plan
meta import GordieHoweTest.Data.FieldModScalar.Structure
meta import GordieHoweTest.Data.FieldModScalar.Cert
meta import GordieHoweTest.Data.FieldModScalar.Derivs
meta import GordieHoweTest.Data.FieldModScalar.Honest.Nodes
meta import GordieHoweTest.Data.FieldModScalar.GKR.A
meta import GordieHoweTest.Data.FieldModScalar.FieldTable
meta import GordieHoweTest.Data.FieldModScalar.Tableau
meta import GordieHoweTest.Data.FieldModScalar.Data
meta import GordieHoweTest.Data.FieldModConv.Program
meta import GordieHoweTest.Data.FieldModConv.Plan
meta import GordieHoweTest.Data.FieldModConv.Structure
meta import GordieHoweTest.Data.FieldModConv.Cert
meta import GordieHoweTest.Data.FieldModConv.Derivs
meta import GordieHoweTest.Data.FieldModConv.Honest.Nodes
meta import GordieHoweTest.Data.FieldModConv.GKR.A
meta import GordieHoweTest.Data.FieldModConv.FieldTable
meta import GordieHoweTest.Data.FieldModConv.Tableau
meta import GordieHoweTest.Data.FieldModConv.Data
meta import GordieHoweTest.Data.FieldModAffine.Program
meta import GordieHoweTest.Data.FieldModAffine.Plan
meta import GordieHoweTest.Data.FieldModAffine.Structure
meta import GordieHoweTest.Data.FieldModAffine.Cert
meta import GordieHoweTest.Data.FieldModAffine.Derivs
meta import GordieHoweTest.Data.FieldModAffine.Honest.Nodes
meta import GordieHoweTest.Data.FieldModAffine.GKR.A
meta import GordieHoweTest.Data.FieldModAffine.FieldTable
meta import GordieHoweTest.Data.FieldModAffine.Tableau
meta import GordieHoweTest.Data.FieldModAffine.Data
meta import GordieHowe.Language.ProgramCheck
meta import GordieHowe.Language.Realizations.Circuit.LoadNative
-- The examples below evaluate the sealed programs and plans.
import all GordieHoweTest.Data.ProductModScalar.Program
import all GordieHoweTest.Data.ProductModScalarDirect.Program
import all GordieHoweTest.Data.ModOperator.Program
import all GordieHoweTest.Data.ModOperatorDirect.Program
import all GordieHoweTest.Data.ProductModConvBatch.Program
import all GordieHoweTest.Data.ConvEqualBatch.Program
import all GordieHoweTest.Data.ConvMulBatch.Program
import all GordieHoweTest.Data.ProductModConv.Program
import all GordieHoweTest.Data.ConvEqualDirect.Program
import all GordieHoweTest.Data.ConvIntEqualDirect.Program
import all GordieHoweTest.Data.ConvIntMulBatch.Program
import all GordieHoweTest.Data.FieldModScalar.Program
import all GordieHoweTest.Data.FieldModConv.Program
import all GordieHoweTest.Data.FieldModAffine.Program

public section

/-!
# `assert_mod` over sides that are not plain sums, on exported programs

Six compiler exports of `assert_mod` at `q = 12289` below the characteristic, each with the
quotient's lower end `0`, three at `q = p`, the Goldilocks prime, in a domain over Goldilocks⁴
(its integer reading linear, `gold4_readLinear`), and five of an equality reading a convolution
with `h` private:

* `GordieHoweTest.Data.ProductModScalar`: `assert_mod(a * b, c, q)` with `a, b < 1024`, in the
  committed-digits form over the expression sides: the source `mod_q (a * b) c`, its quotient
  committed and bound to its digits, and its relation the predicate `product.row`, placed in the
  circuit, which reads the quotient through its digits;
* `GordieHoweTest.Data.ProductModScalarDirect`: the same with `a, b < 256`, its quotient below `6`,
  which the range planner looks up directly: the committed quotient is the direct lookup's record
  (`commDirectCB`), and the circuit-placed row reads it as a committed value;
* `GordieHoweTest.Data.ModOperator`: `assert_mod(AcyclicConv(h)(x), c, q)` with `h` public, an
  affine side no circuit reads, in the committed-digits form with an affine row, its quotient in
  two digits;
* `GordieHoweTest.Data.ModOperatorDirect`: the same with `h < 64`, its quotient below `84`, which
  the range planner looks up directly in the `111`-row table of `c`'s two-sided lookup: the
  quotient is the direct lookup's record, generated as `Gen.commDigit m 0 lk 0`
  (`commDirectCB`);
* `GordieHoweTest.Data.ProductModConv`: `assert_mod(conv(h, x), c, q)` with `h` committed, the
  convolution unpinned, which the compiler realizes directly, in the committed-digits form over
  the expression sides: its row `product.row` states the source `conv` with the target
  `realized`, its realized predicate `product.row.realized`, placed in the circuit, reads the
  committed `C`, and the circuit's products predicate states `C = Σ_{u+v=k} h_u x_v`
  (`SpectralConv.direct`, `DirectOkAt`);
* `GordieHoweTest.Data.ProductModConvBatch`: the same with the convolution pinned to the batch
  realization, in the committed-digits form over the expression sides: its row `product.row`, a
  realization, states the source `conv` with the target `realized`, its realized predicate
  `product.row.realized` reads `INTT(z)`, and the batch's products predicate is the convolution's
  (`specRowCB`, `m` of smaller rank in the completeness step `specRow`);
* `GordieHoweTest.Data.FieldModScalar`: `assert_mod(a * b, c, p)` with `a, b < 1024`, in the field
  form: the source `mod_p (a * b) c` with no quotient, its field row `product.row`,
  `a * b + (p − 1) · c = 0`, placed in the circuit (`fieldRowRealB`, the rule `fieldDvd`);
* `GordieHoweTest.Data.FieldModConv`: `assert_mod(conv(h, x), c, p)` with `h` private, the
  convolution realized directly: the field row states the source `conv` with the target
  `realized`, its realized predicate reading `C`;
* `GordieHoweTest.Data.FieldModAffine`: `assert_mod(a + b, c, p)`, affine sides: the field form
  with its field row an affine row;
* `GordieHoweTest.Data.ConvEqualBatch`: `conv(h, x) - c = 0`, a plain source `equal`, the
  convolution pinned to the batch realization, with the target `realized`;
* `GordieHoweTest.Data.ConvEqualDirect`: `conv(h, x) - c = 0`, the convolution pinned to the
  direct realization, with the target `realized`: its realized predicate `equal.realized` reads
  `C`;
* `GordieHoweTest.Data.ConvIntEqualDirect`: the integer equality `conv(h, x) = c`
  (`assert_int_equal`, a `mod_0`), the convolution pinned to the direct realization, with the
  target `realized`: its realized predicate `equal.realized` states the rewritten node's sides,
  the convolution read as `C`;
* `GordieHoweTest.Data.ConvIntMulBatch`: the integer equality `conv(h, x) · y = w`
  (`assert_int_equal`), not affine in the convolution, pinned to the batch realization: the
  compiler commits `C` with the affine row `C = INTT(z)[0, 31)`, and the realized predicate
  `equal.realized`, placed in the circuit, states the rewritten node's sides, `C · y = w`;
* `GordieHoweTest.Data.ConvMulBatch`: `conv(h, x) · y - w = 0`, not affine in the convolution,
  pinned to the batch realization: the compiler commits `C` with the affine row
  `C = INTT(z)[0, 31)`, the realized predicate `equal.realized`, placed in the circuit, reads `C`
  through its shared leaf, and the convolution's committed reading (`SpectralConv.committed`)
  names that leaf and the row.

The committed-digits rows state no shift (`commHeadB`'s head without one, the shift being `0`).
Every program passes its check end to end (`GordieHowe.ProgramData.programOkB`, one compiled run:
the realization's derivations, the cells, every field's checks, the completion certificate and the
circuit certificate).
-/

namespace GordieHoweTest.ProductModExports

open GordieHowe GordieHowe.RealizedProgram

/-- Whether a predicate is a `mod_q` in the committed-digits form with quotient lower end `0`. -/
def committedAtZero (p : Predicate) : Bool :=
  match p.body with
  | .mod _ _ _ _ real => real.form == .committedDigits && real.quotientLo == 0
  | _ => false

namespace Scalar

open GordieHowe.Generated.ProductModScalar.QROMParams

/-- Its predicate `product` is a committed-digits `mod_q` with quotient lower end `0`. -/
example : Program.program.predicates.any committedAtZero = true := by decide +kernel

/-- Its relation `product.row` is placed in the circuit. -/
example : Program.program.predicates.any (fun p => p.name == "product.row" &&
    match p.body with
    | .equal _ _ _ (.gkr _) => true
    | _ => false) = true := by decide +kernel

/-- **The program passes its check**, compiled at the unfolded data. -/
theorem programOk : data.programOkB false = true := by
  delta data
  gh_native_check

end Scalar

namespace ScalarDirect

open GordieHowe.Generated.ProductModScalarDirect.QROMParams

/-- Its predicate `product` is a committed-digits `mod_q` with quotient lower end `0`. -/
example : Program.program.predicates.any committedAtZero = true := by decide +kernel

/-- Its quotient is looked up directly. -/
example : Program.program.predicates.any (fun p => p.name == "product.q" &&
    match p.body with
    | .mem _ _ _ (.lookup r) => r.kind == .direct
    | _ => false) = true := by decide +kernel

/-- **The program passes its check**, compiled at the unfolded data. -/
theorem programOk : data.programOkB false = true := by
  delta data
  gh_native_check

end ScalarDirect

namespace Operator

open GordieHowe.Generated.ModOperator.QROMParams

/-- Its predicate `product` is a committed-digits `mod_q` with quotient lower end `0`. -/
example : Program.program.predicates.any committedAtZero = true := by decide +kernel

/-- **The program passes its check**, compiled at the unfolded data. -/
theorem programOk : data.programOkB false = true := by
  delta data
  gh_native_check

end Operator

namespace OperatorDirect

open GordieHowe.Generated.ModOperatorDirect.QROMParams

/-- Its predicate `product` is a committed-digits `mod_q` with quotient lower end `0`. -/
example : Program.program.predicates.any committedAtZero = true := by decide +kernel

/-- Its quotient is looked up directly. -/
example : Program.program.predicates.any (fun p => p.name == "product.q" &&
    match p.body with
    | .mem _ _ _ (.lookup r) => r.kind == .direct
    | _ => false) = true := by decide +kernel

/-- **The program passes its check**, compiled at the unfolded data. -/
theorem programOk : data.programOkB false = true := by
  delta data
  gh_native_check

end OperatorDirect

namespace ConvBatch

open GordieHowe.Generated.ProductModConvBatch.QROMParams

/-- Its predicate `product` is a committed-digits `mod_q` with quotient lower end `0`. -/
example : Program.program.predicates.any committedAtZero = true := by decide +kernel

/-- Its row reads the convolution through its spectral realization. -/
example : Program.program.predicates.any (fun p => p.name == "product.row" &&
    match p.body with
    | .equal _ _ _ (.realized _) => true
    | _ => false) = true := by decide +kernel

/-- **The program passes its check**, compiled at the unfolded data. -/
theorem programOk : data.programOkB false = true := by
  delta data
  gh_native_check

end ConvBatch

namespace ConvEqual

open GordieHowe.Generated.ConvEqualBatch.QROMParams

/-- Its predicate `equal` reads the convolution through its spectral realization. -/
example : Program.program.predicates.any (fun p => p.name == "equal" &&
    match p.body with
    | .equal _ _ _ (.realized _) => true
    | _ => false) = true := by decide +kernel

/-- **The program passes its check**, compiled at the unfolded data. -/
theorem programOk : data.programOkB false = true := by
  delta data
  gh_native_check

end ConvEqual

namespace ConvMul

open GordieHowe.Generated.ConvMulBatch.QROMParams

/-- Its convolution has a committed reading. -/
example : Program.program.convs.any (fun c => c.committed.isSome) = true := by decide +kernel

/-- Its realized predicate is placed in the circuit. -/
example : Program.program.predicates.any (fun p => p.name == "equal.realized" &&
    match p.body with
    | .equal _ _ _ (.gkr _) => true
    | _ => false) = true := by decide +kernel

/-- **The program passes its check**, compiled at the unfolded data. -/
theorem programOk : data.programOkB false = true := by
  delta data
  gh_native_check

end ConvMul

namespace Conv

open GordieHowe.Generated.ProductModConv.QROMParams

/-- Its predicate `product` is a committed-digits `mod_q` with quotient lower end `0`. -/
example : Program.program.predicates.any committedAtZero = true := by decide +kernel

/-- Its convolution is realized directly. -/
example : Program.program.convs.any (·.direct) = true := by decide +kernel

/-- Its row reads the convolution through its realization. -/
example : Program.program.predicates.any (fun p => p.name == "product.row" &&
    match p.body with
    | .equal _ _ _ (.realized _) => true
    | _ => false) = true := by decide +kernel

/-- **The program passes its check**, compiled at the unfolded data. -/
theorem programOk : data.programOkB false = true := by
  delta data
  gh_native_check

end Conv

namespace ConvEqualDirect

open GordieHowe.Generated.ConvEqualDirect.QROMParams

/-- Its convolution is realized directly. -/
example : Program.program.convs.any (·.direct) = true := by decide +kernel

/-- Its predicate `equal` reads the convolution through its realization. -/
example : Program.program.predicates.any (fun p => p.name == "equal" &&
    match p.body with
    | .equal _ _ _ (.realized _) => true
    | _ => false) = true := by decide +kernel

/-- **The program passes its check**, compiled at the unfolded data. -/
theorem programOk : data.programOkB false = true := by
  delta data
  gh_native_check

end ConvEqualDirect

namespace ConvIntEqualDirect

open GordieHowe.Generated.ConvIntEqualDirect.QROMParams

/-- Its convolution is realized directly. -/
example : Program.program.convs.any (·.direct) = true := by decide +kernel

/-- Its integer equality `equal` reads the convolution through its realization. -/
example : Program.program.predicates.any (fun p => p.name == "equal" &&
    match p.body with
    | .mod _ 0 _ _ real =>
      match real.target with
      | some (.realized _) => true
      | _ => false
    | _ => false) = true := by decide +kernel

/-- **The program passes its check**, compiled at the unfolded data. -/
theorem programOk : data.programOkB false = true := by
  delta data
  gh_native_check

end ConvIntEqualDirect

namespace ConvIntMulBatch

open GordieHowe.Generated.ConvIntMulBatch.QROMParams

/-- Its convolution has a committed reading. -/
example : Program.program.convs.any (fun c => c.committed.isSome) = true := by decide +kernel

/-- Its integer equality's realized predicate is placed in the circuit. -/
example : Program.program.predicates.any (fun p => p.name == "equal.realized" &&
    match p.body with
    | .equal _ _ _ (.gkr _) => true
    | _ => false) = true := by decide +kernel

/-- **The program passes its check**, compiled at the unfolded data. -/
theorem programOk : data.programOkB false = true := by
  delta data
  gh_native_check

end ConvIntMulBatch

namespace FieldModScalar

open GordieHowe.Generated.FieldModScalar.QROMParams

/-- Its predicate `product` is a `mod_p` in the field form. -/
example : Program.program.predicates.any (fun p => p.name == "product" &&
    match p.body with
    | .mod _ _ _ _ real => real.form == .field
    | _ => false) = true := by decide +kernel

/-- **The program passes its check**, compiled at the unfolded data. -/
theorem programOk : data.programOkB false = true := by
  delta data
  gh_native_check

end FieldModScalar

namespace FieldModConv

open GordieHowe.Generated.FieldModConv.QROMParams

/-- Its predicate `product` is a `mod_p` in the field form. -/
example : Program.program.predicates.any (fun p => p.name == "product" &&
    match p.body with
    | .mod _ _ _ _ real => real.form == .field
    | _ => false) = true := by decide +kernel

/-- Its field row reads the convolution through its realization. -/
example : Program.program.predicates.any (fun p => p.name == "product.row" &&
    match p.body with
    | .equal _ _ _ (.realized _) => true
    | _ => false) = true := by decide +kernel

/-- **The program passes its check**, compiled at the unfolded data. -/
theorem programOk : data.programOkB false = true := by
  delta data
  gh_native_check

end FieldModConv

namespace FieldModAffine

open GordieHowe.Generated.FieldModAffine.QROMParams

/-- Its predicate `product` is a `mod_p` in the field form. -/
example : Program.program.predicates.any (fun p => p.name == "product" &&
    match p.body with
    | .mod _ _ _ _ real => real.form == .field
    | _ => false) = true := by decide +kernel

/-- **The program passes its check**, compiled at the unfolded data. -/
theorem programOk : data.programOkB false = true := by
  delta data
  gh_native_check

end FieldModAffine

end GordieHoweTest.ProductModExports
