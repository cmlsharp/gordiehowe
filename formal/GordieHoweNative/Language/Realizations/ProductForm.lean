-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.RealizedProgram.Protocol

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.Realizations.ProductForm`

The definitions of `GordieHowe.Language.Realizations.ProductForm` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/Realizations/ProductForm.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export

/-- **The summands of an expression's add tree**, in order (the C++ `summands`). -/
def Expr.summands : Expr → List Expr
  | .add a b => a.summands ++ b.summands
  | e => [e]

/-- **The kernel of a named operator**: for a negacyclic convolution or a polynomial broadcast in
transform form, its public value, its number of blocks (`1` for a convolution, `K` for a
broadcast), its root and whether its spectra are in natural order. -/
def NamedOp.kernel? : NamedOp → Option (ℕ × ℕ × ℕ × Bool)
  | .negacyclicConv v (.ntt psi) => some (v, 1, psi, false)
  | .negacyclicConv v (.nttNatural psi) => some (v, 1, psi, true)
  | .polyBroadcast t K (.ntt psi) => some (t, K, psi, false)
  | .polyBroadcast t K (.nttNatural psi) => some (t, K, psi, true)
  | _ => none

/-- **A kernel part** `s · K(x)` of a product form's side: the constant multiple `s` (the natural
of its C++ encoding, `1` for none), the value holding the spectra, its blocks, the block read, the
root `psi` and the order of the spectra, the operand `x` and the operator `K`. -/
structure KernelPart where
  /-- The constant multiple. -/
  scale : ℕ
  /-- The value holding the spectra. -/
  value : ℕ
  /-- Its number of blocks. -/
  blocks : ℕ
  /-- The block read. -/
  block : ℕ
  /-- The transform's root. -/
  psi : ℕ
  /-- Whether the spectra are in natural order. -/
  natural : Bool
  /-- The operand. -/
  operand : Expr
  /-- The operator. -/
  op : NamedOp
  deriving Repr, Inhabited

section

variable (ir : RealizedProgram)

/-- **The block an index map reads**, for blocks of `n` coordinates: the map
`[(b n, 1, n)]` reads block `b`. -/
def blockOf? (n : ℕ) : IndexMap → Option ℕ
  | [(s, 1, c)] => if c = n ∧ 0 < n ∧ s % n = 0 then some (s / n) else none
  | _ => none

/-- **The kernel part at `e` after its constant multiple `c`**: `K(x)` for a convolution
(`.apply op x`, block `0`), `reindex B (K(x))` for a block `B` of a broadcast or a convolution
(`blockOf?`). -/
def kernelCore? (c : ℕ) : Expr → Option KernelPart
  | .apply op x =>
    match op.kernel? with
    | some (v, K, psi, nat) =>
      if K = 1 then some ⟨c, v, K, 0, psi, nat, x, op⟩ else none
    | none => none
  | .reindex idx (.apply op x) =>
    match op.kernel? with
    | some (v, K, psi, nat) =>
      match blockOf? ((ir.value v).size / K) idx with
      | some b => if b < K then some ⟨c, v, K, b, psi, nat, x, op⟩ else none
      | none => none
    | none => none
  | _ => none

/-- **The kernel part a summand is** (the C++ `kernel_part`): an optional constant multiple
`.scale (.const c)` over the kernel's core (`kernelCore?`); none for an expression part. -/
def kernelPart? : Expr → Option KernelPart
  | .scale (.const c) e => ir.kernelCore? c e
  | e => ir.kernelCore? 1 e

/-- **The kernel parts of a row**, in order. -/
def rowKernels (row : Expr) : List KernelPart := row.summands.filterMap ir.kernelPart?

/-- **The expression parts of a row**, in order. -/
def rowExprs (row : Expr) : List Expr :=
  row.summands.filter fun t => (ir.kernelPart? t).isNone

/-- **The rows of a side** of rows of `n` coordinates: its concatenations longer than `n` split
(the C++ `part_ivl`). -/
def rowsAt (n : ℕ) : Expr → List Expr
  | .concat a b =>
    if n < ir.exprLen (.concat a b) then rowsAt n a ++ rowsAt n b else [.concat a b]
  | e => [e]

/-- **The parts of an expression at every level**: its add trees and concatenations flattened. -/
def Expr.deepParts : Expr → List Expr
  | .add a b => a.deepParts ++ b.deepParts
  | .concat a b => a.deepParts ++ b.deepParts
  | e => [e]

/-- **The first kernel part of a product form's sides**, in `P` then `N`. -/
def firstKernel? (P N : Expr) : Option KernelPart :=
  ((P.deepParts ++ N.deepParts).filterMap ir.kernelPart?).head?

/-- **The shape of a spectral product form** with sides `P` and `N`: the kernels' block length `n`,
root `psi` and order `natural` (those of the first kernel part), and the rows of the two sides. -/
structure ProductShape where
  /-- The block length. -/
  n : ℕ
  /-- The transform's root. -/
  psi : ℕ
  /-- Whether the transform is in natural order. -/
  natural : Bool
  /-- The rows of `P`. -/
  rowsP : List Expr
  /-- The rows of `N`. -/
  rowsN : List Expr
  deriving Repr, Inhabited

/-- **The shape of the spectral product form with sides `P` and `N`**, from the first kernel part
(`firstKernel?`), the sides split into rows of its block length (`rowsAt`). -/
def productShape? (P N : Expr) : Option ProductShape :=
  (ir.firstKernel? P N).map fun k =>
    let n := (ir.value k.value).size / k.blocks
    ⟨n, k.psi, k.natural, ir.rowsAt n P, ir.rowsAt n N⟩

end

end GordieHowe.RealizedProgram
