-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.Protocol
public import GordieHoweNative.Language.Realizations.ProductForm

@[expose] public section

/-!
# GordieHowe: the product form of a `mod_q`, its parts and its placed equation

The product form of `assert_mod` (`lib/gordiehowe/ops/integer_congruence.h`, `ModForm.product` and
`ModForm.spectralProduct`) states the congruence `D = P − N = 0 (mod m)` of terms that are not all
affine, `P` the terms of sign `+1` and `N` those of sign `−1`. The realized program writes `P` and
`N` as expressions: the rows of `n` coordinates concatenated, each row the sum (an add tree) of its
parts, a part an expression or a **kernel part** `s · K(x)` (`GordieHowe.RealizedProgram.KernelPart`, read by
`GordieHowe.RealizedProgram.kernelPart?`): the convolution by the polynomial whose spectrum a value holds, a
negacyclic convolution or a polynomial broadcast in transform form (`ConvForm.ntt`,
`ConvForm.nttNatural`), read at one block through a reindex for a broadcast, scaled by a constant.

**The placed equation** (`GordieHowe.RealizedProgram.ProductPlaced`, the meaning of the predicate's own circuit,
`GordieHowe.RealizedProgram.PlacedHolds`): with `Q` the quotient and `qlo` its lower end,

* in the product form, the field equation `P − N = m qlo + m Q`, coordinate by coordinate;
* in the spectral product form, row by row (`GordieHowe.RealizedProgram.ProductShape`: the rows of `P` and `N`,
  the transform of the kernels), the equation in the spectrum of the kernels' transform `T`:
  `T(E − m qlo − m Q_r) = Σ_{N} s · h ⊙ T(x) − Σ_{P} s · h ⊙ T(x)` at every frequency, `E` the
  row's expression parts of `P` minus those of `N`, `h` a kernel's spectrum (the block of its value)
  and `x` its operand; the C++ states this equation (`Congruence::equation`: the transform applies
  once per row) and inverts it row by row for the quotient's generator.

The definitions are in `GordieHoweNative/Language/Realizations/ProductForm.lean`
(the compiled library `GordieHoweNative`); this module has their lemmas.
-/

namespace GordieHowe.RealizedProgram

open Export

/-! ## The placed equation -/

namespace Ops

variable {K : Type*} [Field K]

/-- **The negacyclic transform of length `n` at `ψ`** in natural order (`natural`) or in scheme
order. -/
def nttOf (natural : Bool) (n : ℕ) (ψ : K) (x : ℕ → K) : ℕ → K :=
  if natural then nttNatural n ψ x else nttScheme n ψ x

end Ops

section

variable (ir : RealizedProgram) {I : Interp}

/-- **The quotient term `m qlo + m Q` at coordinate `i`** of a product form of realization `real`,
in domain `d`'s field (`m qlo` for a form without a quotient). -/
def quotTerm (rd : ir.Valuation I) (d m : ℕ) (real : ModRealization) (i : ℕ) :
    (I (ir.domainField d)).K :=
  (((m : ℤ) * real.quotientLo : ℤ) : (I (ir.domainField d)).K) +
    match real.quotient with
    | some Q => (m : (I (ir.domainField d)).K) * ir.evalWith rd d Q i
    | none => 0

/-- **A kernel part's term at frequency `k`** of the transform `natural, n, ψ`: `s · h_k · T(x)_k`,
`h` the block of the kernel's value its spectra (`castElt` into domain `d`'s field). -/
def kernelTerm (rd : ir.Valuation I) (d : ℕ) (natural : Bool) (n : ℕ) (ψ : (I (ir.domainField d)).K)
    (κ : KernelPart) (k : ℕ) : (I (ir.domainField d)).K :=
  (I (ir.domainField d)).decode κ.scale * castElt (rd κ.value (κ.block * n + k)) *
    Ops.nttOf natural n ψ (ir.evalWith rd d κ.operand) k

/-- **Row `r`'s equation of a spectral product form in the spectrum** at frequency `k`
(`ProductPlaced`): `T(E − m qlo − m Q_r)_k = Σ_N s h_k T(x)_k − Σ_P s h_k T(x)_k`, `E` the row's
expression parts of `P` minus those of `N`, `Q_r` the quotient's coordinates `[r n, (r + 1) n)`. -/
def SpectralRowHolds (rd : ir.Valuation I) (d m : ℕ) (real : ModRealization) (sh : ProductShape)
    (r : ℕ) (PR NR : Expr) (k : ℕ) : Prop :=
  Ops.nttOf sh.natural sh.n ((I (ir.domainField d)).decode sh.psi)
      (fun i => ((ir.rowExprs PR).map fun t => ir.evalWith rd d t i).sum -
        ((ir.rowExprs NR).map fun t => ir.evalWith rd d t i).sum -
          ir.quotTerm rd d m real (r * sh.n + i)) k =
    ((ir.rowKernels NR).map fun κ =>
        ir.kernelTerm rd d sh.natural sh.n ((I (ir.domainField d)).decode sh.psi) κ k).sum -
      ((ir.rowKernels PR).map fun κ =>
        ir.kernelTerm rd d sh.natural sh.n ((I (ir.domainField d)).decode sh.psi) κ k).sum

/-- **The placed equation of a product form** `mod_m P N` of realization `real` in domain `d`
(the predicate's own circuit, `PlacedHolds`): in the product form, `P − N = m qlo + m Q` in the
field at every coordinate; in the spectral product form, every row's equation in the spectrum at
every frequency below the block length (`SpectralRowHolds`), for the shape of its sides
(`productShape?`, with as many rows of `P` as of `N`); no meaning for any other form, or for a
spectral form whose sides have no kernel part. -/
def ProductPlaced (rd : ir.Valuation I) (d m : ℕ) (P N : Expr) (real : ModRealization) : Prop :=
  match real.form with
  | .product => ∀ i < ir.exprLen P,
      ir.evalWith rd d P i - ir.evalWith rd d N i = ir.quotTerm rd d m real i
  | .spectralProduct =>
    match ir.productShape? P N with
    | some sh => sh.rowsP.length = sh.rowsN.length ∧
        ∀ r < sh.rowsP.length, ∀ k < sh.n,
          ir.SpectralRowHolds rd d m real sh r (sh.rowsP.getD r default) (sh.rowsN.getD r default) k
    | none => True
  | _ => True

end

end GordieHowe.RealizedProgram
