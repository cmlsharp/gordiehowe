-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.Realizations.Derivation.Ntt
public import GordieHoweNative.Language.Realizations.Derivation.Rules

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.Realizations.Derivation.ProductMod`

The definitions of `GordieHowe.Language.Realizations.Derivation.ProductMod` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/Realizations/Derivation/ProductMod.lean`, which imports this module.
-/

local notation "ℕ" => Nat
local notation "ℤ" => Int

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export

/-- **The interval of a coefficient of a negacyclic product** in `ℤ[X]/(X^n + 1)` (the C++
`int_interval::negacyclic`), the factors' coefficients in `H` and `X`: with their products in
`[Pmin, Pmax]` (`Ivl.mul`), `[min(n Pmin, Pmin − (n − 1) Pmax), max(n Pmax, Pmax − (n − 1) Pmin)]`. -/
def negIvl (n : ℕ) (H Xi : Ivl) : Ivl :=
  ⟨min (n * (H.mul Xi).lo) ((H.mul Xi).lo - ((n - 1 : ℕ) : ℤ) * (H.mul Xi).hi),
    max (n * (H.mul Xi).hi) ((H.mul Xi).hi - ((n - 1 : ℕ) : ℤ) * (H.mul Xi).lo)⟩

section

variable (ir : RealizedProgram)

/-- **A kernel part fits the shape `sh`** at the characteristic `p`: its value holds its blocks
of the block length `n` (`NamedOp.kernel?_spec`), at the shape's root and order, its operand of `n`
coordinates and its constant multiple below `p`. -/
def kernelOkB (p : ℕ) (sh : ProductShape) (κ : KernelPart) : Bool :=
  decide ((ir.value κ.value).size = κ.blocks * sh.n) && decide (κ.psi = sh.psi) &&
    decide (κ.natural = sh.natural) && decide (ir.exprLen κ.operand = sh.n) && decide (κ.scale < p)

/-- **A row fits the shape `sh`**: of `n` coordinates, every kernel part fitting it. -/
def rowOkB (p : ℕ) (sh : ProductShape) (row : Expr) : Bool :=
  decide (ir.exprLen row = sh.n) && (ir.rowKernels row).all (ir.kernelOkB p sh)

/-- **The structural check of a product form** `mod_m P N` of realization `real` (`productOkB`):
in either form, a quotient, and `P`, `N` and the quotient of one length; in the spectral form
moreover the shape
of its sides (`productShape?`): its rows of `n` coordinates, as many of `P` as of `N`, covering both
sides, every row fitting it (`rowOkB`), and the transform's root valid at the characteristic
(`rootOkB`). -/
def productOkB : PredBody → Bool
  | .mod d _ P N real =>
    decide (d < ir.domains.length) && decide (ir.exprLen N = ir.exprLen P) &&
      (match real.quotient with
        | some Q => decide (ir.exprLen Q = ir.exprLen P)
        | none => false) &&
      match real.form with
      | .product => true
      | .spectralProduct =>
        match ir.productShape? P N with
        | some sh =>
          rootOkB (ir.charOf (ir.domainField d)) sh.n sh.psi &&
            decide (sh.rowsP.length = sh.rowsN.length) &&
            decide (ir.exprLen P = sh.rowsP.length * sh.n) &&
            decide (ir.exprLen N = sh.rowsN.length * sh.n) &&
            sh.rowsP.all (ir.rowOkB (ir.charOf (ir.domainField d)) sh) &&
            sh.rowsN.all (ir.rowOkB (ir.charOf (ir.domainField d)) sh)
        | none => false
      | _ => false
  | _ => false

end

section

variable (ir : RealizedProgram)

/-- **Expression `y` reads within `x`**: `y` is `x`, or a view of `x` whose entries lie below
`x`'s length, so `y`'s coordinates are among `x`'s. -/
def readsWithinB (x y : Expr) : Bool :=
  y.beq x ||
    match y with
    | .reindex idx z => z.beq x && idx.inRange (ir.exprLen x)
    | _ => false

/-- **The interval of a kernel part** `s · K(x)` at the characteristic `p` from its premises: the
`kernel` fact at premise `k` (of the part's value and block, at the shape's length, root and
order) and the `ivl` fact at premise `k'` of an expression the operand reads within
(`readsWithinB`): `centred(s) · negIvl(n, H, X)`. -/
def kernelIvl (fs : List Fact) (d p : ℕ) (sh : ProductShape) (κ : KernelPart) (k k' : ℕ) :
    Option Ivl :=
  match fs[k]?, fs[k']? with
  | some (.kernel d1 v b n psi o hl hh), some (.ivl d2 x xl xh) =>
    if d1 = d ∧ d2 = d ∧ v = κ.value ∧ b = κ.block ∧ n = sh.n ∧ psi = sh.psi ∧ o = sh.natural ∧
        ir.readsWithinB x κ.operand = true ∧ 2 * max hl (-hl) < p ∧ 2 * max hh (-hh) < p then
      some (Ivl.smul (centeredZ p κ.scale) (negIvl sh.n ⟨hl, hh⟩ ⟨xl, xh⟩))
    else none
  | _, _ => none

/-- **The interval of a row's summands** `ts` from the premises `ks` (`productMod`): a kernel part
from two premises (`kernelIvl`), an expression part (of at least `n` coordinates) from one `ivl`
premise of the part; their sum, and the premises after. -/
def rowIvl (fs : List Fact) (d p : ℕ) (sh : ProductShape) :
    List Expr → List ℕ → Option (Ivl × List ℕ)
  | [], ks => some (⟨0, 0⟩, ks)
  | t :: ts, ks =>
    match ir.kernelPart? t, ks with
    | some κ, k :: k' :: ks' =>
      (ir.kernelIvl fs d p sh κ k k').bind fun J =>
        (rowIvl fs d p sh ts ks').map fun r => (J.add r.1, r.2)
    | none, k :: ks' =>
      match fs[k]? with
      | some (.ivl d' x lo hi) =>
        if d' = d ∧ x.beq t = true ∧ sh.n ≤ ir.exprLen t then
          (rowIvl fs d p sh ts ks').map fun r => ((⟨lo, hi⟩ : Ivl).add r.1, r.2)
        else none
      | _ => none
    | _, _ => none

/-- **The interval of a side's rows** from the premises `ks`: the hull of the rows' intervals
(`rowIvl` over each row's summands), and the premises after. -/
def rowsIvl (fs : List Fact) (d p : ℕ) (sh : ProductShape) :
    List Expr → List ℕ → Option (Ivl × List ℕ)
  | [], _ => none
  | [r], ks => ir.rowIvl fs d p sh r.summands ks
  | r :: r' :: rs, ks =>
    (ir.rowIvl fs d p sh r.summands ks).bind fun a =>
      (rowsIvl fs d p sh (r' :: rs) a.2).map fun b => (a.1.hull b.1, b.2)

/-- **The interval of a side from one `ivl` premise** of the side. -/
def wholeIvl (fs : List Fact) (d : ℕ) (e : Expr) : List ℕ → Option (Ivl × List ℕ)
  | k :: ks =>
    match fs[k]? with
    | some (.ivl d' x lo hi) => if d' = d ∧ x.beq e = true then some (⟨lo, hi⟩, ks) else none
    | _ => none
  | [] => none

/-- **The interval of a side** `e` of a product form, its rows `rows` (`productMod`): from one
`ivl` premise of the side when no row has a kernel part (or the form is not spectral), else from
its rows (`rowsIvl`). -/
def sideIvl (fs : List Fact) (d p : ℕ) (sh : Option ProductShape) (e : Expr) (rows : List Expr)
    (ks : List ℕ) : Option (Ivl × List ℕ) :=
  match sh with
  | some sh' =>
    if (rows.flatMap ir.rowKernels).isEmpty then wholeIvl fs d e ks
    else ir.rowsIvl fs d p sh' rows ks
  | none => wholeIvl fs d e ks

/-- **The side conditions of `productMod`** at the characteristic `p`: the modulus `m`, the
quotient's lower end `qlo` and range `qmax`, its premise's bound `NQ`, the sides' intervals `JP`,
`JN`: `(Phi − Plo) + a0 < p`, `(Nhi − Nlo) + b0 + m (NQ − 1) < p` (`a0`, `b0` the parts of
`d0 = Plo − Nlo − m qlo`) and `(Phi − Nlo) / m − qlo ≤ qmax`. -/
def productSideB (p m : ℕ) (qlo : ℤ) (qmax NQ : ℕ) (JP JN : Ivl) : Bool :=
  let d0 := JP.lo - JN.lo - m * qlo
  decide (JP.hi - JP.lo + max d0 0 < p) &&
    decide (JN.hi - JN.lo + max (-d0) 0 + m * ((NQ : ℤ) - 1) < p) &&
    decide ((JP.hi - JN.lo) / m - qlo ≤ qmax)

/-- **`productMod ks`** for predicate `pid` of body `body` (the C++ `product_mod`): a product form
`mod_m P N` (`ModForm.isProduct`) passing the structural check (`productOkB`), `2 < m < p`,
its quotient a leaf `v` whose `nat` fact is premise `ks[0]` (`natReadB`), the sides' intervals
from the following premises (`sideIvl`, every premise read) and the side conditions
(`productSideB`): `holds pid`. -/
def productModFact (fs : List Fact) (pid : ℕ) (body : PredBody) (ks : List ℕ) : Option Fact :=
  match body with
  | .mod d m P N real =>
    if real.form.isProduct = true ∧ ir.productOkB body = true ∧ 2 < m ∧
        m < ir.charOf (ir.domainField d) ∧ 2 < ir.charOf (ir.domainField d) then
      match real.quotient, ks with
      | some (.leaf v), k0 :: rest =>
        match fs[k0]? with
        | some (.nat d0 Q NQ) =>
          if d0 = d ∧ Q.beq (.leaf v) = true ∧ 0 < NQ ∧
              natReadB (ir.value v).kind NQ (ir.charOf (ir.domainField d)) = true ∧
              NQ ≤ ir.charOf (ir.domainField d) ∧ ir.valueField v = ir.domainField d ∧
              v < ir.values.length then
            let sh := if real.form = .spectralProduct then ir.productShape? P N else none
            match ir.sideIvl fs d (ir.charOf (ir.domainField d)) sh P
                (sh.map (·.rowsP) |>.getD []) rest with
            | some (JP, rest') =>
              match ir.sideIvl fs d (ir.charOf (ir.domainField d)) sh N
                  (sh.map (·.rowsN) |>.getD []) rest' with
              | some (JN, []) =>
                if productSideB (ir.charOf (ir.domainField d)) m real.quotientLo real.qmax NQ JP JN
                    = true then some (.holds pid)
                else none
              | _ => none
            | none => none
          else none
        | _ => none
      | _, _ => none
    else none
  | _ => none

end

end GordieHowe.RealizedProgram
