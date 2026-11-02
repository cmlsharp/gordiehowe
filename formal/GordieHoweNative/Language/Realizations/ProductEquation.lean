-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.Realizations.Derivation.Basic

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.Realizations.ProductEquation`

The definitions of `GordieHowe.Language.Realizations.ProductEquation` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/Realizations/ProductEquation.lean`, which imports this module.
-/

local notation "ℕ" => Nat
local notation "ℤ" => Int

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export

/-- **The first element `s` with `g s = some b`, and the list without it**, or none. -/
def takeSome {σ : Type _} {β : Type _} (g : σ → Option β) : List σ → Option (β × List σ)
  | [] => none
  | s :: ss =>
    match g s with
    | some b => some (b, ss)
    | none => (takeSome g ss).map fun r => (r.1, s :: r.2)

/-- **Every element of `es` matches a distinct slot of `ss`, and every slot is matched**: each
element `e` in turn removes the first remaining slot `s` with `m s e`. -/
def matchAll {σ : Type _} {τ : Type _} (m : σ → τ → Bool) : List τ → List σ → Bool
  | [], ss => ss.isEmpty
  | e :: es, ss =>
    match takeSome (fun s => if m s e then some () else none) ss with
    | some (_, ss') => matchAll m es ss'
    | none => false

/-- **The code of the integer `z`** modulo `p`: its residue in `[0, p)`. -/
def intCode (p : ℕ) (z : ℤ) : ℕ := (z % (p : ℤ)).toNat

/-- **The transform's order** of the flag `natural`. -/
def nttOrderOf (natural : Bool) : NttOrder := if natural then .natural else .scheme

/-- **A monomial**: the code `coef` times the product of its factors, each an atom expression read
at the coordinates of its path (coordinate `i` of the monomial reads the atom at the path's entry
`i`). -/
structure Mono where
  /-- The code of the scalar. -/
  coef : ℕ
  /-- The factors: a path and an atom. -/
  facs : List (List ℕ × Expr)
  deriving Inhabited

/-- **A monomial scaled by the code `c`**, modulo `p`. -/
def Mono.scale (p c : ℕ) (m : Mono) : Mono := ⟨c * m.coef % p, m.facs⟩

/-- **The product of two monomials**, modulo `p`. -/
def Mono.mul (p : ℕ) (m m' : Mono) : Mono := ⟨m.coef * m'.coef % p, m.facs ++ m'.facs⟩

/-- **The atom `e` read at the path `ps`.** -/
def Mono.atom (ps : List ℕ) (e : Expr) : Mono := ⟨1, [(ps, e)]⟩

/-- **The block `b` a path reads** of the batched transform of `B` blocks of `n`: the path is
`b n, …, b n + n − 1`, `b < B`. -/
def blockOfPath? (n B : ℕ) (ps : List ℕ) : Option ℕ :=
  if decide (0 < n) && decide (ps.headD 0 / n < B) &&
      ps == (List.range n).map (ps.headD 0 / n * n + ·) then some (ps.headD 0 / n) else none

namespace IndexMap

/-- **Entries `ps` of the index map `m`, its runs walked alongside `ps`**: the remaining runs `r`
start at offset `o` of `m`; an entry in the first remaining run is read there, an entry past it
drops the run, and an entry before `o` (a path that is not increasing) is `m.entry`; out of fuel,
the rest are `m.entry`. For an increasing path it costs the path and the runs once, where reading
every entry with `IndexMap.entry` walks the runs from the start each time. -/
def entriesGo (m : IndexMap) : ℕ → IndexMap → ℕ → List ℕ → List ℕ
  | _, _, _, [] => []
  | 0, _, _, ps => ps.map m.entry
  | f + 1, [], o, i :: ps => m.entry i :: entriesGo m f [] o ps
  | f + 1, (s, d, c) :: rest, o, i :: ps =>
    if i < o then m.entry i :: entriesGo m f ((s, d, c) :: rest) o ps
    else if i < o + c then ((s : Int) + d * (i - o : ℕ)).toNat :: entriesGo m f ((s, d, c) :: rest) o ps
    else entriesGo m f rest (o + c) (i :: ps)

/-- **The entries of `m` along the path `ps`** (`entriesGo`, enough fuel for any path the checks
read). -/
def entriesAt (m : IndexMap) (ps : List ℕ) : List ℕ := entriesGo m (2 ^ 40) m 0 ps

end IndexMap

section Norm

variable (ir : RealizedProgram)

/-- **The code a constant leaf reads at every coordinate of the path `ps`**: `u` is a constant of
field `f` whose entries are all one code `c < p`, and every entry of `ps` is below its length. -/
def constCode? (f p u : ℕ) (ps : List ℕ) : Option ℕ :=
  match (ir.value u).kind with
  | .constant es =>
    if decide (ir.valueField u = f) && decide (es.headD 0 < p) && es.all (· == es.headD 0) &&
        ps.all (fun i => decide (i < es.length)) then some (es.headD 0) else none
  | _ => none

/-- **The normal form of a leaf read at `ps`**: the scalar of a constant reading one code there
(`constCode?`), else an atom. -/
def nfLeaf (f p u : ℕ) (ps : List ℕ) : List Mono :=
  match ir.constCode? f p u ps with
  | some c => [⟨c, []⟩]
  | none => [Mono.atom ps (.leaf u)]

/-- **The normal form of a named operator read at `ps`**: a block of a batched transform read
whole is the transform of the operand's block (`blockOfPath?`); else an atom. -/
def nfApply (ps : List ℕ) (op : NamedOp) (x : Expr) : List Mono :=
  match op with
  | .batched B (.ntt n psi o) =>
    match blockOfPath? n B ps with
    | some b => [Mono.atom (List.range n) (.apply (.ntt n psi o) (.reindex [(b * n, 1, n)] x))]
    | none => [Mono.atom ps (.apply op x)]
  | _ => [Mono.atom ps (.apply op x)]

/-- **The normal form of an expression read at the coordinates `ps`**, in field `f` of
characteristic `p`, with `k` levels (see the module docstring); none when the levels run out. -/
def nf (f p : ℕ) : ℕ → List ℕ → Expr → Option (List Mono)
  | 0, _, _ => none
  | k + 1, ps, e =>
    match e with
    | .add a b => do
      let x ← nf f p k ps a
      let y ← nf f p k ps b
      pure (x ++ y)
    | .sub a b => do
      let x ← nf f p k ps a
      let y ← nf f p k ps b
      pure (x ++ y.map (Mono.scale p (intCode p (-1))))
    | .scale c a =>
      match c with
      | .const c =>
        if c < p then (nf f p k ps a).map (List.map (Mono.scale p c))
        else some [Mono.atom ps (.scale (.const c) a)]
      | .node v j => some [Mono.atom ps (.scale (.node v j) a)]
    | .mul a b => do
      let x ← nf f p k ps a
      let y ← nf f p k ps b
      pure (x.flatMap fun m => y.map (Mono.mul p m))
    | .reindex idx a => nf f p k (idx.entriesAt ps) a
    | .concat a b =>
      if ps.all (fun i => decide (i < ir.exprLen a)) then nf f p k ps a
      else if ps.all (fun i => decide (ir.exprLen a ≤ i)) then
        nf f p k (ps.map (· - ir.exprLen a)) b
      else some [Mono.atom ps (.concat a b)]
    | .ref j => if j < ir.exprs.length then nf f p k ps (ir.expr j) else some [Mono.atom ps (.ref j)]
    | .leaf u => some (ir.nfLeaf f p u ps)
    | .apply op x => some (nfApply ps op x)
    | .linear rows a => some [Mono.atom ps (.linear rows a)]
    | .prod w a => some [Mono.atom ps (.prod w a)]
    | .mux b t a => some [Mono.atom ps (.mux b t a)]
    | .logic op w args => some [Mono.atom ps (.logic op w args)]

/-- **Two factors agree**, with `k` levels: equal paths, and structurally equal atoms or two
transforms `.apply (.ntt n ψ o)` read below `n` whose operands' normal forms below `n` agree. -/
def facEqB (f p : ℕ) : ℕ → List ℕ × Expr → List ℕ × Expr → Bool
  | 0, _, _ => false
  | k + 1, (ps, a), (ps', a') =>
    ps == ps' && (a.beq a' ||
      match a, a' with
      | .apply (.ntt n psi o) x, .apply op' x' =>
        decide (op' = .ntt n psi o) && decide (0 < n) && ps.all (fun i => decide (i < n)) &&
          match nf ir f p k (List.range n) x, nf ir f p k (List.range n) x' with
          | some ms, some ms' =>
            matchAll (fun m' m => m.coef == m'.coef && matchAll (facEqB f p k) m.facs m'.facs)
              ms ms'
          | _, _ => false
      | _, _ => false)

/-- **Two monomials agree**, with `k` levels: equal codes, factors matched one to one
(`facEqB`). -/
def monoEqB (f p k : ℕ) (m' m : Mono) : Bool :=
  m.coef == m'.coef && matchAll (ir.facEqB f p k) m.facs m'.facs

/-- **The normal forms of a list of expressions** read at `ps`, concatenated. -/
def nfSum (f p k : ℕ) (ps : List ℕ) : List Expr → Option (List Mono)
  | [] => some []
  | e :: es => do
    let x ← ir.nf f p k ps e
    let y ← nfSum f p k ps es
    pure (x ++ y)

/-- **A kernel part's term as an expression**: block `b` of its value times the transform of its
operand, rows of `n` coordinates. -/
def kernelExpr (sh : ProductShape) (κ : KernelPart) : Expr :=
  .mul (.reindex [(κ.block * sh.n, 1, sh.n)] (.leaf κ.value))
    (.apply (.ntt sh.n sh.psi (nttOrderOf sh.natural)) κ.operand)

/-- **The normal forms of kernel parts' terms**, each scaled by its scale's code (negated with
`neg`); none when a scale is not below `p`. -/
def kernelMonos (f p k : ℕ) (sh : ProductShape) (neg : Bool) : List KernelPart → Option (List Mono)
  | [] => some []
  | κ :: κs => do
    let x ← ir.nf f p k (List.range sh.n) (kernelExpr sh κ)
    let y ← kernelMonos f p k sh neg κs
    if κ.scale < p then
      pure (x.map (Mono.scale p (intCode p (if neg then -(κ.scale : ℤ) else κ.scale))) ++ y)
    else none

/-- **The quotient's row `r` times `−m`**, normalized (none for a form without a quotient). -/
def quotMonos (f p k m : ℕ) (real : ModRealization) (sh : ProductShape) (r : ℕ) :
    Option (List Mono) :=
  match real.quotient with
  | some Q =>
    (ir.nf f p k ((List.range sh.n).map (r * sh.n + ·)) Q).map
      (List.map (Mono.scale p (intCode p (-(m : ℤ)))))
  | none => some []

/-- **The expected normal form of row `r`'s transformed operand `L`**, rows `PR`, `NR` of the sides:
the expression parts of `PR`, those of `NR` negated, `−m` times the quotient's row, and the scalar
`−m qlo` when `qlo ≠ 0`. -/
def lhsMonos (f p k m : ℕ) (real : ModRealization) (sh : ProductShape) (r : ℕ) (PR NR : Expr) :
    Option (List Mono) := do
  let a ← ir.nfSum f p k (List.range sh.n) (ir.rowExprs PR)
  let b ← ir.nfSum f p k (List.range sh.n) (ir.rowExprs NR)
  let q ← ir.quotMonos f p k m real sh r
  pure (a ++ b.map (Mono.scale p (intCode p (-1))) ++ q ++
    if real.quotientLo = 0 then [] else [⟨intCode p (-((m : ℤ) * real.quotientLo)), []⟩])

/-- **The expected normal form of a row's other monomials**: `−s · h_b ⊙ T(x)` for each kernel
part of `NR`, `s · h_b ⊙ T(x)` for each kernel part of `PR`. -/
def rhsMonos (f p k : ℕ) (sh : ProductShape) (PR NR : Expr) : Option (List Mono) := do
  let a ← ir.kernelMonos f p k sh true (ir.rowKernels NR)
  let b ← ir.kernelMonos f p k sh false (ir.rowKernels PR)
  pure (a ++ b)

/-- **The transform monomial's operand**: `L` for the monomial `T L` of code `1` read at
`0, …, n − 1`, `T` the shape's transform. -/
def transformArg? (sh : ProductShape) (m : Mono) : Option Expr :=
  match m.facs with
  | [(ps, .apply op L)] =>
    if m.coef = 1 ∧ op = .ntt sh.n sh.psi (nttOrderOf sh.natural) ∧ ps = List.range sh.n then some L
    else none
  | _ => none

/-- **Row `r` of the asserted equation `X`**, rows `PR`, `NR` of the sides: `X` read at
`r n, …, r n + n − 1` normalizes to `T L` and the rest, `L` agreeing with `lhsMonos` below `n` and
the rest with `rhsMonos` (see the module docstring). -/
def spectralRowB (f p k m : ℕ) (real : ModRealization) (sh : ProductShape) (r : ℕ)
    (PR NR «X» : Expr) : Bool :=
  match ir.nf f p k ((List.range sh.n).map (r * sh.n + ·)) «X» with
  | some ms =>
    match takeSome (transformArg? sh) ms with
    | some (L, rest) =>
      match ir.nf f p k (List.range sh.n) L, ir.lhsMonos f p k m real sh r PR NR,
          ir.rhsMonos f p k sh PR NR with
      | some ls, some el, some er =>
        matchAll (ir.monoEqB f p k) ls el && matchAll (ir.monoEqB f p k) rest er
      | _, _, _ => false
    | none => false
  | none => false

/-- **The node count of an expression**, a Logic builder's arguments not counted. -/
def Expr.nodes : Expr → ℕ
  | .add a b | .sub a b | .mul a b | .concat a b => a.nodes + b.nodes + 1
  | .scale _ a | .reindex _ a | .linear _ a | .prod _ a | .apply _ a => a.nodes + 1
  | .mux b t a => b.nodes + t.nodes + a.nodes + 1
  | .leaf _ | .ref _ | .logic _ _ _ => 1

/-- **The levels of the normal forms** of a product form's check: twice the node counts of `X`,
the sides and the shared expressions, and `8`. -/
def normFuel («X» P N : Expr) : ℕ :=
  2 * («X».nodes + P.nodes + N.nodes + (ir.exprs.map Expr.nodes).sum) + 8

/-- **`X` is the asserted equation of the product form `mod_q P N`** of realization `real` in
domain `d`: a spectral product form whose shape has as many rows of `P` as of `N`, `X` covering
the rows, each row checked by `spectralRowB` in the domain's field (see the module docstring);
`false` for any other form. -/
def productEquationB (d q : ℕ) («X» P N : Expr) (real : ModRealization) : Bool :=
  match real.form, ir.productShape? P N with
  | .spectralProduct, some sh =>
    decide (d < ir.domains.length) && decide (0 < ir.charOf (ir.domainField d)) &&
      decide (0 < sh.n) && sh.rowsP.length == sh.rowsN.length &&
      decide (sh.rowsP.length * sh.n = ir.exprLen «X») &&
      (List.range sh.rowsP.length).all fun r =>
        ir.spectralRowB (ir.domainField d) (ir.charOf (ir.domainField d)) (ir.normFuel «X» P N) q
          real sh r (sh.rowsP.getD r default) (sh.rowsN.getD r default) «X»
  | _, _ => false

end Norm

end GordieHowe.RealizedProgram
