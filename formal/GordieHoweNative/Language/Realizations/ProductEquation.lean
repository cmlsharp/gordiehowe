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

/-- **The code of the integer `z`** modulo `p`: its residue in `[0, p)`. -/
def intCode (p : ℕ) (z : ℤ) : ℕ := (z % (p : ℤ)).toNat

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

/-- **The node count of an expression**, a Logic builder's arguments not counted. -/
def Expr.nodes : Expr → ℕ
  | .add a b | .sub a b | .mul a b | .concat a b => a.nodes + b.nodes + 1
  | .scale _ a | .reindex _ a | .linear _ a | .prod _ a | .apply _ a => a.nodes + 1
  | .mux b t a => b.nodes + t.nodes + a.nodes + 1
  | .leaf _ | .ref _ | .logic _ _ _ => 1

/-- **The levels of the normal forms** of an entry's check: twice the node counts of `X`, the
sides and the shared expressions, and `8`. -/
def normFuel («X» P N : Expr) : ℕ :=
  2 * («X».nodes + P.nodes + N.nodes + (ir.exprs.map Expr.nodes).sum) + 8

end Norm

end GordieHowe.RealizedProgram
