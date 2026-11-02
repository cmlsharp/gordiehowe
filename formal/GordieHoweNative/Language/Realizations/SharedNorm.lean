-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.Realizations.ProductEquation

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.Realizations.SharedNorm`

The definitions of `GordieHowe.Language.Realizations.SharedNorm` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/Realizations/SharedNorm.lean`, which imports this module.
-/

local notation "ℕ" => Nat
local notation "ℤ" => Int

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export

/-- **The modulus of the hashes**, the prime `2^61 − 1`. -/
def hashMod : ℕ := 2305843009213693951

/-- **One step of a hash**: `h` mixed with `x`. -/
def mixH (h x : ℕ) : ℕ := (h * 1099511628211 + x + 1) % hashMod

/-- **The hash of a list of naturals**, from `h`. -/
def hashList : ℕ → List ℕ → ℕ
  | h, [] => h
  | h, x :: xs => hashList (mixH h x) xs

/-- **The hash of an integer.** -/
def intH : ℤ → ℕ
  | .ofNat n => 2 * n
  | .negSucc n => 2 * n + 1

/-- **The hash of a coefficient.** -/
def Coef.hashN : Coef → ℕ
  | .const c => mixH 1 c
  | .node v i => hashList 2 [v, i]

/-- **The hash of an index map**, from `h`. -/
def IndexMap.hashN : IndexMap → ℕ → ℕ
  | [], h => h
  | (s, d, c) :: rest, h => IndexMap.hashN rest (hashList h [s, intH d, c])

/-- **The hash of a polynomial operand's form.** -/
def ConvForm.hashN : ConvForm → ℕ
  | .coefficients => 0
  | .ntt psi => mixH 1 psi
  | .nttNatural psi => mixH 2 psi

/-- **The hash of a transform's order.** -/
def NttOrder.hashN : NttOrder → ℕ
  | .scheme => 0
  | .natural => 1

/-- **The hash of a named operator.** -/
def NamedOp.hashN : NamedOp → ℕ
  | .negacyclicConv h form => hashList 1 [h, form.hashN]
  | .polyMatVec a K L form => hashList 2 [a, K, L, form.hashN]
  | .polyBroadcast t K form => hashList 3 [t, K, form.hashN]
  | .ntt n psi o => hashList 4 [n, psi, o.hashN]
  | .inverseNtt n psi => hashList 5 [n, psi]
  | .nttTranspose n psi => hashList 6 [n, psi]
  | .rowDot M R W => hashList 7 [M, R, W]
  | .macConv r w nch taps => hashList (hashList 8 [r, w, nch]) taps
  | .acyclicConv h lx => hashList 9 [h, lx]
  | .diagonal d => mixH 10 d
  | .scale c => mixH 11 c
  | .constDiagonal d => mixH 12 d
  | .sum w => mixH 13 w
  | .fromDigits k base => hashList 14 [k, base]
  | .batched b op => hashList 15 [b, op.hashN]

/-- **The hash of a Logic builder.** -/
def LogicOp.hashN : LogicOp → ℕ
  | .lt => 0
  | .leq => 1
  | .eq => 2
  | .any => 3
  | .all => 4

/-- **The hash of a sparse row**, from `h`. -/
def rowHash : List (ℕ × Coef) → ℕ → ℕ
  | [], h => h
  | t :: r, h => rowHash r (hashList h [t.1, t.2.hashN])

/-- **The hash of sparse rows**, from `h`. -/
def rowsHash : List (List (ℕ × Coef)) → ℕ → ℕ
  | [], h => h
  | r :: rs, h => rowsHash rs (mixH (rowHash r h) r.length)

mutual

/-- **The structural hash of an expression.** -/
def Expr.hashN : Expr → ℕ
  | .leaf v => mixH 1 v
  | .add a b => hashList 2 [a.hashN, b.hashN]
  | .sub a b => hashList 3 [a.hashN, b.hashN]
  | .scale c a => hashList 4 [c.hashN, a.hashN]
  | .mul a b => hashList 5 [a.hashN, b.hashN]
  | .reindex idx a => mixH (IndexMap.hashN idx 6) a.hashN
  | .concat a b => hashList 7 [a.hashN, b.hashN]
  | .linear rows a => mixH (rowsHash rows 8) a.hashN
  | .prod n a => hashList 9 [n, a.hashN]
  | .mux b t a => hashList 10 [b.hashN, t.hashN, a.hashN]
  | .apply op a => hashList 11 [op.hashN, a.hashN]
  | .ref k => mixH 12 k
  | .logic op w args => hashList 13 [op.hashN, w, Expr.hashNList args]

/-- The structural hash of a list of expressions. -/
def Expr.hashNList : List Expr → ℕ
  | [] => 0
  | e :: es => mixH e.hashN (Expr.hashNList es)

end

/-- **The key of an atom**: `4u` for a leaf, `4j + 1` for a shared expression, `4h + 2` for any
other atom of hash `h`. -/
def atomKey : Expr → ℕ
  | .leaf u => 4 * u
  | .ref j => 4 * j + 1
  | e => 4 * e.hashN + 2

/-- **A factor**: an atom read along a path, with its key. -/
structure SFac where
  /-- The key: the atom's, then the path's hash. -/
  key : ℕ
  /-- The path. -/
  path : List ℕ
  /-- The atom. -/
  atom : Expr
  deriving Inhabited

/-- **The factor of the atom `e` read along `ps`.** -/
def SFac.of (ps : List ℕ) (e : Expr) : SFac := ⟨atomKey e * hashMod + hashList 0 ps, ps, e⟩

/-- **Equal factors**: equal keys, paths and atoms. -/
def SFac.same (x y : SFac) : Bool := Nat.beq x.key y.key && x.path == y.path && x.atom.beq y.atom

/-- **Equal factor lists**, factor by factor. -/
def sameFacs : List SFac → List SFac → Bool
  | [], [] => true
  | x :: xs, y :: ys => x.same y && sameFacs xs ys
  | _, _ => false

/-- **The order of factor lists**: lexicographic on the keys, a shorter list first. -/
def keyCmp : List SFac → List SFac → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | x :: xs, y :: ys =>
    cond (Nat.blt x.key y.key) .lt (cond (Nat.blt y.key x.key) .gt (keyCmp xs ys))

/-- **A monomial**: the code `coef` times its factors, sorted by key. -/
structure SMono where
  /-- The code of the scalar. -/
  coef : ℕ
  /-- The factors. -/
  facs : List SFac
  deriving Inhabited

/-- `m` in front of `q`, unless its code is `0`. -/
def SMono.push (m : SMono) (q : List SMono) : List SMono := cond (Nat.beq m.coef 0) q (m :: q)

/-- **The sum of two normal forms**, modulo `p`: a merge on the keys with `n` steps of fuel (out of
fuel, the concatenation); two monomials of equal factors combine. -/
def sAddF (p : ℕ) : ℕ → List SMono → List SMono → List SMono
  | 0, x, y => x ++ y
  | _ + 1, [], y => y
  | _ + 1, m :: x, [] => m :: x
  | n + 1, m :: x, m' :: y =>
    match keyCmp m.facs m'.facs with
    | .lt => m :: sAddF p n x (m' :: y)
    | .gt => m' :: sAddF p n (m :: x) y
    | .eq =>
      cond (sameFacs m.facs m'.facs)
        (SMono.push ⟨(m.coef + m'.coef) % p, m.facs⟩ (sAddF p n x y))
        (m :: m' :: sAddF p n x y)

/-- **The sum of two normal forms**, with enough fuel for any the checks build. -/
def sAdd (p : ℕ) (x y : List SMono) : List SMono := sAddF p (2 ^ 40) x y

/-- **The code `c` times a normal form**, modulo `p`, zeros dropped. -/
def sScale (p c : ℕ) : List SMono → List SMono
  | [] => []
  | m :: q => SMono.push ⟨c * m.coef % p, m.facs⟩ (sScale p c q)

/-- **Two sorted factor lists merged** by key, with `n` steps of fuel. -/
def mergeFacs : ℕ → List SFac → List SFac → List SFac
  | 0, x, y => x ++ y
  | _ + 1, [], y => y
  | _ + 1, a :: x, [] => a :: x
  | n + 1, a :: x, b :: y =>
    cond (Nat.ble a.key b.key) (a :: mergeFacs n x (b :: y)) (b :: mergeFacs n (a :: x) y)

/-- **The product of two monomials**, modulo `p`. -/
def SMono.mul (p : ℕ) (m m' : SMono) : SMono :=
  ⟨m.coef * m'.coef % p, mergeFacs (2 ^ 40) m.facs m'.facs⟩

/-- One round of pairwise sums. -/
def sPairs (p : ℕ) : List (List SMono) → List (List SMono)
  | x :: y :: r => sAdd p x y :: sPairs p r
  | r => r

/-- Pairwise sums until one normal form is left, with fuel (out of fuel, the concatenation). -/
def sSumAll (p : ℕ) : ℕ → List (List SMono) → List SMono
  | _, [] => []
  | _, [x] => x
  | 0, xs => xs.flatten
  | n + 1, xs => sSumAll p n (sPairs p xs)

/-- **The sum of a list of normal forms**: `64` rounds of pairwise sums. -/
def sSum (p : ℕ) (xs : List (List SMono)) : List SMono := sSumAll p 64 xs

/-- **The product of two normal forms**: the sum of the monomial products. -/
def sMul (p : ℕ) (x y : List SMono) : List SMono :=
  sSum p (x.flatMap fun m => y.map fun m' => SMono.push (m.mul p m') [])

/-- **A factor list sorted by key.** -/
def sortFacs : List (List ℕ × Expr) → List SFac
  | [] => []
  | x :: xs => mergeFacs (2 ^ 40) [SFac.of x.1 x.2] (sortFacs xs)

/-- **A monomial of `nf`** as a monomial with sorted factors. -/
def SMono.ofMono (m : Mono) : SMono := ⟨m.coef, sortFacs m.facs⟩

/-- **A list of monomials of `nf`** as a normal form, modulo `p`. -/
def ofMonos (p : ℕ) (ms : List Mono) : List SMono :=
  sSum p (ms.map fun m => SMono.push (SMono.ofMono m) [])

/-- **The atom `e` read along `ps`.** -/
def sAtom (ps : List ℕ) (e : Expr) : List SMono := [⟨1, [SFac.of ps e]⟩]

section Norm

variable (ir : RealizedProgram)

/-- **The normal form of an expression read at the coordinates `ps`**, in field `f` of
characteristic `p`, with `k` levels (see the module docstring); none when the levels run out. -/
def nfS (f p : ℕ) : ℕ → List ℕ → Expr → Option (List SMono)
  | 0, _, _ => none
  | k + 1, ps, e =>
    match e with
    | .add a b => do
      let x ← nfS f p k ps a
      let y ← nfS f p k ps b
      pure (sAdd p x y)
    | .sub a b => do
      let x ← nfS f p k ps a
      let y ← nfS f p k ps b
      pure (sAdd p x (sScale p (intCode p (-1)) y))
    | .scale c a =>
      match c with
      | .const c =>
        if c < p then (nfS f p k ps a).map (sScale p c)
        else some (sAtom ps (.scale (.const c) a))
      | .node v j => some (sAtom ps (.scale (.node v j) a))
    | .mul a b => do
      let x ← nfS f p k ps a
      let y ← nfS f p k ps b
      pure (sMul p x y)
    | .reindex idx a => nfS f p k (idx.entriesAt ps) a
    | .concat a b =>
      if ps.all (fun i => decide (i < ir.exprLen a)) then nfS f p k ps a
      else if ps.all (fun i => decide (ir.exprLen a ≤ i)) then
        nfS f p k (ps.map (· - ir.exprLen a)) b
      else some (sAtom ps (.concat a b))
    | .ref j => some (sAtom ps (.ref j))
    | .leaf u => some (ofMonos p (ir.nfLeaf f p u ps))
    | .apply op x => some (ofMonos p (nfApply ps op x))
    | .linear rows a => some (sAtom ps (.linear rows a))
    | .prod w a => some (sAtom ps (.prod w a))
    | .mux b t a => some (sAtom ps (.mux b t a))
    | .logic op w args => some (sAtom ps (.logic op w args))

/-- **The factor is `.ref j` read along a path of length at least `L`.** -/
def SFac.isRefAt (L j : ℕ) (x : SFac) : Bool :=
  match x.atom with
  | .ref j' => Nat.beq j' j && Nat.ble L x.path.length
  | _ => false

/-- **A factor list with every factor `.ref j` (paths of length at least `L`) replaced** by the
normal form of `expr j` along its path, multiplied out. -/
def unfoldFacs (f p k L j : ℕ) : List SFac → Option (List SMono)
  | [] => some [⟨1 % p, []⟩]
  | x :: xs =>
    match unfoldFacs f p k L j xs with
    | none => none
    | some r =>
      cond (x.isRefAt L j)
        ((nfS ir f p k x.path (ir.expr j)).map fun e => sMul p e r)
        (some (sMul p [⟨1 % p, [x]⟩] r))

/-- **A monomial with shared expression `j` unfolded**: itself when it reads no factor `.ref j`. -/
def unfoldMono (f p k L j : ℕ) (m : SMono) : Option (List SMono) :=
  cond (m.facs.any (SFac.isRefAt L j)) ((unfoldFacs ir f p k L j m.facs).map (sScale p m.coef))
    (some [m])

/-- **Every monomial with shared expression `j` unfolded.** -/
def unfoldAll (f p k L j : ℕ) : List SMono → Option (List (List SMono))
  | [] => some []
  | m :: D =>
    match unfoldMono ir f p k L j m, unfoldAll f p k L j D with
    | some a, some b => some (a :: b)
    | _, _ => none

/-- **One more than the largest `j < n`** read as a factor `.ref j` along a path of length at least
`L`, or `0`. -/
def maxRef (n L : ℕ) (D : List SMono) : ℕ :=
  D.foldl (fun a m => m.facs.foldl (fun a x =>
    match x.atom with
    | .ref j => cond (Nat.blt j n && Nat.ble L x.path.length && Nat.ble a j) (j + 1) a
    | _ => a) a) 0

/-- **The normal form `D` is zero at every coordinate below `L`**, with `n` steps: `D` is empty, or
its largest shared expression unfolded (`maxRef`, `unfoldAll`) leaves a normal form that is. -/
def zeroLoop (f p k L : ℕ) : ℕ → List SMono → Bool
  | 0, D => D.isEmpty
  | n + 1, D =>
    D.isEmpty ||
      (Nat.blt 0 (maxRef ir.exprs.length L D) &&
        Nat.ble (maxRef ir.exprs.length L D) ir.exprs.length &&
        match unfoldAll ir f p k L (maxRef ir.exprs.length L D - 1) D with
        | some rs => zeroLoop f p k L n (sSum p rs)
        | none => false)

end Norm

end GordieHowe.RealizedProgram
