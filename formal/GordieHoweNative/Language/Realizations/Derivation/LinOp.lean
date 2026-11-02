-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.Realizations.Derivation.Ntt

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.Realizations.Derivation.LinOp`

The definitions of `GordieHowe.Language.Realizations.Derivation.LinOp` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/Realizations/Derivation/LinOp.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export

section

variable (ir : RealizedProgram)

/-- **The operator application `e` with its operand `a` replaced by `b`**: `e` is `.apply op a`
or `.linear rows a`, every column of `rows` below `a`'s length; `none` otherwise. -/
def opSwap (a b : Expr) : Expr → Option Expr
  | .apply op a' => if a'.beq a = true then some (.apply op b) else none
  | .linear rows a' =>
    if a'.beq a = true ∧ (rows.all fun r => r.all fun t => decide (t.1 < ir.exprLen a)) = true then
      some (.linear rows b)
    else none
  | _ => none

/-- **A row's columns shifted by `o`.** -/
def shiftRow (o : ℕ) (row : List (ℕ × Coef)) : List (ℕ × Coef) := row.map fun t => (o + t.1, t.2)

/-- **Row `r` of a core-language operator's block** as sparse coefficients (`r` below its
`rows`); `none` for an operator whose entries are not coefficients. -/
def opRow : NamedOp → ℕ → Option (List (ℕ × Coef))
  | .rowDot M _ W, r => some ((List.range W).map fun c => (c, .node M (r * W + c)))
  | .diagonal d, r => some [(r, .node d r)]
  | .constDiagonal d, r => some [(r, .node d r)]
  | .scale c, _ => some [(0, .node c 0)]
  | .acyclicConv h lx, r =>
    some (((List.range lx).filter fun a => decide (a ≤ r ∧ r - a < (ir.value h).size)).map
      fun a => (a, .node h (r - a)))
  | .sum w, _ => some ((List.range w).map fun t => (t, .const 1))
  | .batched _ op, r =>
    (opRow op (r % NamedOp.rows ir op)).map
      (shiftRow (r / NamedOp.rows ir op * NamedOp.cols ir op))
  | _, _ => none

/-- **The rows of a negacyclic product's output coordinate `r`** of length `n`, `hc s` the
coefficient of `h_s`, the operand's columns from `off`: `y_r = Σ_{k ≤ r} h_{r−k} x_k −
Σ_{k > r} h_{r+n−k} x_k`, the added and the subtracted entries. -/
def negaRows (n : ℕ) (hc : ℕ → Coef) (off r : ℕ) : List (ℕ × Coef) × List (ℕ × Coef) :=
  (((List.range n).filter fun k => decide (k ≤ r)).map fun k => (off + k, hc (r - k)),
    ((List.range n).filter fun k => decide (r < k)).map fun k => (off + k, hc (r + n - k)))

/-- **The row of a number from its digits** in base `b` modulo `p`, from column `l` with
coefficient `c`: the coefficients `c, c b, c b², …` reduced modulo `p`, each by one
multiplication. -/
def digitRow (p b : ℕ) : ℕ → ℕ → ℕ → List (ℕ × Coef)
  | _, _, 0 => []
  | l, c, n + 1 => (l, .const c) :: digitRow p b (l + 1) (c * b % p) n

/-- **Row `r` of a core-language operator's block** at the characteristic `p`, as the added and
the subtracted sparse coefficients (`r` below its `rows`): the rows of `opRow`, the negacyclic
products by a public operand in coefficient form (`negacyclicConv`, `polyBroadcast`,
`polyMatVec`: `negaRows`), and a number from its digits (`fromDigits`: `digitRow`); `none` for an
operator whose entries are not coefficients. -/
def opRows (p : ℕ) : NamedOp → ℕ → Option (List (ℕ × Coef) × List (ℕ × Coef))
  | .negacyclicConv h .coefficients, r => some (negaRows (ir.value h).size (.node h) 0 r)
  | .polyBroadcast t K .coefficients, j =>
    let n := (ir.value t).size / K
    if j < K * n then some (negaRows n (fun s => .node t (j / n * n + s)) 0 (j % n))
    else some ([], [])
  | .polyMatVec a K L .coefficients, j =>
    let n := (ir.value a).size / (K * L)
    if j < K * n then
      let rs := (List.range L).map fun l =>
        negaRows n (fun s => .node a ((j / n * L + l) * n + s)) (l * n) (j % n)
      some (rs.flatMap (·.1), rs.flatMap (·.2))
    else some ([], [])
  | .fromDigits k base, _ => if base < p then some (digitRow p base 0 (1 % p) k, []) else none
  | .batched _ op, r =>
    (opRows p op (r % NamedOp.rows ir op)).map fun PQ =>
      (shiftRow (r / NamedOp.rows ir op * NamedOp.cols ir op) PQ.1,
        shiftRow (r / NamedOp.rows ir op * NamedOp.cols ir op) PQ.2)
  | op, r => (ir.opRow op r).map fun P => (P, [])

/-- **The coefficient `got` reads as `want`** in field `f`: the same coefficient, or `want` is
coordinate `k` of a constant value of field `f` and `got` its entry `k`. -/
def coefMatch (f : ℕ) (want got : Coef) : Bool :=
  decide (got = want) ||
    match want with
    | .node v k =>
      match (ir.value v).kind with
      | .constant es => decide (ir.valueField v = f) && decide (got = .const (es.getD k 0))
      | _ => false
    | _ => false

/-- **The row `got` reads as the row `want`** in field `f`: entry by entry, the same columns and
matching coefficients. -/
def rowMatch (f : ℕ) : List (ℕ × Coef) → List (ℕ × Coef) → Bool
  | [], [] => true
  | w :: ws, g :: gs => decide (g.1 = w.1) && ir.coefMatch f w.2 g.2 && rowMatch f ws gs
  | _, _ => false

/-- **The rows `R` (added) and `N` (subtracted) from output coordinate `j` on are the
operator's** (`opRows`): row `j` of `.apply op ·` is row `j mod rows` of the block, shifted to
block `j / rows`; a missing subtracted row reads as empty. -/
def rowsOk (f : ℕ) (op : NamedOp) : ℕ → List (List (ℕ × Coef)) → List (List (ℕ × Coef)) → Bool
  | _, [], _ => true
  | j, r :: rs, N =>
    (match ir.opRows (ir.charOf f) op (j % NamedOp.rows ir op) with
      | some PQ =>
        ir.rowMatch f (shiftRow (j / NamedOp.rows ir op * NamedOp.cols ir op) PQ.1) r &&
          ir.rowMatch f (shiftRow (j / NamedOp.rows ir op * NamedOp.cols ir op) PQ.2) (N.headD [])
      | none => false) && rowsOk f op (j + 1) rs N.tail

/-- **`linop s`** in domain `d` (`LinOpStep`): congruence, the matrix form, or the spectral
instance. -/
def linopFact (fs : List Fact) (d : ℕ) : LinOpStep → Option Fact
  | .congr k e =>
    match fs[k]? with
    | some (.eq d' a b) =>
      if d' = d then (ir.opSwap a b e).map fun e' => .eq d e e' else none
    | _ => none
  | .rows op x R N =>
    if d < ir.domains.length ∧ R.length = ir.exprLen (.apply op x) ∧
        (N = [] ∨ N.length = R.length) ∧ ir.rowsOk (ir.domainField d) op 0 R N = true then
      some (.eq d (.apply op x)
        (if N = [] then .linear R x else .sub (.linear R x) (.linear N x)))
    else none
  | .spectral c k =>
    match ir.convs[c]?, fs[k]? with
    | some sc, some (.holds q) =>
      if q = sc.products ∧ d < ir.domains.length ∧ ir.convOkAtB d sc = true then
        some (.eq d (.ref sc.source) (.ref sc.read))
      else none
    | _, _ => none
  | s => ir.nttFact d s

end

end GordieHowe.RealizedProgram
