-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.Realizations.Derivation.Basic
public import GordieHoweNative.Language.Realizations.Derivation.Roots

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.Realizations.Derivation.Rules`

The definitions of `GordieHowe.Language.Realizations.Derivation.Rules` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/Realizations/Derivation/Rules.lean`, which imports this module.
-/

local notation "ℕ" => Nat
local notation "ℤ" => Int

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export

section

variable (ir : RealizedProgram)

/-- **The field equation of a predicate body**: of a field `equal` or a `mod_0`. -/
def realizedOf : PredBody → Option Fact
  | .equal d a b _ => some (.eq d a b)
  | .mod d q a b _ => if q = 0 then some (.eq d a b) else none
  | _ => none

/-- **`realized p`**: the field equation of a field `equal` or a `mod_0`. -/
def realizedFact (p : ℕ) : Option Fact :=
  if p < ir.predicates.length then realizedOf (ir.predicate p).body else none

/-- **`subst e₁ e₂`**: `e₂` is the entry of the shared expression `e₁`, or the expression of the
bound value `e₁` (of domain `d`'s field). -/
def substFact (d : ℕ) (e₁ e₂ : Expr) : Option Fact :=
  match e₁ with
  | .ref k => if k < ir.exprs.length ∧ (ir.expr k).beq e₂ = true then some (.eq d e₁ e₂) else none
  | .leaf v =>
    match (ir.value v).kind with
    | .bound x =>
      if v < ir.values.length ∧ x.beq e₂ = true ∧ ir.valueField v = ir.domainField d then
        some (.eq d e₁ e₂)
      else none
    | _ => none
  | _ => none

/-- **The terms of a linear step's premises**: for each `(k, c)`, the `eq` fact `a = b` of domain
`d` at premise `k` (`a` of length at least `n`) gives the terms `c · a` and `−c · b`. -/
def linPrem (fs : List Fact) (d n : ℕ) : List (ℕ × ℤ) → Option (List (ℤ × Expr))
  | [] => some []
  | (k, c) :: cs =>
    match fs[k]? with
    | some (.eq d' a b) =>
      if d' = d ∧ n ≤ ir.exprLen a then
        (linPrem fs d n cs).map fun ts => (c, a) :: (-c, b) :: ts
      else none
    | _ => none

/-- **The linear form of a combination** `Σ c · x` of expressions (`linForm`), in field `f` at
the first `n` coordinates. -/
def linTerms (f n : ℕ) : List (ℤ × Expr) → Option (ℤ × List (ℤ × Expr))
  | [] => some (0, [])
  | (c, x) :: ts =>
    (ir.linForm f n x).bind fun a => (linTerms f n ts).map fun b =>
      (c * a.1 + b.1, a.2.map (fun t => (c * t.1, t.2)) ++ b.2)

/-- **`linear cs e₁ e₂`** in domain `d`: the combination of the premises' equations minus
`e₁ − e₂` vanishes modulo the characteristic as a linear form. -/
def linearFact (fs : List Fact) (d : ℕ) (cs : List (ℕ × ℤ)) (e₁ e₂ : Expr) : Option Fact :=
  if d < ir.domains.length then
    match ir.linPrem fs d (ir.exprLen e₁) cs with
    | some ts =>
      match ir.linTerms (ir.domainField d) (ir.exprLen e₁) (ts ++ [(-1, e₁), (1, e₂)]) with
      | some x =>
        if linZeroB (ir.charOf (ir.domainField d)) x = true then some (.eq d e₁ e₂) else none
      | none => none
    | none => none
  else none

/-- **Member `m` of group `g` of table `t`.** -/
def memberAt (t g m : ℕ) : Member := (ir.members t g).getD m default

/-- **The needle of member `m` of group `g` of table `t`.** -/
def memberNeedle (t g m : ℕ) : Expr :=
  ir.needleExpr (ir.memberAt t g m).pred (ir.memberAt t g m).needle

/-- **The end of contiguous slices** starting at `pos`: each member starts where the previous one
ends. -/
def sliceEnd : List Member → ℕ → Option ℕ
  | [], pos => some pos
  | m :: ms, pos => if m.first = pos then sliceEnd ms (pos + m.count) else none

/-- **A member reference `(t, g, m)` of table `t` names a member of a group of `t`** whose needle
is `N`. -/
def memberRefB (t : ℕ) (N : Expr) (x : ℕ × ℕ × ℕ) : Bool :=
  decide (x.1 = t) && decide (x.2.1 < ir.groupCountOf t) &&
    decide (x.2.2 < (ir.members t x.2.1).length) && (ir.memberNeedle t x.2.1 x.2.2).beq N

/-- **`lookup ms`**: the members `ms`, all of one table `t` and one needle `N`, are contiguous
slices from `N`'s first coordinate covering its length; `N`'s coordinates are rows of `t` (or a
group's challenge is bad). -/
def lookupFact : List (ℕ × ℕ × ℕ) → Option Fact
  | [] => none
  | (t, g, m) :: ms =>
    if t < ir.tables.length ∧ ((t, g, m) :: ms).all (ir.memberRefB t (ir.memberNeedle t g m)) = true then
      match sliceEnd (((t, g, m) :: ms).map fun x => ir.memberAt x.1 x.2.1 x.2.2) 0 with
      | some q =>
        if ir.exprLen (ir.memberNeedle t g m) ≤ q then some (.inRows t (ir.memberNeedle t g m))
        else none
      | none => none
    else none

/-- **`rangeNat k`** in domain `d`: the rows of a range `[0, T)`, in a challenge of `d`'s field, are
casts of naturals below `T`. -/
def rangeNatFact (fs : List Fact) (d k : ℕ) : Option Fact :=
  match fs[k]? with
  | some (.inRows t x) =>
    match (ir.table t).rows with
    | .range T =>
      if ir.chalField (ir.alphaOf t) = ir.domainField d then some (.nat d x T) else none
    | _ => none
  | _ => none

/-- **`holdsIn k`**: an `in` `x ∈ [0, N)` that holds bounds `x`. -/
def holdsInFact (fs : List Fact) (k : ℕ) : Option Fact :=
  match fs[k]? with
  | some (.holds q) =>
    match (ir.predicate q).body with
    | .mem d [x] (.range N) _ => some (.nat d x N)
    | _ => none
  | _ => none

/-- **The guard of a `src` step**: `v` is a value of domain `d`'s field, of characteristic above
`2`. -/
def srcGuard (d v : ℕ) : Bool :=
  decide (v < ir.values.length) && decide (d < ir.domains.length) &&
    decide (ir.valueField v = ir.domainField d) && decide (2 < ir.charOf (ir.domainField d))

/-- **`src v s`** in domain `d`: the interval of the leaf `v` from its source (a constant's entries
checked below the characteristic in one walk by the recursor, `allK`). -/
def srcFact (primeNodes : ℕ → List String) (sr : List (ℕ × ℕ)) (fs : List Fact) (d v : ℕ) :
    IvlSrc → Option Fact
  | .const =>
    match (ir.value v).kind with
    | .constant es =>
      if allK (· < ir.charOf (ir.domainField d)) es = true then
        some (.ivl d (.leaf v) (constIvlOf (ir.charOf (ir.domainField d)) (ir.value v).size es).lo
          (constIvlOf (ir.charOf (ir.domainField d)) (ir.value v).size es).hi)
      else none
    | _ => none
  | .declared k =>
    match sr[k]? with
    | some (w, N) =>
      if w = v ∧ natReadB (ir.value v).kind N (ir.charOf (ir.domainField d)) = true ∧ 0 < N ∧
          N ≤ ir.charOf (ir.domainField d)
      then some (.ivl d (.leaf v) 0 ((N : ℤ) - 1))
      else none
    | none => none
  | .nat k =>
    match fs[k]? with
    | some (.nat d' x N) =>
      if d' = d ∧ x.beq (.leaf v) = true ∧
          natReadB (ir.value v).kind N (ir.charOf (ir.domainField d)) = true ∧ 0 < N ∧
          N ≤ ir.charOf (ir.domainField d) then
        some (.ivl d (.leaf v) 0 ((N : ℤ) - 1))
      else none
    | _ => none
  | .prime =>
    match (ir.value v).type, (ir.value v).typeSource with
    | .sub E, .node =>
      if isPlainKind (ir.value v).kind = true ∧ (ir.value v).field = none ∧
          (ir.value v).domain < ir.domains.length ∧ E ∈ primeNodes (ir.value v).domain then
        some (.ivl d (.leaf v) 0 ((ir.charOf (ir.domainField d) : ℤ) - 1))
      else none
    | _, _ => none
  | .shift k =>
    match fs[k]? with
    | some (.nat d' (.add (.leaf w) (.leaf c)) N) =>
      if d' = d ∧ w = v ∧ isPlainKind (ir.value v).kind = true then
        match ir.constEntry c (ir.value v).size (ir.domainField d) with
        | some c0 =>
          if centeredZ (ir.charOf (ir.domainField d)) c0 ≤ 0 ∧
              (N : ℤ) - 1 - centeredZ (ir.charOf (ir.domainField d)) c0 < ir.charOf (ir.domainField d) then
            some (.ivl d (.leaf v) (-centeredZ (ir.charOf (ir.domainField d)) c0)
              ((N : ℤ) - 1 - centeredZ (ir.charOf (ir.domainField d)) c0))
          else none
        | none => none
      else if d' = d ∧ w = v ∧ (ir.value v).kind.isBound = true then
        match ir.constEntry c (ir.value v).size (ir.domainField d) with
        | some c0 =>
          if 0 < N ∧ 2 * max (centeredZ (ir.charOf (ir.domainField d)) c0) (-(centeredZ (ir.charOf (ir.domainField d)) c0)) <
                (ir.charOf (ir.domainField d) : ℤ) ∧
              2 * max ((N : ℤ) - 1 - centeredZ (ir.charOf (ir.domainField d)) c0) (-((N : ℤ) - 1 - centeredZ (ir.charOf (ir.domainField d)) c0)) <
                (ir.charOf (ir.domainField d) : ℤ) then
            some (.ivl d (.leaf v) (-centeredZ (ir.charOf (ir.domainField d)) c0)
              ((N : ℤ) - 1 - centeredZ (ir.charOf (ir.domainField d)) c0))
          else none
        | none => none
      else none
    | _ => none
  | .opaqueBit =>
    match (ir.value v).kind with
    | .pub (.opaque _ (_ :: _)) =>
      if (ir.value v).type = .bit then some (.ivl d (.leaf v) 0 (((2 : ℕ) : ℤ) - 1)) else none
    | _ => none
  | .quadRoot q r =>
    match fs[r]? with
    | some (.ivl d' (.leaf m) lo hi) =>
      if d' = d ∧ ir.valueField m = ir.domainField d ∧ isPlainKind (ir.value v).kind = true then
        match ir.quadSrcN v q m lo hi with
        | some N => some (.ivl d (.leaf v) 0 ((N : ℤ) - 1))
        | none => none
      else none
    | _ => none
  | .rootSet qs =>
    if isPlainKind (ir.value v).kind = true then
      match ir.rootSetSrc v qs with
      | some J => some (.ivl d (.leaf v) J.lo J.hi)
      | none => none
    else none
  | .tableHull _ _ _ => none

/-- **The intervals of an `ivlExpr` step's premises**, in order: the `ivl` facts of domain `d` at
the premises `ks`. -/
def ivlPrem (fs : List Fact) (d : ℕ) : List ℕ → Option (List (Expr × Ivl))
  | [] => some []
  | k :: ks =>
    match fs[k]? with
    | some (.ivl d' x a b) => if d' = d then (ivlPrem fs d ks).map ((x, ⟨a, b⟩) :: ·) else none
    | _ => none

/-- **One node of the interval walk** at the characteristic `p`, the walk below it `w`: a sum,
difference or product of operands (the second at least as long as the first), a multiple by a
constant below `p` (read centred), a view in range of its operand, or a shared expression (its
entry). -/
def ivlNode (p f : ℕ) (w : Expr → List (Expr × Ivl) → Option (Ivl × List (Expr × Ivl)))
    (e : Expr) (ps : List (Expr × Ivl)) : Option (Ivl × List (Expr × Ivl)) :=
  match e with
  | .leaf v =>
    match (ir.value v).kind with
    | .constant es =>
      if 0 < p ∧ allK (· < p) es = true ∧ ir.valueField v = f then
        some (constIvlOf p (ir.value v).size es, ps)
      else none
    | _ => none
  | .add a b =>
    if ir.exprLen a ≤ ir.exprLen b then
      (w a ps).bind fun r => (w b r.2).map fun r' => (r.1.add r'.1, r'.2)
    else none
  | .sub a b =>
    if ir.exprLen a ≤ ir.exprLen b then
      (w a ps).bind fun r => (w b r.2).map fun r' => (r.1.sub r'.1, r'.2)
    else none
  | .mul a b =>
    if ir.exprLen a ≤ ir.exprLen b then
      (w a ps).bind fun r => (w b r.2).map fun r' => (r.1.mul r'.1, r'.2)
    else none
  | .scale (.const c) a =>
    if c < p then (w a ps).map fun r => (r.1.smul (centeredZ p c), r.2) else none
  | .reindex idx a => if idx.inRange (ir.exprLen a) = true then w a ps else none
  | .concat a b => (w a ps).bind fun r => (w b r.2).map fun r' => (r.1.hull r'.1, r'.2)
  | .ref k => if k < ir.exprs.length then w (ir.expr k) ps else none
  | .apply op a =>
    match op.sumWidth with
    | some m => if 2 < p then (w a ps).map fun r => (r.1.nsmul m, r.2) else none
    | none =>
      if 2 < p then
        (w a ps).bind fun r =>
          match op.macIvl p r.1 with
          | some J => some (J, r.2)
          | none => (op.polyIvl ir (fun _ => none) p r.1).map fun J => (J, r.2)
      else none
  | .linear rows a =>
    if (rows.all fun row => row.all fun t => decide (t.1 < ir.exprLen a)) = true then
      (w a ps).bind fun r => (linIvl p r.1 rows).map fun K => (K, r.2)
    else none
  | _ => none

/-- **The interval walk** of `e` at the characteristic `p`, consuming the premises `ps` in
pre-order: a node equal to the next premise's expression takes its interval; any other node
descends by its rule (`ivlNode`). Returns the interval and the premises left. -/
def ivlWalk (p f : ℕ) : ℕ → Expr → List (Expr × Ivl) → Option (Ivl × List (Expr × Ivl))
  | 0, _, _ => none
  | n + 1, e, ps =>
    match ps with
    | (x, J) :: ps' =>
      if x.beq e = true then some (J, ps') else ir.ivlNode p f (ivlWalk p f n) e ps
    | [] => ir.ivlNode p f (ivlWalk p f n) e ps

/-- **The fuel of the interval walk**: its nodes and shared-expression descents. -/
def walkFuel : ℕ := 1000000

/-- **`ivlExpr ks x lo hi`** in domain `d`: the interval walk of `x` consuming every premise
lies within `[lo, hi]`. -/
def ivlExprFact (fs : List Fact) (d : ℕ) (ks : List ℕ) (x : Expr) (lo hi : ℤ) : Option Fact :=
  if d < ir.domains.length ∧ 2 < ir.charOf (ir.domainField d) then
    match ivlPrem fs d ks with
    | some ps =>
      match ir.ivlWalk (ir.charOf (ir.domainField d)) (ir.domainField d) walkFuel x ps with
      | some (J, []) => if J.Within lo hi then some (.ivl d x lo hi) else none
      | _ => none
    | none => none
  else none

/-- **`transport k j`**: from `e₁ = e₂` (`k`) and a range or the rows of a table of `e₁` (`j`),
the same of `e₂`, of at most `e₁`'s length. -/
def transportFact (fs : List Fact) (k j : ℕ) : Option Fact :=
  match fs[k]? with
  | some (.eq d x y) =>
    if ir.exprLen y ≤ ir.exprLen x then
      match fs[j]? with
      | some (.nat d' x' N) => if d' = d ∧ x'.beq x = true then some (.nat d y N) else none
      | some (.inRows t x') =>
        if ir.chalField (ir.alphaOf t) = ir.domainField d ∧ x'.beq x = true then
          some (.inRows t y)
        else none
      | _ => none
    else none
  | _ => none

/-- **`ivlNat k`** in domain `d`: a plain leaf below `N` lies in `[0, N − 1]`. -/
def ivlNatFact (fs : List Fact) (d k : ℕ) : Option Fact :=
  match fs[k]? with
  | some (.nat d' (.leaf v) N) =>
    if d' = d ∧ ir.srcGuard d v = true ∧ isPlainKind (ir.value v).kind = true ∧ 0 < N ∧
        N ≤ ir.charOf (ir.domainField d) then
      some (.ivl d (.leaf v) 0 ((N : ℤ) - 1))
    else none
  | _ => none

/-- **`ivlMeet a b`**: two intervals of one expression meet. -/
def ivlMeetFact (fs : List Fact) (a b : ℕ) : Option Fact :=
  match fs[a]?, fs[b]? with
  | some (.ivl d x lo hi), some (.ivl d' x' lo' hi') =>
    if d' = d ∧ x'.beq x = true then some (.ivl d x (max lo lo') (min hi hi')) else none
  | _, _ => none

/-- **`natIvl k`**: an expression with a nonnegative interval `[lo, hi]` is below `hi + 1`. -/
def natIvlFact (fs : List Fact) (k : ℕ) : Option Fact :=
  match fs[k]? with
  | some (.ivl d x lo hi) => if 0 ≤ lo then some (.nat d x (hi + 1).toNat) else none
  | _ => none

/-- **The checked expression of a Boolean check** `x · x = x` of domain `d`, `x` a leaf or a shared
expression. -/
def boolOf? : PredBody → Option (ℕ × Expr)
  | .equal d (.mul a b) c _ =>
    match c with
    | .leaf _ => if a.beq c = true ∧ b.beq c = true then some (d, c) else none
    | .ref _ => if a.beq c = true ∧ b.beq c = true then some (d, c) else none
    | _ => none
  | _ => none

/-- **`natBool p`**: a Boolean check bounds its value by `2`. -/
def natBoolFact (p : ℕ) : Option Fact :=
  if p < ir.predicates.length then
    (boolOf? (ir.predicate p).body).map fun dv => .nat dv.1 dv.2 2
  else none

/-- **`natComp k j`** in domain `d`: `e` below `A`, `X` below `B`, `X + e = c` as linear forms,
`A + B − 1 ≤ p`: `e` is at most `c`. -/
def natCompFact (fs : List Fact) (d k j : ℕ) : Option Fact :=
  match fs[k]?, fs[j]? with
  | some (.nat d₁ e A), some (.nat d₂ Xc B) =>
    if d₁ = d ∧ d₂ = d ∧ d < ir.domains.length ∧ ir.exprLen e ≤ ir.exprLen Xc ∧
        A + B - 1 ≤ ir.charOf (ir.domainField d) ∧ 0 < A ∧ 0 < B then
      match ir.linTerms (ir.domainField d) (ir.exprLen e) [(1, Xc), (1, e)] with
      | some x =>
        if (x.1 % (ir.charOf (ir.domainField d) : ℤ)).toNat < ir.charOf (ir.domainField d) ∧
            linZeroB (ir.charOf (ir.domainField d))
              (x.1 - ((x.1 % (ir.charOf (ir.domainField d) : ℤ)).toNat : ℤ), x.2) = true then
          some (.nat d e ((x.1 % (ir.charOf (ir.domainField d) : ℤ)).toNat + 1))
        else none
      | none => none
    else none
  | _, _ => none

/-- **`liftConst k a`** for a `mod_q` body: `x = C` (`k`), `C` a constant holding `c` (centred
`c'`), `x`'s interval `[lo, hi]` (`a`), `q ∣ c'`, `hi − c' < p` and `c' − lo < p`: `x` reads `c'`,
a multiple of `q`. -/
def liftConstFact (fs : List Fact) (body : PredBody) (k a : ℕ) : Option Fact :=
  match body with
  | .mod _ q _ _ _ =>
    match fs[k]?, fs[a]? with
    | some (.eq d x (.leaf C)), some (.ivl d' x' lo hi) =>
      if d' = d ∧ x'.beq x = true ∧ d < ir.domains.length ∧ 0 < q then
        match ir.constEntry C (ir.exprLen x) (ir.domainField d) with
        | some c =>
          if centeredZ (ir.charOf (ir.domainField d)) c % (q : ℤ) = 0 ∧
              hi - centeredZ (ir.charOf (ir.domainField d)) c < ir.charOf (ir.domainField d) ∧
              centeredZ (ir.charOf (ir.domainField d)) c - lo < ir.charOf (ir.domainField d) then
            some (.dvd d x q)
          else none
        | none => none
      else none
    | _, _ => none
  | _ => none

/-- **A multiple of the quotient plus a constant**: `q · Q + C` with `C` a constant holding `c` at
the first `n` coordinates in field `f` (`constEntry`), or `q · Q` (`c = 0`). -/
def quotShape (f n : ℕ) : Expr → Option (ℕ × Expr × ℕ)
  | .add (.scale (.const q) Q) (.leaf u) => (ir.constEntry u n f).map fun c => (q, Q, c)
  | .scale (.const q) Q => some (q, Q, 0)
  | _ => none

/-- **The quotient lift** of `x = y` in domain `d`, `x`'s interval `[lo, hi]` and the range
`nat d₃ Q N` of the quotient: `y = q · Q + C`, `C` holding `c` (read centred `c'`), `q` divides
`c'`, and the no-wrap conditions `hi − c' < p`, `q (N − 1) + c' − lo < p`. -/
def quotLift (d : ℕ) (x y : Expr) (lo hi : ℤ) (d₃ : ℕ) (Q : Expr) (N : ℕ) : Option Fact :=
  match ir.quotShape (ir.domainField d) (ir.exprLen x) y with
  | some (q, Q', c) =>
    if d₃ = d ∧ Q'.beq Q = true ∧ ir.exprLen x ≤ ir.exprLen Q ∧ 0 < q ∧
        q < ir.charOf (ir.domainField d) ∧ 0 < N ∧
        centeredZ (ir.charOf (ir.domainField d)) c % (q : ℤ) = 0 ∧
        hi - centeredZ (ir.charOf (ir.domainField d)) c < ir.charOf (ir.domainField d) ∧
        ((q * (N - 1) : ℕ) : ℤ) + (centeredZ (ir.charOf (ir.domainField d)) c - lo) <
          ir.charOf (ir.domainField d) then
      some (.dvd d x q)
    else none
  | none => none

/-- **`lift k a b`**: from `x = y` (`k`) and `x`'s interval (`a`), the integer equation with `y`'s
interval (`b`) when the span is below the characteristic, or the divisibility by the quotient
lift (`quotLift`) with the quotient's range (`b`). -/
def liftFact (fs : List Fact) (k a b : ℕ) : Option Fact :=
  match fs[k]? with
  | some (.eq d x y) =>
    match fs[a]? with
    | some (.ivl d₂ x' lo hi) =>
      if d < ir.domains.length ∧ d₂ = d ∧ x'.beq x = true then
        match fs[b]? with
        | some (.ivl d₃ y' lo' hi') =>
          if d₃ = d ∧ y'.beq y = true ∧ ir.exprLen x ≤ ir.exprLen y ∧
              hi - lo' < ir.charOf (ir.domainField d) ∧ hi' - lo < ir.charOf (ir.domainField d) then
            some (.intEq d x y)
          else none
        | some (.nat d₃ Q N) => ir.quotLift d x y lo hi d₃ Q N
        | _ => none
      else none
    | _ => none
  | _ => none

/-- **`y` and `z` are equal as linear forms** modulo the characteristic of field `f`, at the first
`n` coordinates. -/
def linSameB (f n : ℕ) (y z : Expr) : Bool :=
  match ir.linTerms f n [(1, y), (-1, z)] with
  | some x => linZeroB (ir.charOf f) x
  | none => false

/-- **The ranges of a `natLin` step**: the `nat` facts of domain `d` at `ks`, each of length at
least `n`. -/
def natLinPrem (fs : List Fact) (d n : ℕ) : List ℕ → Option (List (Expr × ℕ))
  | [] => some []
  | k :: ks =>
    match fs[k]? with
    | some (.nat d' x N) =>
      if d' = d ∧ n ≤ ir.exprLen x then (natLinPrem fs d n ks).map ((x, N) :: ·) else none
    | _ => none

/-- **The coefficient of `x` in a linear form**, modulo `p`. -/
def coefIn (p : ℕ) (ts : List (ℤ × Expr)) (x : Expr) : ℕ :=
  (((ts.filter fun t => t.2.beq x).map (·.1)).sum % (p : ℤ)).toNat

/-- **`natLin k ks`** in domain `d`. -/
def natLinFact (fs : List Fact) (d k : ℕ) (ks : List ℕ) : Option Fact :=
  match fs[k]? with
  | some (.eq d' e y) =>
    let f := ir.domainField d
    let p := ir.charOf f
    if d' = d ∧ d < ir.domains.length then
      match ir.natLinPrem fs d (ir.exprLen e) ks, ir.linForm f (ir.exprLen e) y with
      | some xs, some ly =>
        let cs := xs.map fun xN => (coefIn p ly.2 xN.1, xN.1, xN.2)
        let S := (cs.map fun c => c.1 * (c.2.2 - 1)).sum
        if (cs.all fun c => decide (0 < c.1 ∧ 0 < c.2.2)) = true ∧ S < p ∧
            ir.linSameB f (ir.exprLen e) y (cs.foldr (fun c acc => .add (.scale (.const c.1) c.2.1) acc)
              (.scale (.const 0) e)) = true then
          some (.nat d e (S + 1))
        else none
      | _, _ => none
    else none
  | _ => none

/-- **The digits' sum** `D_0 + T · (D_1 + T · (…))`. -/
def digitExpr (T : ℕ) : Expr → List Expr → Expr
  | D, [] => D
  | D, D' :: Ds => .add D (.scale (.const T) (digitExpr T D' Ds))

/-- **The digits of a `digits` step**: the `nat` facts of domain `d` below at most `T` at the
premises `ks`. -/
def natPrem (fs : List Fact) (d T : ℕ) : List ℕ → Option (List Expr)
  | [] => some []
  | k :: ks =>
    match fs[k]? with
    | some (.nat d' D N) => if d' = d ∧ N ≤ T then (natPrem fs d T ks).map (D :: ·) else none
    | _ => none

/-- **`digits k ds T`** in domain `d`: `x` is the digits' sum (`k`), each digit below `T` (`ds`),
`T` below the characteristic, so `x` is below `T^n`. -/
def digitsFact (fs : List Fact) (d k : ℕ) (ds : List ℕ) (T : ℕ) : Option Fact :=
  match fs[k]? with
  | some (.eq d' x y) =>
    match natPrem fs d T ds with
    | some (D :: Ds) =>
      if d' = d ∧ d < ir.domains.length ∧ (y.beq (digitExpr T D Ds) ||
            ir.linSameB (ir.domainField d) (ir.exprLen x) y (digitExpr T D Ds)) = true ∧
          (D :: Ds).all (fun D' => decide (ir.exprLen x ≤ ir.exprLen D')) = true ∧
          T < ir.charOf (ir.domainField d) then
        some (.nat d x (T ^ (Ds.length + 1)))
      else none
    | _ => none
  | _ => none

/-- **`congr k`** for predicate `pid`: its body is the `mod_q` `e ≡ e'` and `k` is
`dvd d (e − e') q`. -/
def congrFact (fs : List Fact) (pid : ℕ) (body : PredBody) (k : ℕ) : Option Fact :=
  match fs[k]? with
  | some (.dvd d' x q') =>
    match body with
    | .mod d q e e' real =>
      if d' = d ∧ q' = q ∧ x.beq (.sub e e') = true then
        some (.holds pid)
      else none
    | _ => none
  | _ => none

/-- **`conclude k`** for predicate `pid`: the fact `k` is its body (a field `equal`, an `in` into a
range, or a `mod_0`). -/
def concludeFact (fs : List Fact) (pid : ℕ) (body : PredBody) (k : ℕ) : Option Fact :=
  match fs[k]? with
  | some (.eq d' a' b') =>
    match body with
    | .equal d a b _ =>
      if d' = d ∧ a'.beq a = true ∧ b'.beq b = true then some (.holds pid) else none
    | _ => none
  | some (.nat d' x' N') =>
    match body with
    | .mem d [x] (.range N) _ =>
      if d' = d ∧ x'.beq x = true ∧ N' ≤ N then some (.holds pid) else none
    | _ => none
  | some (.inRows t' x') =>
    match body with
    | .mem d [x] (.table t) _ =>
      if t' = t ∧ x'.beq x = true ∧ ir.chalField (ir.alphaOf t) = ir.domainField d then
        some (.holds pid)
      else none
    | .mem d [x] (.expr e') _ =>
      match (ir.table t').rows with
      | .expr e₀ =>
        if e₀.beq e' = true ∧ x'.beq x = true ∧ ir.chalField (ir.alphaOf t') = ir.domainField d then
          some (.holds pid)
        else none
      | _ => none
    | _ => none
  | some (.intEq d' a' b') =>
    match body with
    | .mod d q a b _ =>
      if q = 0 ∧ d' = d ∧ a'.beq a = true ∧ b'.beq b = true then some (.holds pid) else none
    | _ => none
  | _ => none

end

end GordieHowe.RealizedProgram
