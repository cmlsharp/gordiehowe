-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Derivation

@[expose] public section


namespace GordieHowe.RealizedProgram

open Export Range IOP

/-! ## A prototype emitter

The derivations of three lowerings, built from the realized program's realization records: a
field `equal` (`realized`, `conclude`), a direct `in` into a range (`lookup`, `rangeNat`,
`conclude`), and a one-digit `mod_q` (the quotient's identity by `subst` and `linear`, its range by
`lookup` and `rangeNat`, the sides' interval by `src` and `ivlExpr`, `lift`, `congr`), and a
`mod_0` in the integer form (`realized`, `src`, `ivlExpr`, `lift`, `conclude`). The emitter is
untrusted: its output is checked by `derivB`. It searches the tables for a needle's members and
the values for the quotient's constant; the checker searches nothing. -/

section Proto

variable (ir : RealizedProgram)

/-- **Insertion into a sorted list** (structural, so the kernel reduces it). -/
def insertBy {α : Type} (le : α → α → Bool) (x : α) : List α → List α
  | [] => [x]
  | y :: ys => if le x y then x :: y :: ys else y :: insertBy le x ys

/-- **The members of table `t` whose needle is `N`**, ordered by their first coordinate. -/
def membersFor (t : ℕ) (N : Expr) : List (ℕ × ℕ × ℕ) :=
  ((List.range (ir.groupCountOf t)).flatMap fun g =>
    ((List.range (ir.members t g).length).filter fun m => (ir.memberNeedle t g m).beq N).map
      fun m => (t, g, m)).foldr (insertBy fun a b =>
    (ir.memberAt a.1 a.2.1 a.2.2).first ≤ (ir.memberAt b.1 b.2.1 b.2.2).first) []

/-- **A range table looking up `N`**, with its members and size. -/
def lookupFor (N : Expr) : Option (List (ℕ × ℕ × ℕ) × ℕ) :=
  (List.range ir.tables.length).findSome? fun t =>
    match (ir.table t).rows with
    | .range T =>
      let ms := ir.membersFor t N
      if ms.isEmpty then none else some (ms, T)
    | _ => none

/-- **The steps bounding the leaf `v`** from fact index `base` on: a constant's entries, a range
lookup, or a prime-subfield read; the index of its `ivl` fact and its interval. -/
def leafChain (p base v : ℕ) : Option (List Step × ℕ × Ivl) :=
  match (ir.value v).kind with
  | .constant es => some ([.src v .const], base, constIvlOf p (ir.value v).size es)
  | _ =>
    match ir.lookupFor (.leaf v) with
    | some (ms, T) =>
      some ([.lookup ms, .rangeNat base, .src v (.nat (base + 1))], base + 2, ⟨0, (T : ℤ) - 1⟩)
    | none =>
      match (List.range ir.predicates.length).find? fun q =>
          (boolOf? (ir.predicate q).body).any fun dv => dv.2.beq (.leaf v) with
      | some q => some ([.natBool q, .src v (.nat base)], base + 1, ⟨0, 1⟩)
      | none => some ([.src v .prime], base, ⟨0, (p : ℤ) - 1⟩)

/-- **The steps bounding the leaves `vs`** from fact index `base` on. -/
def leavesChain (p : ℕ) : ℕ → List ℕ → Option (List Step × List ℕ × List (ℕ × Ivl))
  | _, [] => some ([], [], [])
  | base, v :: vs =>
    (ir.leafChain p base v).bind fun ⟨ss, k, J⟩ =>
      (leavesChain p (base + ss.length) vs).map fun ⟨ss', ks, ls⟩ => (ss ++ ss', k :: ks, (v, J) :: ls)

/-- **The leaves of `e` in the interval walk's pre-order** (`ivlWalk`). -/
def leafOrder : ℕ → Expr → List ℕ
  | 0, _ => []
  | n + 1, e =>
    match e with
    | .leaf v => [v]
    | .add a b => leafOrder n a ++ leafOrder n b
    | .sub a b => leafOrder n a ++ leafOrder n b
    | .mul a b => leafOrder n a ++ leafOrder n b
    | .scale (.const _) a => leafOrder n a
    | .reindex _ a => leafOrder n a
    | .apply _ a => leafOrder n a
    | .concat a b => leafOrder n a ++ leafOrder n b
    | .ref k => leafOrder n (ir.expr k)
    | _ => []

/-- **An `ivlExpr` step for `x`** at the bounded leaves `ls` (each with its fact index and
interval): the premises in the walk's order, and the walk's interval. -/
def ivlExprStep (p f : ℕ) (ls : List (ℕ × ℕ × Ivl)) (x : Expr) : Option Step :=
  let order := ir.leafOrder walkFuel x
  (order.mapM fun v => ls.lookup v).bind fun kJs =>
    match ir.ivlWalk p f walkFuel x ((order.zip kJs).map fun vkJ => (.leaf vkJ.1, vkJ.2.2)) with
    | some (J, []) => some (.ivlExpr (kJs.map (·.1)) x J.lo J.hi)
    | _ => none

/-- **The steps bounding the distinct leaves of `xs`** from fact index `base` on, and each leaf's
fact index and interval. -/
def boundLeaves (p base : ℕ) (xs : List Expr) :
    Option (List Step × List (ℕ × ℕ × Ivl)) :=
  let vs := (xs.flatMap (ir.leafOrder walkFuel)).eraseDups
  (ir.leavesChain p base vs).map fun ⟨ss, ks, ls⟩ =>
    (ss, (vs.zip (ks.zip (ls.map (·.2)))))

/-- **The derivation of a `mod_0` in the integer form.** -/
def mod0Deriv (pid d : ℕ) (e e' : Expr) : Option (List Step) :=
  let p := ir.charOf (ir.domainField d)
  (ir.boundLeaves p 1 [e, e']).bind fun ⟨ss, ls⟩ =>
    let a := 1 + ss.length
    match ir.ivlExprStep p (ir.domainField d) ls e, ir.ivlExprStep p (ir.domainField d) ls e' with
    | some s₁, some s₂ => some ([.realized pid] ++ ss ++ [s₁, s₂, .lift 0 a (a + 1), .conclude (a + 2)])
    | _, _ => none

/-- **The derivation of a one-digit `mod_q`**: `e − e' = q · Q + C` by unfolding the quotient and
a linear combination, `C` a constant holding `q · qlo` modulo `p`; the quotient's range by its
lookup; the interval of `e − e'`; the lift to a multiple of `q`. -/
def oneDigitDeriv (d q : ℕ) (e e' : Expr) (real : ModRealization) : Option (List Step) :=
  let p := ir.charOf (ir.domainField d)
  let Qe := real.quotExpr
  let dX := Expr.sub e e'
  let c0 := ((q : ℤ) * real.quotientLo % (p : ℤ)).toNat
  let Yo : Option Expr :=
    if c0 = 0 then some (.scale (.const q) Qe)
    else ((List.range ir.values.length).find? fun u =>
      ir.constAll u c0 (ir.exprLen e) (ir.domainField d)).map fun u =>
        .add (.scale (.const q) Qe) (.leaf u)
  Yo.bind fun Yq => (ir.lookupFor Qe).bind fun ⟨msQ, _⟩ =>
    (ir.boundLeaves p 4 [dX]).bind fun ⟨ss, ls⟩ =>
      let a := 4 + ss.length
      (ir.ivlExprStep p (ir.domainField d) ls dX).map fun s =>
        [.subst Qe (ir.deref Qe), .linear [(0, -(q : ℤ))] dX Yq, .lookup msQ, .rangeNat 2] ++ ss ++
          [s, .lift 1 a 3, .congr (a + 1)]

/-- **The steps bounding the digits `us` below `T`**, from fact index `base` on: a lookup and a
range per digit; the digits' `nat` fact indices. -/
def digitChain (base : ℕ) : List ℕ → Option (List Step × List ℕ)
  | [] => some ([], [])
  | u :: us =>
    (ir.lookupFor (.leaf u)).bind fun ⟨ms, _⟩ =>
      (digitChain (base + 2) us).map fun ⟨ss, ks⟩ =>
        ([.lookup ms, .rangeNat base] ++ ss, (base + 1) :: ks)

/-- **The field `equal` mentioning the leaf `u`**, other than `v`'s: a reconstruction or top row. -/
def rowWith (u : ℕ) : Option ℕ :=
  (List.range ir.predicates.length).find? fun q =>
    match (ir.predicate q).body with
    | .equal _ L _ _ => (ir.nodesOf L).contains u
    | _ => false

/-- **The steps turning a row `q` into `x = y`** from fact index `base` on: `realized q`, one
`subst` per shared expression among the row's linear terms, and a `linear` combining them (each
shared expression's coefficient cancelled). Returns the steps and the `eq` fact's index. -/
def rowEq (d base q : ℕ) (x y : Expr) : Option (List Step × ℕ) :=
  match (ir.predicate q).body with
  | .equal _ L _ _ =>
    let p := ir.charOf (ir.domainField d)
    (ir.linForm (ir.domainField d) (ir.exprLen x) L).map fun lf =>
      let refs := (lf.2.filter fun t => match t.2 with | .ref _ => true | _ => false)
      let ss := refs.map fun t => Step.subst t.2 (ir.deref t.2)
      let cs := (refs.zipIdx.map fun ti =>
        (base + 1 + ti.2, if ti.1.1 % (p : ℤ) = 1 then (-1 : ℤ) else 1))
      ([.realized q] ++ ss ++ [.linear ((base, 1) :: cs) x y], base + 1 + refs.length)
  | _ => none

/-- **The derivation of a digit `in`** `x ∈ [0, N)`: the digits' lookups, the reconstruction row
to `x = Σ T^j d_j`, `digits`. Returns the steps and the `nat` fact's index. -/
def digitsPart (d base T : ℕ) (x : Expr) (us : List ℕ) : Option (List Step × ℕ) :=
  match us with
  | [] => none
  | u :: rest =>
    (ir.digitChain base us).bind fun ⟨ds, ks⟩ =>
      (ir.rowWith u).bind fun q =>
        (ir.rowEq d (base + ds.length) q x (digitExpr T (.leaf u) (rest.map .leaf))).map
          fun ⟨rs, k⟩ => (ds ++ rs ++ [.digits k ks T], base + ds.length + rs.length)

/-- **The derivation of a lookup `in`** of predicate `pid` by its realization's kind. -/
def inDeriv (d : ℕ) (x : Expr) (r : LookupRealization) : Option (List Step) :=
  let p := ir.charOf (ir.domainField d)
  match r.kind with
  | .direct => (ir.lookupFor x).map fun ⟨ms, _⟩ => [.lookup ms, .rangeNat 0, .conclude 1]
  | .digits => (ir.digitsPart d 0 r.base x r.digitValues).map fun ⟨ss, k⟩ => ss ++ [.conclude k]
  | .twoSided =>
    (ir.digitsPart d 0 r.base x r.digitValues).bind fun ⟨ss₁, k₁⟩ =>
      match r.second with
      | [] => none
      | h :: _ =>
        (ir.rowWith h).bind fun q =>
          match (ir.predicate q).body with
          | .equal _ L _ _ =>
            ((ir.nodesOf L).find? fun u => match (ir.value u).kind with
              | .constant _ => true | _ => false).bind fun top =>
              let Xt := Expr.sub (.leaf top) x
              (ir.digitsPart d (ss₁.length) r.base Xt r.second).map fun ⟨ss₂, k₂⟩ =>
                ss₁ ++ ss₂ ++ [.natComp k₁ k₂, .conclude (ss₁.length + ss₂.length)]
          | _ => none
  | .complement =>
    let ne := r.needles.headD default
    (ir.lookupFor ne).bind fun ⟨ms, _⟩ =>
      (ir.boundLeaves p 4 [x]).bind fun ⟨sl, ls⟩ =>
        (ir.ivlExprStep p (ir.domainField d) ls x).map fun st =>
          let a := 4 + sl.length
          [.lookup ms, .rangeNat 0, .subst ne (ir.deref ne), .transport 2 1] ++ sl ++
            [st, .natIvl a, .natComp (a + 1) 3, .conclude (a + 2)]
  | _ => none

/-- **The prototype derivation of predicate `pid`** (`[]`, which fails, outside the lowerings it
covers). -/
def protoDeriv (pid : ℕ) (body : PredBody) : List Step :=
  ((match body with
  | .equal _ _ _ _ => some [Step.realized pid, Step.conclude 0]
  | .mem d [x] (.range _) (.lookup r) => ir.inDeriv d x r
  | .mem _ [x] _ (.lookup r) =>
    let ms := ir.membersFor r.table x
    if r.kind = LookupKind.direct ∧ ms ≠ [] then some [.lookup ms, .conclude 0] else none
  | .mod d q e e' real =>
    if q = 0 then ir.mod0Deriv pid d e e'
    else if real.form = ModForm.oneDigit then ir.oneDigitDeriv d q e e' real else none
  | .cross _ _ _ _ _ _ => some [.mac [] none []]
  | _ => none : Option (List Step)).getD [])

/-- **The prototype derivations** of every predicate. -/
def protoDerivs : List (List Step) :=
  (ir.predicates.zipIdx).map fun pi => ir.protoDeriv pi.2 pi.1.body

/-- **The prototype certificate**: the derivations, cross-field `equal`s ranked above every other
predicate, no shared facts. -/
def protoCert : Derivations :=
  { derivs := ir.protoDerivs.zipIdx.map fun sk => (sk.2, sk.1), ranks := ir.predicates.map fun pr => if derivCrossB pr.body then 1 else 0 }

end Proto


end GordieHowe.RealizedProgram
