-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.Realizations.Realized
public import GordieHoweNative.Language.RealizedProgram.Interval
public import GordieHoweNative.Language.RealizedProgram.StructureCheck

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.RealizedProgram.RealizationValid`

The definitions of `GordieHowe.Language.RealizedProgram.RealizationValid` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/RealizedProgram/RealizationValid.lean`, which imports this module.
-/

local notation "ℕ" => Nat
local notation "ℤ" => Int

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export

/-- **The runs `(first, count)` tile `[pos, len)` in order**: each run starts where the previous
one ends, and the last ends at `len`. -/
def tiles : List (ℕ × ℕ) → ℕ → ℕ → Bool
  | [], pos, len => pos == len
  | fc :: rest, pos, len => fc.1 == pos && tiles rest (pos + fc.2) len

/-- **The bound `N` of a range set** `[0, N)` (`0` for a table or an expression's entries). -/
def InSet.bound : InSet → ℕ
  | .range N => N
  | .table _ => 0
  | .expr _ => 0

/-- **The key of a constant** at the characteristic `p`: its centred reading plus `p`
(`centeredZ_eq_key`), a natural, so keys are ordered as the centred readings. -/
def centeredKey (p c : ℕ) : ℕ := if 2 * c < p then c + p else c

/-- **The least and largest keys** (`centeredKey`) of `lo`, `hi` and the entries `es` at the
characteristic `p`. Each step compares the entry's key with the two bounds and passes on the bound
it chooses, so every bound the kernel reads is a literal or one key, in one pass. -/
def keyHull (p : ℕ) : ℕ → ℕ → List ℕ → ℕ × ℕ
  | lo, hi, [] => (lo, hi)
  | lo, hi, c :: es =>
    match lo.ble (centeredKey p c), (centeredKey p c).ble hi with
    | true, true => keyHull p lo hi es
    | true, false => keyHull p lo (centeredKey p c) es
    | false, _ => keyHull p (centeredKey p c) hi es

/-- **The interval of a constant of `n` coordinates** with entries `es` at the characteristic `p`:
the hull of its entries read centred, and of `0` when it has fewer than `n` entries (a coordinate
past the entries reads `0`), in one pass over the entries (`keyHull`). -/
def constIvlOf (p n : ℕ) : List ℕ → Ivl
  | [] => ⟨0, 0⟩
  | c :: es =>
    let r := keyHull p (centeredKey p c) (centeredKey p c)
      (if n ≤ es.length + 1 then es else 0 :: es)
    ⟨(r.1 : ℤ) - p, (r.2 : ℤ) - p⟩

/-- **The last term `c · u` of a sum** `rest + c · u`, `c` a constant and `u` a value. -/
def peelStep : Expr → Option (Expr × ℕ × ℕ)
  | .add rest (.scale (.const c) (.leaf u)) => some (rest, c, u)
  | _ => none

/-- **The terms `c_j · u_j` of a left-nested sum** `((h + c_0 u_0) + c_1 u_1) + …` of `n` terms,
`c_j` constants and `u_j` values: the head `h` and the terms in order. -/
def peel : ℕ → Expr → Option (Expr × List (ℕ × ℕ))
  | 0, e => some (e, [])
  | n + 1, e =>
    (peelStep e).bind fun rcu => (peel n rcu.1).map fun ht => (ht.1, ht.2 ++ [(rcu.2.1, rcu.2.2)])

/-- **The terms are `−T^j · u_j`** at the characteristic `p`, from the power `pw = T^j` on: each
constant is `p − pw`, the values are `us` in order. -/
def chainOk (p T : ℕ) : ℕ → List (ℕ × ℕ) → List ℕ → Bool
  | _, [], [] => true
  | pw, (c, u) :: ts, u' :: us => u == u' && c + pw == p && 0 < pw && chainOk p T (pw * T) ts us
  | _, _, _ => false

/-- **The terms are `T^j · u_j`** below the characteristic `p`, from the power `pw = T^j` on: each
constant is `pw < p`, the values are `us` in order. -/
def posChainOk (p T : ℕ) : ℕ → List (ℕ × ℕ) → List ℕ → Bool
  | _, [], [] => true
  | pw, (c, u) :: ts, u' :: us =>
    u == u' && c == pw && decide (pw < p) && posChainOk p T (pw * T) ts us
  | _, _, _ => false

/-- **The expression `x` is the number of the digits `us` in base `T`**: `u_0 + Σ_{j ≥ 1} T^j · u_j`
as a left-nested sum (`peel`) whose head is the first digit and whose terms are `T^j · u_j`
(`posChainOk`), the constants below the characteristic `p` (`RangePolicy::bind_digit_views`,
compiler/range.h). -/
def digitsExprOk (p T : ℕ) (x : Expr) : List ℕ → Bool
  | [] => false
  | u :: us =>
    match peel us.length x with
    | some (.leaf h, ts) => h == u && posChainOk p T T ts us
    | _ => false

/-- **The quotient of a `mod_q`** (`ModRealization.quotient`; a default expression when it has
none). -/
def ModRealization.quotExpr (real : ModRealization) : Expr := real.quotient.getD default

section

variable (ir : RealizedProgram)

/-- **A read fixed before challenge `j` and other than `j`**: a challenge other than `j` drawn no
later than `j` (`ChalBefore`), a late value of a phase before `j`'s, or a pad. -/
def ReadBefore (j : ℕ) : Read → Prop
  | .chal c => c ≠ j ∧ ir.ChalBefore c j
  | .late u => (ir.value u).phase < (ir.challenge j).phase
  | .pad _ => True

instance (j : ℕ) (rd : Read) : Decidable (ir.ReadBefore j rd) := by
  cases rd <;> unfold ReadBefore <;> try unfold ChalBefore
  all_goals infer_instance

/-- **`ReadsBefore j v`**, through the reads table. -/
def readsBeforeB (j v : ℕ) : Bool := (ir.readsT.getD v []).all fun rd => decide (ir.ReadBefore j rd)

/-- **The runs of needle `n` of predicate `pid` in table `t`**: the members of the table's groups,
in group order, that are coordinates of that needle, as `(first, count)`. -/
def coverRuns (t pid n : ℕ) : List (ℕ × ℕ) :=
  ((List.range (ir.groupCountOf t)).flatMap fun g => ir.members t g).filterMap fun m =>
    if m.pred = pid ∧ m.needle = n then some (m.first, m.count) else none

/-- **Predicate `p` looks up into table `t` with a needle `n`**. -/
def LooksUp (p t n : ℕ) : Prop :=
  match lookupOf? (ir.predicate p).body with
  | some r => r.table = t ∧ n < r.needles.length
  | none => False

instance (p t n : ℕ) : Decidable (ir.LooksUp p t n) := by
  unfold LooksUp
  split <;> infer_instance

/-- **The histogram values of group `g` of table `t`**. -/
def histValues (t g : ℕ) : List ℕ :=
  (ir.groupOf t g).staticMult.toList ++ (ir.groupOf t g).lateMult.toList

/-- **Table `t` is a range** `[0, T)`. -/
def IsRange (t : ℕ) : Prop := (ir.table t).rows = .range (ir.tableSize t)

instance (t : ℕ) : Decidable (ir.IsRange t) := by
  unfold IsRange
  infer_instance

/-- **The needle `e'` is the record `e`**: the same expression, or a shared expression that is. -/
def needleMatches (e' e : Expr) : Bool :=
  e'.beq e ||
    match e' with
    | .ref k => decide (k < ir.exprs.length) && (ir.expr k).beq e
    | _ => false

/-- **One record and one needle, the needle matching the record** (`needleMatches`). -/
def singleMatch : List Expr → List Expr → Bool
  | [e], [e'] => ir.needleMatches e' e
  | _, _ => false

/-- **The set of a direct lookup into table `t`**: the range of a range table, the rows of `t`, or
the entries of the expression whose coordinates are `t`'s rows (`TableRows.expr`). -/
def DirectSet (t : ℕ) : InSet → Prop
  | .range n => n = ir.tableSize t ∧ ir.IsRange t
  | .table t' => t' = t
  | .expr e' => (ir.table t).rows = .expr e'

instance (t : ℕ) (set : InSet) : Decidable (ir.DirectSet t set) := by
  cases set <;> unfold DirectSet <;> infer_instance

/-- **The characteristic of field `f`.** -/
abbrev charOf (f : ℕ) : ℕ := (ir.field f).characteristic

/-- **Predicate `q` is the Boolean check `v · v = v` of value `v`** in a domain of `v`'s field. -/
def boolCheckOk (v q : ℕ) : Bool :=
  decide (q < ir.predicates.length) &&
    match (ir.predicate q).body with
    | .equal d (.mul (.leaf a) (.leaf b)) (.leaf c) _ =>
      a == v && b == v && c == v && decide (ir.domainField d = ir.valueField v)
    | _ => false

/-- **Value `v` is read in the prime subfield** (`primeNodes d` the prime-subfield nodes of domain
`d`): its domain exists, and it is of type `Bit` at a node or with its Boolean check
(`boolCheckOk`), or of type `Sub(E)` stored at the prime-subfield node `E`. -/
def primeRead (primeNodes : ℕ → List String) (v : ℕ) : Bool :=
  decide ((ir.value v).domain < ir.domains.length) &&
    match (ir.value v).type, (ir.value v).typeSource with
    | .bit, .node => true
    | .bit, .pred q => ir.boolCheckOk v q
    | .sub E, .node => decide (E ∈ primeNodes (ir.value v).domain)
    | _, _ => false

/-- **The bound of an `in` on value `v`** in predicate `p`: `N` for the `in` `v ∈ [0, N)` realized
by a direct or a digit lookup, with `0 < N` at most the characteristic, in a domain of `v`'s
field. -/
def rangeBoundOf (v : ℕ) (p : Predicate) : Option ℕ :=
  match p.body with
  | .mem d [.leaf u] (.range N) (.lookup r) =>
    if u = v ∧ (r.kind = .direct ∨ r.kind = .digits) ∧ 0 < N ∧ N ≤ ir.charOf (ir.valueField v) ∧
        ir.domainField d = ir.valueField v then some N else none
  | _ => none

/-- **The constant value `u` holds `c` at its first `n` coordinates**, a value of field `f`. -/
def constAll (u c n f : ℕ) : Bool :=
  match (ir.value u).kind with
  | .constant es => decide (n ≤ es.length) && es.all (· == c) && decide (ir.valueField u = f)
  | _ => false

/-- **The constant entry of value `c` at `n` coordinates** in field `f`: `k` when `c` is a constant of
field `f` holding `k` at its first `n` coordinates (`constAll`). -/
def constEntry (c n f : ℕ) : Option ℕ :=
  match (ir.value c).kind with
  | .constant (k :: _) => if ir.constAll c k n f = true ∧ k < ir.charOf f then some k else none
  | _ => none

/-- **The range of an `in` on value `v` or on `v + c`** in predicate `p`: `(c₀, N)`
for the `in` `v + c ∈ [0, N)` with `c` a constant holding `c₀` (read centred), or `(0, N)` for
`v ∈ [0, N)`, realized by a direct, digit or two-sided lookup, with `0 < N` at most the
characteristic, in a domain of `v`'s field. -/
def shiftRangeOf (v : ℕ) (p : Predicate) : Option (ℤ × ℕ) :=
  match p.body with
  | .mem d [rec] (.range N) (.lookup r) =>
    if 0 < N ∧ N ≤ ir.charOf (ir.valueField v) ∧ ir.domainField d = ir.valueField v ∧
        (r.kind = .direct ∨ r.kind = .digits ∨ r.kind = .twoSided) then
      match rec with
      | .leaf u => if u = v then some (0, N) else none
      | .add (.leaf u) (.leaf c) =>
        if u = v then
          (ir.constEntry c (ir.value v).size (ir.valueField v)).map fun k =>
            (centeredZ (ir.charOf (ir.valueField v)) k, N)
        else none
      | _ => none
    else none
  | _ => none

/-- **The interval of a centred range** `(c₀, N)` of value `v` (`shiftRangeOf`):
`v ∈ [−c₀, N − 1 − c₀]`, when both ends lie in `(−p/2, p/2)`. -/
def centredIvl (v : ℕ) (cN : ℤ × ℕ) : Option Ivl :=
  if 2 * max (-cN.1) (-(-cN.1)) < ir.charOf (ir.valueField v) ∧
      2 * max ((cN.2 : ℤ) - 1 - cN.1) (-((cN.2 : ℤ) - 1 - cN.1)) < ir.charOf (ir.valueField v)
  then some ⟨-cN.1, (cN.2 : ℤ) - 1 - cN.1⟩ else none

/-- **The interval of value `v` from the `in` of predicate `q`** read centred
(`RealizedProgram.intOf`): the `in` on `v` or `v + c` of predicate `q` (`shiftRangeOf`), with its
interval (`centredIvl`). -/
def shiftIvl (v q : ℕ) : Option Ivl :=
  if q < ir.predicates.length then
    match ir.shiftRangeOf v (ir.predicate q) with
    | some cN => ir.centredIvl v cN
    | none => none
  else none

/-- **The constant read by an expression of `n` coordinates in field `f`**: `k` for a constant leaf
holding `k` at its first `n` coordinates (`constEntry`), or a view of a constant holding `k` at
every coordinate whose first `n` entries stay inside the constant; none otherwise. -/
def constOf (n f : ℕ) : Expr → Option ℕ
  | .leaf c => ir.constEntry c n f
  | .reindex idx (.leaf c) =>
    if (List.range n).all fun i => decide (idx.entry i < (ir.value c).size) then
      ir.constEntry c (ir.value c).size f
    else none
  | _ => none

/-- **A quadratic root equation on value `v`** in predicate `pr`: the field `equal`
`(m − v)(m − (c − v)) = 0` (`v` a root of the quadratic whose roots are `m` and `c − m`, the
compiler's magnitude equations `magnitudes.s1`, `magnitudes.s2`), written
`(m + a v) · (m + a (a v + C)) = z` with `a = p − 1`, `z` a constant holding `0`, `C` a constant
expression holding `c` (`constOf`), `m` a value of `v`'s field: the value `m` and the constant
`c`. -/
def quadRootView (v : ℕ) (pr : Predicate) : Option (ℕ × ℕ) :=
  match pr.body with
  | .equal d lhs (.leaf z) _ =>
    match lhs with
    | .mul (.add (.leaf m) (.scale (.const a) (.leaf v₁)))
        (.add (.leaf m₂) (.scale (.const a₂) (.add (.scale (.const a₃) (.leaf v₂)) C))) =>
      if v₁ = v ∧ v₂ = v ∧ m₂ = m ∧ a + 1 = ir.charOf (ir.valueField v) ∧ a₂ = a ∧ a₃ = a ∧
          ir.domainField d = ir.valueField v ∧ ir.valueField m = ir.valueField v ∧
          ir.valueField z = ir.valueField v ∧ (ir.value v).size ≤ ir.exprLen lhs ∧
          ir.zeroConstB z = true then
        (ir.constOf (ir.value v).size (ir.valueField v) C).map fun c => (m, c)
      else none
    | _ => none
  | _ => none

/-- **The interval of a quadratic root** `v` with the constant `c` (`quadRootView`), its `m` with
the interval `J`: `[0, c]` when `J = [0, M]` with `M ≤ c`. -/
def quadIvl (c : ℕ) (J : Ivl) : Option Ivl :=
  if J.lo = 0 ∧ J.hi ≤ c then some ⟨0, c⟩ else none

/-- **The depth of a root product** the root-set rule follows (`rootsAt`): a product deeper than
this is not read as one. -/
def rootFuel : ℕ := 64

/-- **The value and index map of a chain of `reindex`es over a leaf**, through shared expressions
at `level` levels, with `fuel` steps: `(u, g)` when coordinate `i` of the expression is coordinate
`g i` of value `u`. -/
def leafViewAt : ℕ → ℕ → Expr → Option (ℕ × (ℕ → ℕ))
  | _, _, .leaf u => some (u, id)
  | fuel + 1, level, .reindex idx e =>
    (leafViewAt fuel level e).map fun ug => (ug.1, fun i => ug.2 (idx.entry i))
  | fuel + 1, level + 1, .ref k => leafViewAt fuel level (ir.expr k)
  | _, _, _ => none

/-- **The entries a constant expression reads** in field `f` (`leafViewAt`): `cv` when coordinate
`i` of the expression is the entry `cv i` of a constant of field `f`. -/
def constReadAt (f fuel level : ℕ) (C : Expr) : Option (ℕ → ℕ) :=
  match ir.leafViewAt fuel level C with
  | some (c, gc) =>
    match (ir.value c).kind with
    | .constant es => if ir.valueField c = f then some fun i => es.getD (gc i) 0 else none
    | _ => none
  | none => none

/-- **The roots of a factor's constant part** in field `f` at its first `L` coordinates
(`constReadAt`): `ρ` when the factor `X + C` vanishes exactly at `X = ρ i`. For `C = a C'` with
`a = p − 1` (`−C'`), the entries of `C'`; for any other constant `C`, the entries `(p − c) mod p`
of `−C`. The entries read lie below the characteristic `p`. -/
def factorRoots (f fuel level L : ℕ) (C : Expr) : Option (ℕ → ℕ) :=
  match C with
  | .scale (.const a) C' =>
    match ir.constReadAt f fuel level C' with
    | some cv => if a + 1 = ir.charOf f ∧ ∀ i < L, cv i < ir.charOf f then some cv else none
    | none => none
  | _ =>
    match ir.constReadAt f fuel level C with
    | some cv =>
      if ∀ i < L, cv i < ir.charOf f then some fun i => (ir.charOf f - cv i) % ir.charOf f
      else none
    | none => none

/-- **A root product** in field `f` at its first `L` coordinates, through shared expressions at
`level` levels, with `fuel` steps: `(u, j, r)` when coordinate `i < L` of the expression is
`κ · ∏_{ρ ∈ r i} (u_{j i} − ρ)` for a nonzero `κ`, so that it vanishes only when `u_{j i}` is one of
the roots `r i`. The factors are `X` (the root `0`) and `X + C`, `X` a chain of `reindex`es of `u`
(`leafViewAt`) and `C` a constant part (`factorRoots`); products are `mul` (of equal reads of `u`), `prod n` (of `n`
factors reading the same coordinate of `u`) and `scale` by a nonzero constant below `p`. -/
def rootsAt (f : ℕ) : ℕ → ℕ → ℕ → Expr → Option (ℕ × (ℕ → ℕ) × (ℕ → List ℕ))
  | 0, _, _, _ => none
  | fuel + 1, level, L, e =>
    match e with
    | .mul a b =>
      match rootsAt f fuel level L a with
      | some (u, g, r) =>
        match rootsAt f fuel level L b with
        | some (u', g', r') =>
          if u = u' ∧ ∀ i < L, g i = g' i then some (u, g, fun i => r i ++ r' i) else none
        | none => none
      | none => none
    | .ref k =>
      match level with
      | 0 => none
      | level + 1 => rootsAt f fuel level L (ir.expr k)
    | .scale (.const s) a =>
      if 0 < s ∧ s < ir.charOf f then rootsAt f fuel level L a else none
    | .prod n a =>
      match rootsAt f fuel level (L * n) a with
      | some (u, g, r) =>
        if ∀ i < L, ∀ t < n, g (i * n + t) = g (i * n) then
          some (u, fun i => g (i * n), fun i => (List.range n).flatMap fun t => r (i * n + t))
        else none
      | none => none
    | .add X C =>
      match ir.leafViewAt fuel level X, ir.factorRoots f fuel level L C with
      | some (u, g), some ρ => some (u, g, fun i => [ρ i])
      | _, _ => none
    | X => (ir.leafViewAt fuel level X).map fun ug => (ug.1, ug.2, fun _ => [0])

/-- **A root-set equation on value `v`** in predicate `pr`: the field `equal` `P = z` with `z` a
constant holding `0` and `P` a root product on `v` in `v`'s field at the equation's coordinates
(`rootsAt`; first read at no coordinates, so that the equation's length is computed only for a
root product on `v`), whose roots lie below the characteristic: the coordinates `j i` of `v` it reads, its
number `L` of coordinates, and the interval `[min, max]` of its roots. -/
def rootSetView (v : ℕ) (pr : Predicate) : Option ((ℕ → ℕ) × ℕ × Ivl) :=
  match pr.body with
  | .equal d lhs (.leaf z) _ =>
    if (ir.rootsAt (ir.domainField d) rootFuel ir.exprs.length 0 lhs).map (·.1) = some v ∧
        ir.zeroConstB z = true then
      let L := ir.exprLen lhs
      match ir.rootsAt (ir.domainField d) rootFuel ir.exprs.length L lhs with
      | some (u, j, r) =>
        let rs := (List.range L).flatMap r
        let lo := rs.foldl min (rs.headD 0)
        let hi := rs.foldl max 0
        if u = v ∧ ir.domainField d = ir.valueField v ∧ ir.valueField z = ir.valueField v ∧
            ∀ i < L, ∀ ρ ∈ r i, lo ≤ ρ ∧ ρ ≤ hi ∧ ρ < ir.charOf (ir.valueField v) then
          some (j, L, ⟨lo, hi⟩)
        else none
      | none => none
    else none
  | _ => none

/-- **Predicate `pr` is a root equation on value `v`**: a quadratic root equation (`quadRootView`)
or a root-set equation (`rootSetView`) on it. The values' intervals read only these equations'
facts (`RealizedProgram.IvlFacts.roots`). -/
def rootEqB (v : ℕ) (pr : Predicate) : Bool :=
  (ir.quadRootView v pr).isSome || (ir.rootSetView v pr).isSome

/-- **The interval of value `v` from the root-set equations `ws`** (`rootSetView`): when they
together read every coordinate of `v`, the interval `[lo, hi]` holding every one of their
intervals. -/
def rootSetHull (v : ℕ) (ws : List ((ℕ → ℕ) × ℕ × Ivl)) : Option Ivl :=
  let lo := (ws.map fun w => w.2.2.lo).foldl min ((ws.map fun w => w.2.2.lo).headD 0)
  let hi := (ws.map fun w => w.2.2.hi).foldl max ((ws.map fun w => w.2.2.hi).headD 0)
  if (∀ c < (ir.value v).size, ∃ w ∈ ws, ∃ i < w.2.1, w.1 i = c) ∧
      ∀ w ∈ ws, lo ≤ w.2.2.lo ∧ w.2.2.hi ≤ hi then
    some ⟨lo, hi⟩
  else none

-- `IvlSource` and `IvlSource.allows` are in `GordieHowe/Language/RealizedProgram/IvlSource.lean`.

/-- **The interval of entry `k` of the value ranges `sr`** for value `v` of field `f`: `[0, N − 1]`
for the entry `(v, N)` with `0 < N` at most the characteristic. -/
def declaredIvl (sr : List (ℕ × ℕ)) (f v k : ℕ) : Option Ivl :=
  match sr[k]? with
  | some (u, N) => if u = v ∧ 0 < N ∧ N ≤ ir.charOf f then some ⟨0, (N : ℤ) - 1⟩ else none
  | none => none

/-- **The interval of value `v` from the `in` of predicate `q`** (`rangeBoundOf`): `[0, N − 1]`. -/
def rangeIvl (v q : ℕ) : Option Ivl :=
  if q < ir.predicates.length then
    (ir.rangeBoundOf v (ir.predicate q)).map fun N : ℕ => ⟨0, (N : ℤ) - 1⟩
  else none

/-- **The interval of a prime-subfield read** `v` of field `f` (`primeRead`): `[0, 1]` for `Bit`,
else `[0, p − 1]`. -/
def primeIvl (primeNodes : ℕ → List String) (f v : ℕ) : Option Ivl :=
  if ir.primeRead primeNodes v then
    some (if (ir.value v).type = .bit then ⟨0, 1⟩ else ⟨0, (ir.charOf f : ℤ) - 1⟩)
  else none

/-- **The interval of value `v` from the quadratic root equation of predicate `q`**
(`quadRootView`), its `m` with the interval of the `in` of predicate `r` (`shiftIvl`): `quadIvl`. -/
def quadRootIvl (v q r : ℕ) : Option Ivl :=
  if q < ir.predicates.length then
    match ir.quadRootView v (ir.predicate q) with
    | some (m, c) =>
      match ir.shiftIvl m r with
      | some J => quadIvl c J
      | none => none
    | none => none
  else none

/-- **The root-set equations on value `v` of the predicates `qs`** (`rootSetView`). -/
def rootSetViews (v : ℕ) (qs : List ℕ) : List ((ℕ → ℕ) × ℕ × Ivl) :=
  qs.filterMap fun q => if q < ir.predicates.length then ir.rootSetView v (ir.predicate q) else none

/-- **The interval of value `v` from the root-set equations of the predicates `qs`**
(`rootSetViews`, `rootSetHull`). -/
def rootSetIvlAt (v : ℕ) (qs : List ℕ) : Option Ivl := ir.rootSetHull v (ir.rootSetViews v qs)

/-- **The interval rule `s` at value `v` of field `f`** at the value ranges `sr`, checked locally
(`primeNodes d` the prime-subfield nodes of domain `d`): see `IvlSource`. -/
def ruleIvl (primeNodes : ℕ → List String) (sr : List (ℕ × ℕ)) (f v : ℕ) : IvlSource → Option Ivl
  | .const =>
    match (ir.value v).kind with
    | .constant es =>
      if es.all (· < ir.charOf f) then some (constIvlOf (ir.charOf f) (ir.value v).size es)
      else none
    | _ => none
  | .opaqueBit => if (ir.value v).type = .bit then some ⟨0, 1⟩ else none
  | .declared k => ir.declaredIvl sr f v k
  | .shiftRange q => ir.shiftIvl v q
  | .range q => ir.rangeIvl v q
  | .quadRoot q r => ir.quadRootIvl v q r
  | .rootSet qs => ir.rootSetIvlAt v qs
  | .prime => ir.primeIvl primeNodes f v

/-- **The interval source `s` justifies an interval of value `v`'s coordinates read in field `f`**
at the value ranges `sr`: under its guards (a value of the program and of field `f`, of
characteristic above `2`), a source the value's kind takes (`IvlSource.allows`), and its rule
(`ruleIvl`). -/
def ivlAt (primeNodes : ℕ → List String) (sr : List (ℕ × ℕ)) (f v : ℕ) (s : IvlSource) :
    Option Ivl :=
  if v < ir.values.length ∧ ir.valueField v = f ∧ f < ir.fields.length ∧ 2 < ir.charOf f ∧
      s.allows (ir.value v).kind = true then
    ir.ruleIvl primeNodes sr f v s
  else none

/-- **The interval of an expression of field `f`** at the values' intervals `L`
(`RealizedProgram.ivlOf`). -/
def exprIvl (L : ℕ → ℕ → Option Ivl) (f : ℕ) (e : Expr) : Option Ivl :=
  ir.ivlOf (ir.charOf f) (L f) e

/-- **The interval sources of the structure records `S`**, as a trie keyed by value, built once
per checker. -/
def _root_.GordieHowe.RealizedProgram.Structure.ivlTrie (S : Structure) : NatTrie IvlSource :=
  NatTrie.ofList S.ivlSources

/-- **The values' intervals at the exported sources** `T` (`Structure.ivlTrie`), read at the value
ranges `sr`: value `v`'s interval read in field `f` is its source's rule (`ivlAt`), none for a value
without a source. -/
def ivlTab (primeNodes : ℕ → List String) (T : NatTrie IvlSource) (sr : List (ℕ × ℕ)) (f v : ℕ) :
    Option Ivl :=
  (T.get? v).bind (ir.ivlAt primeNodes sr f v)

/-- **The values' intervals the honest checks read**: the structure records' interval sources
(`ivlTab` at `Structure.ivlTrie`) at the declared statement bounds, justified by construction
(`ivlTab_justified`). -/
abbrev srcLeafIvl (primeNodes : ℕ → List String) (S : Structure) : ℕ → ℕ → Option Ivl :=
  ir.ivlTab primeNodes S.ivlTrie ir.declaredRanges

/-- **`srcLeafIvl`, the value ranges evaluated only for a declared bound**: the code compiled for
`srcLeafIvl` (`srcLeafIvl_csimp`). Compiled checkers pass `srcLeafIvl primeNodes S` on as a
function of the field and the value, and compiled code evaluates its arguments at each call:
`declaredRanges`, a pass over the values, would run once per value an interval reads. Only a
declared bound's rule reads the ranges. -/
def srcLeafIvlC (primeNodes : ℕ → List String) (S : Structure) (f v : ℕ) : Option Ivl :=
  (S.ivlTrie.get? v).bind fun
    | .declared k => ir.ivlAt primeNodes ir.declaredRanges f v (.declared k)
    | s => ir.ivlAt primeNodes [] f v s

@[csimp] theorem srcLeafIvl_csimp : @srcLeafIvl = @srcLeafIvlC := by
  funext ir primeNodes S f v
  change (S.ivlTrie.get? v).bind _ = (S.ivlTrie.get? v).bind _
  cases S.ivlTrie.get? v with
  | none => rfl
  | some s => cases s <;> rfl

/-- **One step of dereferencing**: a reference to an existing shared expression is that entry. -/
def deref : Expr → Expr
  | .ref k => if k < ir.exprs.length then ir.expr k else .ref k
  | e => e

/-- **The needle `ne` is `(N − 1) − rec`** in domain `d`: (one dereference of) `top + c · rec'` with
`c = p − 1`, `top` a constant holding `N − 1`, `rec'` matching the record `rec`
(`needleMatches`), of the record's length. -/
def complementMatch (d N : ℕ) (rec ne : Expr) : Bool :=
  decide (ir.exprLen ne = ir.exprLen rec) &&
    match ir.deref ne with
    | .add (.leaf top) (.scale (.const c) rec') =>
      decide (c + 1 = ir.charOf (ir.domainField d)) && ir.needleMatches rec' rec &&
        ir.constAll top (N - 1) (ir.exprLen rec) (ir.domainField d)
    | _ => false

/-- **The reconstruction row of a two-sided lookup** in domain `d` for the record `rec`: the field
`equal` `rec' + Σ_j (p − T^j) · d_j = z`, `rec'` matching the record (`needleMatches`), `d_j` the
digit values in order (`chainOk`), `z` a constant holding `0`. -/
def reconMatch (d : ℕ) (rec : Expr) (r : LookupRealization) : PredBody → Bool
  | .equal d' L (.leaf z) _ =>
    d' == d && ir.constAll z 0 (ir.exprLen rec) (ir.domainField d) &&
      match peel r.digits L with
      | some (h, ts) =>
        ir.needleMatches h rec && chainOk (ir.charOf (ir.domainField d)) r.base 1 ts r.digitValues
      | none => false
  | _ => false

/-- **The top row of a two-sided lookup** in domain `d` for the record `rec` and the range `[0, N)`:
the field `equal` `top + (p − 1) · rec' + Σ_j (p − T^j) · h_j = z`, `top` a constant of the
record's length holding `N − 1`, `rec'` matching the record, `h_j` the second digit set in order,
`z` a constant holding `0`. -/
def topMatch (d N : ℕ) (rec : Expr) (r : LookupRealization) : PredBody → Bool
  | .equal d' L (.leaf z) _ =>
    d' == d && ir.constAll z 0 (ir.exprLen rec) (ir.domainField d) &&
      match peel r.digits L with
      | some (.add (.leaf top) (.scale (.const c) rec'), ts) =>
        decide (c + 1 = ir.charOf (ir.domainField d)) && ir.needleMatches rec' rec &&
          chainOk (ir.charOf (ir.domainField d)) r.base 1 ts r.second &&
          ir.constAll top (N - 1) (ir.exprLen rec) (ir.domainField d) &&
          decide ((ir.value top).size = ir.exprLen rec)
      | _ => false
  | _ => false

/-- **The record `rec` is a value bound to the digits of `r`** in domain `d`: `rec` is a value `v` of
the program, of the domain's field, bound to the number of the digit values `d_j` in base `T`
(`digitsExprOk`), so it has no reconstruction row; or `rec` is `v + c` for a value `v` of the
domain's field bound to that number minus `c` (`x + (p − 1) · c`, a request on `v + c`,
`RangePolicy::bind_digit_views`, compiler/range.h). The realized assignment reads `v` through its
digits (`RealizedProgram.bindAsg`). Or `rec` is a shared expression whose entry is the digits' number (a
committed-digits quotient `d_0 + T d_1 + …`, compiler/mod.h). -/
def boundDigitsOk (d : ℕ) (rec : Expr) (r : LookupRealization) : Bool :=
  match rec with
  | .leaf v =>
    decide (v < ir.values.length) && decide (ir.valueField v = ir.domainField d) &&
      match (ir.value v).kind with
      | .bound x => digitsExprOk (ir.charOf (ir.domainField d)) r.base x r.digitValues
      | _ => false
  | .add (.leaf v) (.leaf u) =>
    decide (v < ir.values.length) && decide (ir.valueField v = ir.domainField d) &&
      match (ir.value v).kind with
      | .bound (.add x (.scale (.const c) (.leaf u'))) =>
        u' == u && decide (c + 1 = ir.charOf (ir.domainField d)) &&
          digitsExprOk (ir.charOf (ir.domainField d)) r.base x r.digitValues
      | _ => false
  | .ref k =>
    decide (k < ir.exprs.length) &&
      digitsExprOk (ir.charOf (ir.domainField d)) r.base (ir.expr k) r.digitValues
  | _ => false

/-- **A two-sided lookup** of predicate `pid` in domain `d` with records `recs` into the set `set`
`[0, N)`, `N ≤ p`: the table exists and is of the domain, of `T` rows for the base `T`; one record
`v`; the needles the `k` digit values `d_j`, then the `k` values `h_j` (`range.<r>.d<j>`,
`range.<r>.h<j>`), each of the record's length in the domain's field; `T > 1`, `2 (T^k − 1) < p` and
`p > 2`; the members of the table's groups tile every needle's coordinates. -/
structure TwoSidedOk (pid d : ℕ) (recs : List Expr) (set : InSet) (r : LookupRealization) :
    Prop where
  /-- The table exists. -/
  table : r.table < ir.tables.length
  /-- The table is of the domain. -/
  domain : d = (ir.table r.table).domain
  /-- The table is a range. -/
  rangeTable : ir.IsRange r.table
  /-- One record. -/
  single : recs.length = 1
  /-- The set is a range. -/
  range : set = .range set.bound
  /-- The range is nonempty. -/
  pos : 0 < set.bound
  /-- The base is the table's size. -/
  base : r.base = ir.tableSize r.table
  /-- The base exceeds `1`. -/
  baseGt : 1 < r.base
  /-- `k` digits in each set. -/
  digitsLen : r.digitValues.length = r.digits ∧ r.second.length = r.digits
  /-- The range lies within the characteristic. -/
  rangeLe : set.bound ≤ ir.charOf (ir.domainField d)
  /-- The needles are the digit values. -/
  needles : Expr.beqList r.needles ((r.digitValues ++ r.second).map .leaf) = true
  /-- The digit values have the record's length, in the domain's field. -/
  sizes : ∀ u ∈ r.digitValues ++ r.second,
    (ir.value u).size = ir.exprLen (recs.headD default) ∧ ir.valueField u = ir.domainField d
  /-- The characteristic exceeds `2`. -/
  char : 2 < ir.charOf (ir.domainField d)
  /-- The two digit numbers' sum stays below the characteristic. -/
  fits : 2 * (r.base ^ r.digits - 1) < ir.charOf (ir.domainField d)
  /-- The members tile every needle's coordinates. -/
  covered : ∀ n < r.needles.length,
    tiles (ir.coverRuns r.table pid n) 0 (ir.exprLen (r.needles.getD n default)) = true

theorem twoSidedOk_iff (pid d : ℕ) (recs : List Expr) (set : InSet) (r : LookupRealization) :
    ir.TwoSidedOk pid d recs set r ↔
      r.table < ir.tables.length ∧ d = (ir.table r.table).domain ∧ ir.IsRange r.table ∧
        recs.length = 1 ∧ set = .range set.bound ∧ 0 < set.bound ∧
        r.base = ir.tableSize r.table ∧ 1 < r.base ∧
        (r.digitValues.length = r.digits ∧ r.second.length = r.digits) ∧
        set.bound ≤ ir.charOf (ir.domainField d) ∧
        Expr.beqList r.needles ((r.digitValues ++ r.second).map .leaf) = true ∧
        (∀ u ∈ r.digitValues ++ r.second,
          (ir.value u).size = ir.exprLen (recs.headD default) ∧
            ir.valueField u = ir.domainField d) ∧
        2 < ir.charOf (ir.domainField d) ∧
        2 * (r.base ^ r.digits - 1) < ir.charOf (ir.domainField d) ∧
        ∀ n < r.needles.length,
          tiles (ir.coverRuns r.table pid n) 0 (ir.exprLen (r.needles.getD n default)) = true :=
  ⟨fun h => ⟨h.table, h.domain, h.rangeTable, h.single, h.range, h.pos, h.base, h.baseGt,
      h.digitsLen, h.rangeLe, h.needles, h.sizes, h.char, h.fits, h.covered⟩,
    fun ⟨h1, h2, h2', h3, h4, h5, h6, h6', h6'', h6''', h7, h8, h11, h12, h13⟩ =>
      ⟨h1, h2, h2', h3, h4, h5, h6, h6', h6'', h6''', h7, h8, h11, h12, h13⟩⟩

instance (pid d : ℕ) (recs : List Expr) (set : InSet) (r : LookupRealization) :
    Decidable (ir.TwoSidedOk pid d recs set r) :=
  decidable_of_iff _ (ir.twoSidedOk_iff pid d recs set r).symm

/-- **A digit lookup** of predicate `pid` in domain `d` with records `recs` into the set `set`
`[0, N)`: the table exists and is of the domain, of `T` rows for the base `T > 1`; one record `v`;
the needles the digit values (`range.<r>.d<j>`), each of the record's
length in the domain's field; `T^k ≤ N`; the members of the table's groups tile every needle's
coordinates. Each digit in the table makes `v` a natural below `T^k ≤ N`; the digits' number needs
no bound by the characteristic, as it is read as a natural below `T^k` before it is cast. -/
structure DigitsOk (pid d : ℕ) (recs : List Expr) (set : InSet) (r : LookupRealization) :
    Prop where
  /-- The table exists. -/
  table : r.table < ir.tables.length
  /-- The table is of the domain. -/
  domain : d = (ir.table r.table).domain
  /-- The table is a range. -/
  rangeTable : ir.IsRange r.table
  /-- One record. -/
  single : recs.length = 1
  /-- The set is a range. -/
  range : set = .range set.bound
  /-- The base is the table's size. -/
  base : r.base = ir.tableSize r.table
  /-- The base exceeds `1`. -/
  baseGt : 1 < r.base
  /-- `k` digits. -/
  digitsLen : r.digitValues.length = r.digits
  /-- The digits' numbers lie below the range's bound. -/
  le : r.base ^ r.digits ≤ set.bound
  /-- The needles are the digit values. -/
  needles : Expr.beqList r.needles (r.digitValues.map .leaf) = true
  /-- The digit values have the record's length, in the domain's field. -/
  sizes : ∀ u ∈ r.digitValues,
    (ir.value u).size = ir.exprLen (recs.headD default) ∧ ir.valueField u = ir.domainField d
  /-- The members tile every needle's coordinates. -/
  covered : ∀ n < r.needles.length,
    tiles (ir.coverRuns r.table pid n) 0 (ir.exprLen (r.needles.getD n default)) = true

theorem digitsOk_iff (pid d : ℕ) (recs : List Expr) (set : InSet) (r : LookupRealization) :
    ir.DigitsOk pid d recs set r ↔
      r.table < ir.tables.length ∧ d = (ir.table r.table).domain ∧ ir.IsRange r.table ∧
        recs.length = 1 ∧ set = .range set.bound ∧
        r.base = ir.tableSize r.table ∧ 1 < r.base ∧ r.digitValues.length = r.digits ∧
        r.base ^ r.digits ≤ set.bound ∧
        Expr.beqList r.needles (r.digitValues.map .leaf) = true ∧
        (∀ u ∈ r.digitValues,
          (ir.value u).size = ir.exprLen (recs.headD default) ∧
            ir.valueField u = ir.domainField d) ∧
        ∀ n < r.needles.length,
          tiles (ir.coverRuns r.table pid n) 0 (ir.exprLen (r.needles.getD n default)) = true :=
  ⟨fun h => ⟨h.table, h.domain, h.rangeTable, h.single, h.range, h.base, h.baseGt, h.digitsLen,
      h.le, h.needles, h.sizes, h.covered⟩,
    fun ⟨h1, h2, h2', h3, h4, h5, h6, h7, h8, h9, h10, h12⟩ =>
      ⟨h1, h2, h2', h3, h4, h5, h6, h7, h8, h9, h10, h12⟩⟩

instance (pid d : ℕ) (recs : List Expr) (set : InSet) (r : LookupRealization) :
    Decidable (ir.DigitsOk pid d recs set r) :=
  decidable_of_iff _ (ir.digitsOk_iff pid d recs set r).symm

/-- **An expression as a linear form** `c + Σ_j a_j · t_j` over the integers, read in field `f` at
its first `n` coordinates: sums, differences and constant multiples (by constants below the
characteristic) are expanded, a constant leaf holding one entry below the characteristic at its
first `n` coordinates (`constEntry`) is that constant, and any other expression is a term of
coefficient `1`; `none` where a multiple's constant reaches the characteristic. -/
def linForm (f n : ℕ) : Expr → Option (ℤ × List (ℤ × Expr))
  | .add a b => (linForm f n a).bind fun x => (linForm f n b).map fun y =>
      (x.1 + y.1, x.2 ++ y.2)
  | .sub a b => (linForm f n a).bind fun x => (linForm f n b).map fun y =>
      (x.1 - y.1, x.2 ++ y.2.map fun t => (-t.1, t.2))
  | .scale (.const k) a =>
      if k < ir.charOf f then
        (linForm f n a).map fun x => ((k : ℤ) * x.1, x.2.map fun t => ((k : ℤ) * t.1, t.2))
      else none
  | .leaf v =>
      match ir.constEntry v n f with
      | some c => some ((c : ℤ), [])
      | none => some (0, [(1, .leaf v)])
  | e => some (0, [(1, e)])

/-- **A linear form vanishes modulo `p`**: its constant is divisible by `p`, and so is the sum of
the coefficients of the terms equal to each term. -/
def linZeroB (p : ℕ) (x : ℤ × List (ℤ × Expr)) : Bool :=
  x.1 % p == 0 &&
    x.2.all fun t => ((x.2.filter fun u => u.2.beq t.2).map (·.1)).sum % p == 0

/-- **The quotient of a `mod_q` is derived from its sides** in domain `d` with characteristic `p`
(compiler/mod.h, `quotient`: `Q = q⁻¹ · (e − e' − q · qlo)`, in any arrangement of its terms): `q`
is invertible modulo `p`, and the linear form (`linForm`, at the left side's length) of
`q · Q − e + e' + q · qlo`, with `Q` the quotient (one dereference of it), vanishes modulo `p`
(`linZeroB`). Then `e − e' = q · (qlo + Q)` in the field (`RealizedProgram.fieldEq_of_quotDerived`). -/
def quotDerivedB (d q : ℕ) (e e' : Expr) (real : ModRealization) : Bool :=
  decide (q % ir.charOf (ir.domainField d) ≠ 0) &&
    match ir.linForm (ir.domainField d) (ir.exprLen e) (ir.deref real.quotExpr),
      ir.linForm (ir.domainField d) (ir.exprLen e) e,
      ir.linForm (ir.domainField d) (ir.exprLen e) e' with
    | some xQ, some x, some x' =>
      linZeroB (ir.charOf (ir.domainField d))
        ((q : ℤ) * xQ.1 - x.1 + x'.1 + q * real.quotientLo,
          xQ.2.map (fun t => ((q : ℤ) * t.1, t.2)) ++ x.2.map (fun t => (-t.1, t.2)) ++ x'.2)
    | _, _, _ => false

/-- **Predicate `rid` bounds the quotient of a `mod_q` in domain `d` without wrapping** (the left
side `e`): a direct `in` `Q' ∈ [0, N)` of domain `d` with `Q'` the quotient, of the left side's
length, `0 < N`, and `q (N − 1) + q · qlo + rhsHi − lhsLo < p` (the right half of the no-wrap
condition: `e − e' − q (qlo + Q)` lies above `−p`). -/
def quotRangeB (d q : ℕ) (e : Expr) (real : ModRealization) (rid : ℕ) : Bool :=
  decide (rid < ir.predicates.length) &&
    match (ir.predicate rid).body with
    | .mem d' [Q'] (.range N) (.lookup r) =>
      decide (d' = d) && decide (r.kind = .direct) && Q'.beq real.quotExpr &&
        decide (ir.exprLen Q' = ir.exprLen e) && decide (0 < N) &&
        decide (((q * (N - 1) : ℕ) : ℤ) + q * real.quotientLo + real.rhsHi - real.lhsLo <
          ir.charOf (ir.domainField d))
    | _ => false

/-- **The accumulator row's left side** `acc + (p − 1)·t_0 + (p − 1)·t_1 + …` for the left side
`e = t_0 + t_1 + …` (left-nested on both sides), at the characteristic `p`: its value is
`acc − e` (`RealizedProgram.evalE_of_accTerms`). -/
def accTerms (p acc : ℕ) : Expr → Expr → Bool
  | .add L (.scale (.const c) t), .add e₁ e₂ => c + 1 == p && t.beq e₂ && accTerms p acc L e₁
  | .add (.leaf a) (.scale (.const c) t), e => a == acc && c + 1 == p && t.beq e
  | _, _ => false

/-- **The shape of a quotient derived from an accumulator** (`quotDerivedAccB` without its
accumulator row): `qlo = 0` and (one dereference of) the quotient is `a · acc + b · e'` with
constants `a, b < p`, `q · a ≡ 1` and `q · b ≡ −1` modulo `p`. -/
def quotAccShapeB (d q : ℕ) (e' : Expr) (real : ModRealization) : Bool :=
  decide (real.quotientLo = 0) &&
    match ir.deref real.quotExpr with
    | .add (.scale (.const a) (.leaf _)) (.scale (.const b) e₂) =>
      e₂.beq e' && decide (a < ir.charOf (ir.domainField d)) &&
        decide (b < ir.charOf (ir.domainField d)) &&
        decide (q * a % ir.charOf (ir.domainField d) = 1) &&
        decide ((q * b + 1) % ir.charOf (ir.domainField d) = 0)
    | _ => false

/-- **The accumulator of a one-digit `mod_q`** whose quotient is derived from it
(`quotDerivedAccB`), read off the quotient (`0` when it has none). -/
def oneDigitAcc (real : ModRealization) : ℕ :=
  match ir.deref real.quotExpr with
  | .add (.scale (.const _) (.leaf acc)) (.scale (.const _) _) => acc
  | _ => 0

/-- **The top digit of a `mod_q` is derived** in domain `d` with the left side committed by `acc`
(compiler/mod.h, `digits`: `top = (q B^{k−1})⁻¹ · (acc − e' − Σ_{j<k−1} q B^j d_j)`): `qlo = 0`, the
digits are the lower digits `d_j` (values, `k − 1 ≥ 1` of them) then the top, and (one dereference
of) the top is `a · acc + b · e' + Σ_j c_j · d_j` (left-nested, `peel`) with constants below the
characteristic `p`, `P a ≡ 1`, `P b ≡ −1` and `P c_j + q B^j ≡ 0` modulo `p` for `P = q B^{k−1}`.
Then `q · Σ_j B^j d_j = acc − e'` in the field (`RealizedProgram.fieldEq_of_topDerived`). -/
def topDerivedB (d q : ℕ) (e' : Expr) (real : ModRealization) (acc : ℕ) : Bool :=
  decide (real.quotientLo = 0) &&
    match real.digits.reverse with
    | top :: lowerRev =>
      let lower := lowerRev.reverse
      let p := ir.charOf (ir.domainField d)
      let P := q * real.radix ^ lower.length
      decide (0 < lower.length) &&
      match peel lower.length (ir.deref top) with
      | some (.add (.scale (.const a) (.leaf acc')) (.scale (.const b) e₂), ts) =>
        acc' == acc && e₂.beq e' && decide (a < p) && decide (b < p) &&
          decide (P * a % p = 1) && decide ((P * b + 1) % p = 0) &&
          Expr.beqList lower (ts.map fun cu => .leaf cu.2) &&
          (ts.zipIdx.all fun cuj => decide (cuj.1.1 < p) &&
            decide ((P * cuj.1.1 + q * real.radix ^ cuj.2) % p = 0))
      | _ => false
    | [] => false

/-- **Predicate `rid` bounds digit `D` of a `mod_q` in domain `d`** (the left side `e`): a direct
`in` `D' ∈ [0, N)` of domain `d` with `D'` the digit, of the left side's length, `0 < N`; its bound
`N`. -/
def digitRangeOf (d : ℕ) (e D : Expr) (rid : ℕ) : Option ℕ :=
  if rid < ir.predicates.length then
    match (ir.predicate rid).body with
    | .mem d' [D'] (.range N) (.lookup r) =>
      if d' = d ∧ r.kind = .direct ∧ D'.beq D = true ∧ ir.exprLen D' = ir.exprLen e ∧ 0 < N then
        some N
      else none
    | _ => none
  else none

/-- **The largest quotient of digits below their bounds** `N_j` in base `B`: `Σ_j B^j (N_j − 1)`. -/
def digitsMax (B : ℕ) : List ℕ → ℕ
  | [] => 0
  | n :: N => (n - 1) + B * digitsMax B N

/-- **The accumulator of a `mod_q` in the digit form**: the value of the derived top digit's
accumulator term (`topDerivedB`), read off the top digit (`0` when it has none). -/
def digitsAcc (real : ModRealization) : ℕ :=
  match real.digits.reverse with
  | top :: lowerRev =>
    match peel lowerRev.reverse.length (ir.deref top) with
    | some (.add (.scale (.const _) (.leaf acc)) _, _) => acc
    | _ => 0
  | [] => 0

/-- **Two index maps have the same entries**, run by run, in `n` steps: empty runs are dropped; of
two head runs `(s, d, c + 1)`, `(s', d', c' + 1)` with `s = s'` (and `d = d'` past one entry), the
shorter is split off both, the remainder `(s + d k, d, …)` of the longer starting at a natural. -/
def IndexMap.sameB : ℕ → IndexMap → IndexMap → Bool
  | 0, _, _ => false
  | _ + 1, [], [] => true
  | n + 1, (_, _, 0) :: m, m' => IndexMap.sameB n m m'
  | n + 1, m, (_, _, 0) :: m' => IndexMap.sameB n m m'
  | n + 1, (s, d, c + 1) :: m, (s', d', c' + 1) :: m' =>
    s == s' && (min c c' == 0 || d == d') &&
      if c ≤ c' then
        if c = c' then IndexMap.sameB n m m'
        else decide (0 ≤ (s' : ℤ) + d' * (c + 1 : ℕ)) &&
          IndexMap.sameB n m ((((s' : ℤ) + d' * (c + 1 : ℕ)).toNat, d', c' - c) :: m')
      else decide (0 ≤ (s : ℤ) + d * (c' + 1 : ℕ)) &&
        IndexMap.sameB n ((((s : ℤ) + d * (c' + 1 : ℕ)).toNat, d, c - c') :: m) m'
  | _ + 1, _, _ => false

/-- **The runs of the MAC powers map** (`powersMap`): row `c < nch` reads `c + 1` zeros (the key)
then `nch − c − 1` ones. -/
def powersRuns (nch : ℕ) : IndexMap :=
  (List.range nch).flatMap fun c => [(0, 0, c + 1), (1, 0, nch - c - 1)]

/-- **Value `r` holds the MAC powers** `r_c = β^(c+1)`, `c < nch`, of challenge `key`
(`<mac>.powers`), in field `f`: the public expression
`prod nch (reindex idx (concat (leaf kv) (leaf one)))` with `idx` the powers map (`powersMap`,
checked run by run against `powersRuns`), `kv`
the key's value (one coordinate) and `one` a constant holding `1`, all of field `f`, the key's
field. -/
def powersB (r key nch f : ℕ) : Bool :=
  decide (r < ir.values.length) && decide (ir.valueField r = f) && decide (ir.chalField key = f) &&
    match (ir.value r).kind with
    | .pub (.expr (.prod n (.reindex idx (.concat (.leaf kv) (.leaf one))))) =>
      n == nch &&
        IndexMap.sameB (idx.length + (powersRuns nch).length + 1) idx (powersRuns nch) &&
        decide (kv < ir.values.length) &&
        decide ((ir.value kv).size = 1) && decide (ir.valueField kv = f) &&
        (match (ir.value kv).kind with
          | .challenge c => c == key
          | _ => false) &&
        ir.constAll one 1 1 f
    | _ => false

/-- **The entries `s, s + 1, …, s + n − 1`** of an index map of one run. -/
def runList (s n : ℕ) : List ℕ := (List.range n).map (s + ·)

/-- **A left side in the MAC unit form** `b + macConv(r, w, nch, taps)(y)` (compiler/mac.h, the MAC's
tail): the blind `b` (unit `0`) and the convolution's `nch` chunks (units `1, …, nch`). -/
structure MacUnits where
  /-- The blind. -/
  blind : ℕ
  /-- The powers. -/
  powers : ℕ
  /-- The chunk width. -/
  width : ℕ
  /-- The number of chunks. -/
  chunks : ℕ
  /-- The reduction taps. -/
  taps : List ℕ
  /-- The A operand. -/
  operand : Expr

/-- **The units of a left side in the MAC unit form** (`MacUnits`); `none` for any other form. -/
def macUnits? : Expr → Option MacUnits
  | .add (.leaf b) (.apply (.macConv r w nch taps) y) => some ⟨b, r, w, nch, taps, y⟩
  | _ => none

/-- **The chunk runs of a grouping**: group `(first, count)` of units covers the chunks
`[first − 1, first − 1 + count)` (unit `0` is the blind). -/
def _root_.GordieHowe.RealizedProgram.GroupedMod.chunkRuns (G : GroupedMod) : List (ℕ × ℕ) :=
  G.groups.map fun fc => (fc.1 - 1, fc.2)

/-- **Value `r` holds the powers `β^(c+1)`, `c < nch`, of some MAC key** (`powersB` at the key the
public expression reads), in a field of the program of characteristic above `1`. -/
def macPowersB (r nch : ℕ) : Bool :=
  decide (ir.valueField r < ir.fields.length) && decide (1 < ir.charOf (ir.valueField r)) &&
    match (ir.value r).kind with
    | .pub (.expr (.prod _ (.reindex _ (.concat (.leaf kv) _)))) =>
      match (ir.value kv).kind with
      | .challenge key => ir.powersB r key nch (ir.valueField r)
      | _ => false
    | _ => false

/-- **The units of a grouped left side are well formed** in domain `d`: the blind is a value of the
domain's field of `w > 0` coordinates; the operand has `nch · w` coordinates; the powers are a MAC
key's (`macPowersB`); the taps give a `convMax` (`macConvMax?`) and `2 w` is below the characteristic
(the convolution's entries, in `[0, w]`, read as themselves on the integers); no group holds the blind, and the groups' chunk runs tile
`[0, nch)` in order. -/
def macUnitsOkB (d : ℕ) (u : MacUnits) (G : GroupedMod) : Bool :=
  ir.macPowersB u.powers u.chunks &&
  decide (u.blind < ir.values.length) && decide (ir.valueField u.blind = ir.domainField d) &&
    decide ((ir.value u.blind).size = u.width) && decide (0 < u.width) &&
    decide (ir.exprLen u.operand = u.chunks * u.width) &&
    (match macConvMax? u.width u.taps with
      | some _ => decide (2 * u.width < ir.charOf (ir.domainField d))
      | none => false) &&
    G.groups.all (fun fc => decide (1 ≤ fc.1)) && tiles G.chunkRuns 0 u.chunks

/-- **Value `rg` holds the powers `r_s, …, r_{s + n − 1}`** of value `r`: a public expression
`reindex idx (leaf r)` of `r`'s field with `idx` the run `[s, s + n)`. -/
def subPowersB (rg r s n : ℕ) : Bool :=
  decide (rg < ir.values.length) && decide (r < ir.values.length) &&
    decide (ir.valueField rg = ir.valueField r) &&
    match (ir.value rg).kind with
    | .pub (.expr (.reindex idx (.leaf r'))) => r' == r && idx.toList == runList s n
    | _ => false

/-- **Predicate body `b` is the accumulator row of group `g`** (`<name>.A.g<g>`, compiler/mod.h,
`group_residues`) of a grouped `mod_q` in domain `d` with units `u`, accumulators `acc` and the
group's units `fc = (first, count)`: `acc[g w + i] + (p − 1) · macConv(rg, w, count, taps)(Y)_i = z_i`
for `i < w`, with `rg` the powers `r_{first − 1}, …` (`subPowersB`), `Y` (one dereference) the view of
the operand's chunks `[first − 1, first − 1 + count)`, `z` a constant holding `0`; the group's
convolution has `w` coordinates, well-formed shape and shared expressions, and its interval within
`[0, smax]` (the interval evaluator, `exprIvl`). -/
def groupRowB (L : ℕ → ℕ → Option Ivl) (d : ℕ) (u : MacUnits) (G : GroupedMod) (acc g : ℕ)
    (fc : ℕ × ℕ) (b : PredBody) : Bool :=
  match b with
  | .equal d' (.add (.reindex ia (.leaf acc')) (.scale (.const c)
      (.apply (.macConv rg w cnt taps) Y))) (.leaf z) _ =>
    d' == d && acc' == acc && c + 1 == ir.charOf (ir.domainField d) && w == u.width &&
      cnt == fc.2 && taps == u.taps && ia.toList == runList (g * u.width) u.width &&
      ir.subPowersB rg u.powers (fc.1 - 1) fc.2 &&
      (match ir.deref Y with
        | .reindex iy y' => y'.beq u.operand &&
          iy.toList == runList ((fc.1 - 1) * u.width) (fc.2 * u.width)
        | _ => false) &&
      ir.constAll z 0 u.width (ir.domainField d) &&
      decide (ir.exprLen (.apply (.macConv rg w cnt taps) Y) = u.width) &&
      ir.exprShapeOk (.apply (.macConv rg w cnt taps) Y) &&
      Y.refs.all (· < ir.exprs.length) &&
      decide (IvlWithin (ir.exprIvl L (ir.domainField d)
        (.apply (.macConv rg w cnt taps) Y)) 0 G.groupBound)
  | _ => false

/-- **The residues of a grouped `mod_q`** in domain `d` with units `u` and accumulators `acc`
(compiler/mod.h, `r_g = S_g − q · from_digits_T(gq_g)`): (one dereference of) the residues is
`acc + c · batched(groups · w, fromDigits(k, T))(gq)` with `c + q = p`, `T` the base below `p`,
`k` the digit count, `gq` the group digits, a value of the domain's field of `groups · w · k`
coordinates; `acc` a value of the domain's field of `groups · w` coordinates; the residues have
`groups · w` coordinates. -/
def residuesB (d q : ℕ) (u : MacUnits) (G : GroupedMod) (acc : ℕ) : Bool :=
  decide (acc < ir.values.length) && decide (ir.valueField acc = ir.domainField d) &&
    decide ((ir.value acc).size = G.groups.length * u.width) &&
    decide (ir.exprLen G.residues = G.groups.length * u.width) &&
    G.residues.refs.all (· < ir.exprs.length) &&
    match ir.deref G.residues, G.groupDigits with
    | .add (.leaf acc') (.scale (.const c) (.apply (.batched bb (.fromDigits k T)) (.leaf gq'))),
        .leaf gq =>
      acc' == acc && gq' == gq && c + q == ir.charOf (ir.domainField d) &&
        bb == G.groups.length * u.width && k == G.digitCount && T == G.base &&
        decide (T < ir.charOf (ir.domainField d)) && decide (gq < ir.values.length) &&
        decide (ir.valueField gq = ir.domainField d) &&
        decide ((ir.value gq).size = G.groups.length * u.width * G.digitCount)
    | _, _ => false

/-- **The first term `a · b` of a final sum**: the blind `b` at the coefficient `a`. -/
def finHeadB (a b : ℕ) : Expr → Bool
  | .scale (.const a') (.leaf b') => a' == a && b' == b
  | _ => false

/-- **Term `g` of a final sum** `a · R[idx_g]`: group `g`'s residues `R` at the coefficient `a`, read
through the run `[g w, g w + w)`. -/
def finTermB (a : ℕ) (R : Expr) (w g : ℕ) : Expr → Bool
  | .scale (.const a') (.reindex ia R') => a' == a && R'.beq R && ia.toList == runList (g * w) w
  | _ => false

/-- **The final sum's terms** `a · b + a · R[idx_0] + … + a · R[idx_{g−1}]` (left-nested) of a
grouped `mod_q`: the blind `b` (`finHeadB`) and the `g` groups' residues `R` (`finTermB`). -/
def finSumB (a b : ℕ) (R : Expr) (w : ℕ) : ℕ → Expr → Bool
  | 0, F => finHeadB a b F
  | g + 1, F =>
    match F with
    | .add F' t => finTermB a R w g t && finSumB a b R w g F'
    | _ => false

/-- **The coefficient of a final sum's first term** (`finSumB`). -/
def finCoef? : Expr → Option ℕ
  | .scale (.const a) _ => some a
  | .add F _ => finCoef? F
  | _ => none

/-- **The final quotient of a grouped `mod_q` is derived** in domain `d` with right side `e'` and
units `u` (compiler/mod.h, the final sum in the one-group form: `Q = q⁻¹ · (fin − e')` with
`fin = b + Σ_g r_g`): `qlo = 0` and (one dereference of) the quotient is `F + c · e'` with `F` the
final sum's terms at a coefficient `a` (`finSumB`), `a, c < p`, `q a ≡ 1` and `q c ≡ −1` modulo
`p`. -/
def finalQuotB (d q : ℕ) (e' : Expr) (u : MacUnits) (G : GroupedMod) (real : ModRealization) :
    Bool :=
  decide (real.quotientLo = 0) &&
    match ir.deref real.quotExpr with
    | .add F (.scale (.const c) e₂) =>
      match finCoef? F with
      | some a =>
        finSumB a u.blind G.residues u.width G.groups.length F && e₂.beq e' &&
          decide (a < ir.charOf (ir.domainField d)) && decide (c < ir.charOf (ir.domainField d)) &&
          decide (q * a % ir.charOf (ir.domainField d) = 1) &&
          decide ((q * c + 1) % ir.charOf (ir.domainField d) = 0)
      | none => false
    | _ => false

/-- **The core of a grouped `mod_q`'s shape** (`groupedShapeB` without its accumulator rows): the
left side in the MAC unit form with well-formed units (`macUnitsOkB`), accumulators `acc`, the
residues (`residuesB`) and the final quotient derived from the final sum and the right side
(`finalQuotB`). -/
def groupedCoreB (d q : ℕ) (e e' : Expr) (real : ModRealization) : Bool :=
  match real.grouped, macUnits? e with
  | some G, some u =>
    match G.accumulators with
    | some (.leaf acc) =>
      ir.macUnitsOkB d u G && ir.residuesB d q u G acc && ir.finalQuotB d q e' u G real
    | _ => false
  | _, _ => false

/-- **The final quotient of a `mod_q` with left side `e` is bounded by a direct `in`** of the left
side's length (`digitRangeOf`), the first of its exported ranges (the compiler lists the quotient's
range first). -/
def groupedQuotRangeB (d : ℕ) (e : Expr) (real : ModRealization) : Bool :=
  (ir.digitRangeOf d e real.quotExpr (real.ranges.headD ir.predicates.length)).isSome

/-- **The largest quotient of `k` digits below `N` in base `T`**: `Σ_{j<k} T^j (N − 1)`
(`digitsMax`). -/
def groupQuotMax (T k N : ℕ) : ℕ := digitsMax T (List.replicate k N)

/-- **Predicate body `b` is the field equation of a `mod_p`** in domain `d` with sides `e`, `e'`
(compiler/mod.h, `m = p`: `assert_zero(lhs − rhs)`): `e + (p − 1) · e' = z` in domain `d`, `z` a
constant holding `0` at `e`'s coordinates. -/
def fieldRowB (d : ℕ) (e e' : Expr) (b : PredBody) : Bool :=
  match b with
  | .equal d' (.add e₁ (.scale (.const c) e₂)) (.leaf z) _ =>
    d' == d && e₁.beq e && e₂.beq e' && c + 1 == ir.charOf (ir.domainField d) &&
      ir.constAll z 0 (ir.exprLen e) (ir.domainField d)
  | _ => false

section FieldRow

open GordieHowe.Twin

/-- **Predicate `r` is the field row of the field-form `mod_q` `m`, at the pointer**, as a check
whose failure names `m` (slot `1`, the row): `r` is a predicate of the program, of role
`realization m`, and its body is the field equation `e + (p − 1) e' = z` of `m`'s sides
(`fieldRowB`). -/
def fieldRowAtE (m r : ℕ) : Except StructFailure Unit :=
  seqE (guardE (decide (r < ir.predicates.length)) ⟨m, 1, .badPointer⟩) <|
    seqE (guardE ((ir.predicate r).role == .realization m) ⟨m, 1, .roleMismatch⟩) <|
      guardE (match (ir.predicate m).body with
        | .mod d _ e e' real => real.form == .field && ir.fieldRowB d e e' (ir.predicate r).body
        | _ => false) ⟨m, 1, .slotMismatch⟩

/-- **The row the structure records name for the field-form `mod_q` `m`**: the `modField` record
whose first predicate is `m` (`Structure.gadgetAt`), `preds = [m, r]`; the failure names `m`. -/
def fieldRowRecE (S : Structure) (m : ℕ) : Except StructFailure ℕ :=
  match S.gadgetAt.get? m with
  | none => .error ⟨m, 0, .noRecord⟩
  | some i =>
    match S.gadgets[i]? with
    | none => .error ⟨m, 0, .noRecord⟩
    | some g =>
      if g.kind = .modField then
        match g.preds with
        | [_, r] => .ok r
        | _ => .error ⟨m, 0, .slotMismatch⟩
      else .error ⟨m, 0, .wrongKind⟩

/-- **The field row of the field-form `mod_q` `m` at the structure records' pointer**
(`fieldRowRecE`, then `fieldRowAtE`). -/
def fieldRowPtrE (S : Structure) (m : ℕ) : Except StructFailure Unit :=
  thenE (fieldRowRecE S m) (ir.fieldRowAtE m)

end FieldRow

/-- **One term `c · D` of a left-nested sum** `rest + c · D`: `(rest, c, D)`. -/
def peelTerm : Expr → Option (Expr × ℕ × Expr)
  | .add rest (.scale (.const c) D) => some (rest, c, D)
  | _ => none

/-- **The digit terms of a committed-digits row** at the characteristic `p`, modulus `q` and radix
`R`: the left-nested sum `(…(h + c_0 · D_0) + …) + c_{k−1} · D_{k−1}` peeled from the right, the
pairs `(D_j, j)` given last first, each `c_j < p` with `c_j + q R^j ≡ 0` modulo `p` (so `c_j`
decodes to `−q R^j`); the head `h`. -/
def commPeel (p q R : ℕ) : Expr → List (Expr × ℕ) → Option Expr
  | L, [] => some L
  | L, (D', j) :: ts =>
    match peelTerm L with
    | some (rest, c, D) =>
      if D.beq D' = true ∧ c < p ∧ (c + q * R ^ j) % p = 0 then commPeel p q R rest ts else none
    | none => none

/-- **The shift of a committed-digits `mod_q`** at the characteristic `p`: `q · qlo` reduced
modulo `p`, the constant the row subtracts. -/
def commShift (p q : ℕ) (real : ModRealization) : ℕ :=
  Int.toNat (((q : ℤ) * real.quotientLo) % (p : ℤ))

/-- **`a · t` is the negation of the term `v`** at the characteristic `p`: `v = c · t` with
`a + c ≡ 0`, or `v = t` with `a = p − 1`. -/
def _root_.GordieHowe.RealizedProgram.negTermB (p : ℕ) (v : Expr) (a : ℕ) (t : Expr) : Bool :=
  match v with
  | .scale (.const c) t' => t'.beq t && decide (c < p) && decide (a < p) && (a + c) % p == 0
  | _ => v.beq t && a + 1 == p

/-- **`X` is `e − e'`** at the characteristic `p`, term by term (the compiler's rows distribute the
negated right side): `X = e + (p − 1) · e'`; or `X = Y + a · t` with `a · t` the negation of the
last term `v` of `e' = u + v` (`negTermB`) and `Y` the difference `e − u`, or of `e'` itself with
`Y = e`. -/
def _root_.GordieHowe.RealizedProgram.subB (p : ℕ) (e : Expr) : Expr → Expr → Bool
  | e', .add Y (.scale (.const a) t) =>
    (a + 1 == p && t.beq e' && Y.beq e) ||
      match e' with
      | .add u v => negTermB p v a t && subB p e u Y
      | _ => negTermB p e' a t && Y.beq e
  | _, _ => false

/-- **The head of a committed-digits row** in domain `d` for sides `e`, `e'`:
`(e − e') + (p − 1) · s` (`subB`) with `s` a constant holding `q · qlo` modulo `p`
(`commShift`) at `e`'s coordinates; or, when that shift is `0` (the compiler states none for
`qlo = 0`), `e − e'` itself (`subB`). -/
def commHeadB (d q : ℕ) (e e' : Expr) (real : ModRealization) (h : Expr) : Bool :=
  (match h with
    | .add X (.scale (.const b) (.leaf sh)) =>
      subB (ir.charOf (ir.domainField d)) e e' X &&
        b + 1 == ir.charOf (ir.domainField d) &&
        ir.constAll sh (commShift (ir.charOf (ir.domainField d)) q real) (ir.exprLen e)
          (ir.domainField d)
    | _ => false) ||
    (commShift (ir.charOf (ir.domainField d)) q real == 0 &&
      subB (ir.charOf (ir.domainField d)) e e' h)

/-- **Predicate body `b` is the field equation of a committed-digits `mod_q`** in domain `d`
(compiler/mod.h, `kCommittedDigits`: `assert_zero(lhs − rhs − q·qlo − q·Σ_j R^j d_j)`):
`e + (p − 1) · e' + (p − 1) · s + Σ_j c_j · D_j = z` (no shift term `s` when the shift is `0`)
with the digit terms of the realization's digits (`commPeel`), the head `commHeadB`, `z` a constant
holding `0` at `e`'s coordinates. -/
def commRowB (d q : ℕ) (e e' : Expr) (real : ModRealization) (b : PredBody) : Bool :=
  match b with
  | .equal d' L (.leaf z) _ =>
    d' == d && ir.constAll z 0 (ir.exprLen e) (ir.domainField d) &&
      match commPeel (ir.charOf (ir.domainField d)) q real.radix L real.digits.zipIdx.reverse with
      | some h => ir.commHeadB d q e e' real h
      | none => false
  | _ => false

/-- **Value `tb` holds the bits of the MAC target** (`<mac>.target_bits`) in domain `dy`: an opaque
value of type `Bit` of domain `dy` whose one argument is the message of the tag `tag`, of the tag's
field. -/
def targetBitsB (tb dy tag : ℕ) : Bool :=
  decide (tb < ir.values.length) && decide (ir.valueField tb = ir.domainField dy) &&
    decide ((ir.value tb).type = .bit) &&
    match (ir.value tb).kind with
    | .pub (.opaque _ [m]) =>
      decide (m < ir.values.length) && decide (ir.valueField m = ir.valueField tag) &&
        match (ir.value m).kind with
        | .message u => u == tag
        | _ => false
    | _ => false

/-- **The key of the MAC of predicate `pid`** (`<mac>.beta`): a challenge of a phase the program has,
of one coordinate, uniform in the MAC field, owned by `pid`. -/
def macKeyB (pid : ℕ) (real : MacRealization) : Bool :=
  decide (ir.IsPhaseChal real.key) && decide ((ir.challenge real.key).size = 1) &&
    decide ((ir.challenge real.key).sampler = .full) &&
    decide (ir.chalField real.key = real.macField) &&
    (ir.challenge real.key).role == .realization pid

/-- **The tag of a MAC** (`<mac>.value`): a late value of the MAC field. -/
def macTagB (real : MacRealization) : Bool :=
  decide (real.tag < ir.values.length) && decide (ir.valueField real.tag = real.macField) &&
    decide (0 < (ir.value real.tag).size) &&
    match (ir.value real.tag).kind with
    | .late => true
    | _ => false

/-- **Where coordinate `i` of the view `e` reads from**, in field `f`, with `n` levels: through
`reindex`, `concat` and shared-expression views down to `some (b, j)`, coordinate `j` of an
expression `b` that is no such view (or `e` itself past the levels); `none` where it reads `0` (a
constant holding `0` of field `f`). -/
def viewSrc (f : ℕ) : ℕ → Expr → ℕ → Option (Expr × ℕ)
  | 0, e, i => some (e, i)
  | n + 1, e, i =>
    match e with
    | .reindex idx e' => viewSrc f n e' (idx.entry i)
    | .concat a b =>
      if i < ir.exprLen a then viewSrc f n a i else viewSrc f n b (i - ir.exprLen a)
    | .leaf c =>
      match (ir.value c).kind with
      | .constant es =>
        if es.getD i 0 = 0 ∧ ir.valueField c = f ∧ i < (ir.value c).size then none else some (e, i)
      | _ => some (e, i)
    | .ref k => if k < ir.exprs.length then viewSrc f n (ir.expr k) i else some (e, i)
    | _ => some (e, i)

/-- **Two view sources agree** (`viewSrc`): both `0`, or the same coordinate of the same
expression. -/
def srcEqB : Option (Expr × ℕ) → Option (Expr × ℕ) → Bool
  | none, none => true
  | some (a, i), some (b, j) => a.beq b && i == j
  | _, _ => false

/-- **The levels a padding view is followed through.** -/
def padFuel : ℕ := 16

/-- **`z'` reads `z` followed by zeros to `N` coordinates** in field `f`, coordinate by coordinate (compiler/mac.h:
a MAC's operand of fewer than `chunks · width` bits is read padded to them): `z'` has `N`
coordinates and `z` at most `N`; coordinate `i < N` of `z'` reads where coordinate `i` of `z` reads
below `z`'s length and `0` past it (`viewSrc`, through `reindex`, `concat` and shared-expression views
and constants holding `0`). -/
def zeroPadWalkB (f N : ℕ) (z' z : Expr) : Bool :=
  decide (ir.exprLen z' = N) && decide (ir.exprLen z ≤ N) &&
    (List.range N).all fun i =>
      srcEqB (ir.viewSrc f padFuel z' i) (if i < ir.exprLen z then ir.viewSrc f padFuel z i else none)

/-- **`z'` is `z` padded by zeros to `N` coordinates**, as a check: `z'` is `z` itself of `N`
coordinates (one comparison of the expressions), or the coordinatewise check `zeroPadWalkB`. -/
def zeroPadB (f N : ℕ) (z' z : Expr) : Bool :=
  (z'.beq z && decide (ir.exprLen z = N)) || ir.zeroPadWalkB f N z' z

/-- **The tail of the MAC of predicate `pid`** (compiler/mac.h: `mod_2(b + macConv(r)(y), bits(T))`):
predicate `t`, of role `realization pid`, is `mod_2(b + macConv(r, w, nch, taps)(y'), tb)` in domain
`dy`, with `y'` the operand `y` padded by zeros to `nch · w` coordinates (`zeroPadB`), `b` the
blind, `w` and `nch` the MAC's width and chunks, `r` the key's powers
(`powersB`), `tb` the target's bits (`targetBitsB`); the taps give a `convMax` (`macConvMax?`) and
`2 w < p`, so the convolution's matrix entries, in `[0, w]`, read as themselves on the integers. The tail's own realization (a
`mod_q` form, checked like any other `mod_q`) gives its integer congruence; the MAC needs no bound on
the left side. -/
def macTailB (pid dy : ℕ) (y : Expr) (real : MacRealization) (t : ℕ) : Bool :=
  decide (t < ir.predicates.length) && (ir.predicate t).role == .realization pid &&
    match (ir.predicate t).body with
    | .mod d 2 (.add (.leaf b) (.apply (.macConv r w nch taps) y')) (.leaf tb) _ =>
      d == dy && some b == real.blind && w == real.width && nch == real.chunks &&
        ir.zeroPadB (ir.domainField dy) (real.chunks * real.width) y' y &&
        ir.powersB r real.key real.chunks real.macField && ir.targetBitsB tb dy real.tag &&
        match macConvMax? w taps with
        | some _ => decide (2 * w < ir.charOf (ir.domainField dy))
        | none => false
    | _ => false

/-- **The index map of the generator's powers in the H predicate**: entry `c · w + i` is `i`, for
`nch` chunks of `w`. -/
def genPowsMap (nch w : ℕ) : List ℕ := (List.range (nch * w)).map (· % w)

/-- **Value `g` holds the generator's powers** `2^i`, `i < w`, as constants of field `f` (decoded,
`2^i` is the `i`-th power of the generator in a binary field's polynomial basis,
`FieldInterp.MacFieldOk.decodePow`). -/
def genPowsB (g w f : ℕ) : Bool :=
  decide (g < ir.values.length) && decide (ir.valueField g = f) &&
    match (ir.value g).kind with
    | .constant es => es == (List.range w).map (2 ^ ·)
    | _ => false

/-- **The generator's powers read at coordinate `c w + i`, `c < nch`** (the H predicate's
weights): `reindex idx (leaf g)` with `idx` the map `c w + i ↦ i` (`genPowsMap`), or `leaf g` for
one chunk, `g` the powers (`genPowsB`). -/
def genViewB (nch w f : ℕ) : Expr → Bool
  | .reindex idx (.leaf g) => idx.toList == genPowsMap nch w && ir.genPowsB g w f
  | .leaf g => nch == 1 && ir.genPowsB g w f
  | _ => false

/-- **Predicate `p` is the H predicate `<mac>.H` of the MAC of predicate `pid`** with H operand `x`
in domain `dx` (`equal(U, Σ_c r_c · chunk_c(X_H))`, `chunk_c(X_H) = Σ_i x^i X_H[c][i]`): a predicate
of role `realization pid`, in a MAC field of characteristic `2`, with body
`U + Σ_c r_c · Σ_i X_H[c w + i] · g_i = 0` in domain `dx`, written
`equal(add(leaf U, sum nch (mul (leaf r) (sum w (mul x (reindex idx (leaf g)))))), leaf z)`: `U` the
tag, `r` the key's powers (`powersB`), `idx` the map `c w + i ↦ i` (`genPowsMap`), `g` the
generator's powers (`genPowsB`; `leaf g` itself for one chunk, `genViewB`) and `z` a constant holding
`0`; `x` is read padded by zeros to `chunks · width` coordinates (`zeroPadB`). In characteristic `2` it states the
H half (`RealizedProgram.MacHHoldsAt`). It is an ordinary affine row of its domain; its truth is a field
`equal` of the realized program. -/
def macHPredB (pid dx : ℕ) (x : Expr) (real : MacRealization) (p : ℕ) : Bool :=
  decide (p < ir.predicates.length) && (ir.predicate p).role == .realization pid &&
    decide (ir.charOf real.macField = 2) &&
    match (ir.predicate p).body with
    | .equal d (.add (.leaf u) (.apply (.sum n) (.mul (.leaf r)
        (.apply (.sum w) (.mul x' G))))) (.leaf z) _ =>
      d == dx && u == real.tag && n == real.chunks && w == real.width &&
        ir.zeroPadB (ir.domainField dx) (real.chunks * real.width) x' x &&
        ir.powersB r real.key real.chunks real.macField &&
        ir.genViewB real.chunks real.width real.macField G &&
        ir.constAll z 0 1 real.macField
    | _ => false

/-- **The H half of the MAC of predicate `pid`**: the compiler's own circuit (no `<mac>.H`
predicate, `RealizedAt.macH`), or the H predicate `<mac>.H` (`macHPredB`). -/
def macHalfB (pid dx : ℕ) (x : Expr) (real : MacRealization) : Bool :=
  match real.hPredicate with
  | none => true
  | some p => ir.macHPredB pid dx x real p

/-- **The operands of a MAC read only what is fixed before its key** (and not the key): every value
the operands `x`, `y`, the blind and the blind of the check over `x`'s field read (`ReadsBefore`).
-/
def macReadsBeforeB (x y : Expr) (real : MacRealization) : Bool :=
  (ir.nodesOf x ++ ir.nodesOf y ++ real.blind.toList ++ real.blindX.toList).all
    (ir.readsBeforeB real.key)

/-- **The blind `b` of a MAC check over a field in domain `d`** (`<mac>.blind:<D>`): a value of `d`'s field of
`width` coordinates, read as bits (interval `[0, 1]`). `macBlindB` is the blind of the check over
`y`'s field, `real.blind`. -/
def macBlindAtB (L : ℕ → ℕ → Option Ivl) (d b : ℕ) (real : MacRealization) : Bool :=
  decide (b < ir.values.length) && decide (ir.valueField b = ir.domainField d) &&
    decide ((ir.value b).size = real.width) &&
    decide (IvlWithin (ir.exprIvl L (ir.domainField d) (.leaf b)) 0 1)

/-- **The interval-free part of `macBlindAtB`**: a value of `d`'s field of `width` coordinates. -/
def macBlindCoreB (d b : ℕ) (real : MacRealization) : Bool :=
  decide (b < ir.values.length) && decide (ir.valueField b = ir.domainField d) &&
    decide ((ir.value b).size = real.width)

/-- **The tail of a MAC check over a field of odd characteristic** (compiler/mac.h, `mac_odd`:
`mod_2(b + macConv(r)(z), bits_D(T))`): predicate `t`, of role `realization pid`, is
`mod_2(b + macConv(r, w, nch, taps)(z), tb)` in domain `d`, with `b` the check's blind, `w` and
`nch` the MAC's width and chunks, `r` the key's powers (`powersB`), `tb` the target's bits in `d`
(`targetBitsB`); the taps give a `convMax` and `2 w < p`. `macTailB` is the tail of the check over
`y`'s field, with blind `real.blind`. -/
def macTailAtB (pid d : ℕ) (z : Expr) (b : ℕ) (real : MacRealization) (t : ℕ) : Bool :=
  decide (t < ir.predicates.length) && (ir.predicate t).role == .realization pid &&
    match (ir.predicate t).body with
    | .mod d' 2 (.add (.leaf b') (.apply (.macConv r w nch taps) z')) (.leaf tb) _ =>
      d' == d && b' == b && w == real.width && nch == real.chunks && z'.beq z &&
        ir.powersB r real.key real.chunks real.macField && ir.targetBitsB tb d real.tag &&
        match macConvMax? w taps with
        | some _ => decide (2 * w < ir.charOf (ir.domainField d))
        | none => false
    | _ => false

/-- **The tail of a MAC check over a field of characteristic `2`** (the paper's `sec:mac`,
Cross-field links: a field of characteristic `2` that need not contain the MAC field checks
`acc = bits(T)` entrywise): predicate `t`, of role `realization pid`, is the field `equal`
`b + macConv(r, w, nch, taps)(z) = tb` in domain `d` of characteristic `2`, with `b` the check's
blind, `r` the key's powers (`powersB`) and `tb` the target's bits in `d` (`targetBitsB`). In
characteristic `2` the field computes each accumulator entry modulo `2`. The C++ compiler does not
emit this form. -/
def macTailTwoB (pid d : ℕ) (z : Expr) (b : ℕ) (real : MacRealization) (t : ℕ) : Bool :=
  decide (t < ir.predicates.length) && (ir.predicate t).role == .realization pid &&
    decide (ir.charOf (ir.domainField d) = 2) &&
    match (ir.predicate t).body with
    | .equal d' (.add (.leaf b') (.apply (.macConv r w nch _) z')) (.leaf tb) _ =>
      d' == d && b' == b && w == real.width && nch == real.chunks && z'.beq z &&
        ir.powersB r real.key real.chunks real.macField && ir.targetBitsB tb d real.tag
    | _ => false

/-- **Value `v` is a bit in its domain** (`RealizedProgram.TypeSources`; the paper's condition that every
phase-0 `Bit` value is stored at the node of its type or has its Boolean check): a value of type
`Bit` read in the prime subfield (`primeRead`: stored at its packing-tree node `bit`, or with its
Boolean check `v · v = v`, `boolCheckOk`). -/
def bitLeafB (primeNodes : ℕ → List String) (v : ℕ) : Bool :=
  decide (v < ir.values.length) && decide ((ir.value v).type = .bit) && ir.primeRead primeNodes v

/-- **An expression is a view of bits** at the leaves `bl` and the shared expressions `rb`, the
shared expressions having lengths `rl`: a leaf in `bl`, a reindexing within its operand's length,
a concatenation of two views, or a shared expression in `rb`. Every coordinate of such a view below
its length is a coordinate of a leaf below its size. -/
def bitsB (bl rb : ℕ → Bool) (rl : ℕ → ℕ) : Expr → Bool
  | .leaf v => bl v
  | .reindex idx e => bitsB bl rb rl e && idx.inRange (Expr.len ir rl e)
  | .concat a b => bitsB bl rb rl a && bitsB bl rb rl b
  | .ref k => rb k
  | _ => false

/-- **The shared expressions that are views of bits** at the leaves `bl`, with `n` levels
(`0`: none). -/
def refBitsT (bl : ℕ → Bool) : ℕ → ℕ → Bool
  | 0, _ => false
  | n + 1, k => decide (k < ir.exprs.length) &&
      ir.bitsB bl (refBitsT bl n) (ir.refLen ir.exprs.length) (ir.expr k)

/-- **An expression reads bits** (in any characteristic): a view of bits (`bitsB`) whose leaves are
bits of their domains (`bitLeafB`), through the shared expressions at the program's depth. The
compiler's MAC operands (the joined copies of the shared bits, `<mac>.xa`, `<mac>.xb`) are such
views. -/
def exprBitsB (primeNodes : ℕ → List String) (e : Expr) : Bool :=
  ir.bitsB (ir.bitLeafB primeNodes) (ir.refBitsT (ir.bitLeafB primeNodes) ir.exprs.length)
    (ir.refLen ir.exprs.length) e

/-- **`MacOddFieldOk` with its tail at predicate `t`**, as a check. -/
def macOddFieldAtB (L : ℕ → ℕ → Option Ivl) (pid d : ℕ) (z : Expr) (b : ℕ)
    (real : MacRealization) (t : ℕ) : Bool :=
  decide (2 < ir.charOf (ir.domainField d)) && ir.macBlindAtB L d b real &&
    decide (IvlWithin (ir.exprIvl L (ir.domainField d) z) 0 1) && ir.macTailAtB pid d z b real t

/-- **`MacTwoFieldOk` with its tail at predicate `t`**, as a check. -/
def macTwoFieldAtB (primeNodes : ℕ → List String) (pid d : ℕ) (z : Expr) (b : ℕ)
    (real : MacRealization) (t : ℕ) : Bool :=
  decide (ir.valueField b = ir.domainField d) && decide ((ir.value b).size = real.width) &&
    ir.exprBitsB primeNodes z && ir.macTailTwoB pid d z b real t

/-- **`MemberOk t m`**, through the tables. -/
def memberOkB (t : ℕ) (m : Member) : Bool :=
  decide (m.pred < ir.predicates.length) && decide (ir.LooksUp m.pred t m.needle) &&
    (ir.needleExpr m.pred m.needle).refs.all (· < ir.exprs.length) &&
    (ir.nodesOf (ir.needleExpr m.pred m.needle)).all (ir.readsBeforeB (ir.alphaOf t))

/-- **`GroupOk t g`**, through the tables. -/
def groupOkB (t g : ℕ) : Bool :=
  (ir.members t g).all (ir.memberOkB t) &&
    decide (ir.groupCount t g < (ir.field (ir.chalField (ir.alphaOf t))).characteristic) &&
    (ir.histValues t g).all (ir.readsBeforeB (ir.alphaOf t))

/-- **`RowsOk t rows`**, through the tables. -/
def rowsOkB (t : ℕ) : TableRows → Bool
  | .range T => decide (T ≤ ir.tmaxOf (ir.alphaOf t))
  | .columns cols => !cols.isEmpty && ir.readsBeforeB (ir.alphaOf t) (cols.headD 0)
  | .expr e' => e'.refs.all (· < ir.exprs.length) && (ir.nodesOf e').all (ir.readsBeforeB (ir.alphaOf t))

/-- **`TableOk t`**, through the tables. -/
def tableOkB (t : ℕ) : Bool :=
  ir.rowsOkB t (ir.table t).rows && decide (ir.IsPhaseChal (ir.alphaOf t)) &&
    decide ((ir.challenge (ir.alphaOf t)).size = 1) &&
    decide ((ir.challenge (ir.alphaOf t)).sampler =
      .fieldMinusTables (.range (ir.tmaxOf (ir.alphaOf t)))) &&
    decide (ir.chalField (ir.alphaOf t) < ir.fields.length) &&
    decide (ir.chalField (ir.alphaOf t) = ir.domainField (ir.table t).domain) &&
    decide (ir.tmaxOf (ir.alphaOf t) < (ir.field (ir.chalField (ir.alphaOf t))).characteristic) &&
    (List.range (ir.groupCountOf t)).all (ir.groupOkB t)

/-- **`DirectOk pid d recs set r`**, through the tables. -/
def directOkB (pid d : ℕ) (recs : List Expr) (set : InSet)
    (r : LookupRealization) : Bool :=
  decide (r.table < ir.tables.length) && decide (d = (ir.table r.table).domain) &&
    decide (ir.DirectSet r.table set) &&
    ir.singleMatch recs r.needles &&
    r.needles.all (fun e => e.refs.all (· < ir.exprs.length)) &&
    (List.range r.needles.length).all fun n =>
      tiles (ir.coverRuns r.table pid n) 0 (ir.lenOf (r.needles.getD n default))

/-- Whether value `u` is a committed value or a constant, through the table (`isPrivOrConst`). -/
def isPrivOrConstT (u : ℕ) : Bool :=
  match (ir.valueT u).kind with
  | .priv => true
  | .constant _ => true
  | _ => false

/-- **`BoundOk v`**, on value `v`, through the tables. -/
def boundOkV (x : Value) : Bool :=
  match x.kind with
  | .bound e => e.refs.all (· < ir.exprs.length) && ir.closAll Expr.directNodes ir.isPrivOrConstT e
  | _ => true

end

end GordieHowe.RealizedProgram
