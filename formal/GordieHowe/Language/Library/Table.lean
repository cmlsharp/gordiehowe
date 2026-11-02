-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Library.Eval

@[expose] public section

/-!
# GordieHowe frontend: the matchers of a public table's row selection

`lib/gordiehowe/lib/table.h` proves that a committed record is `M(row_i)` of a public table for
committed index bits `i` (`public_table`, `select_row`): one challenge `γ`, its powers
(`<table>.powers`: `γ^0, …, γ^(wmax−1)`, then `γ^off` per leaf at a nonzero offset), the rows'
digests against `Mᵀ g`, `g_c = γ^(e(c))` (`<table>.digests`), a multiplexer fold of the digests by
the index bits, and one equality `Σ_c rec_c γ^(e(c)) = fold(digests, i)`. This file holds the
data and the `Bool`/`Option` matchers the program facts are decided with; their soundness and the
selection's theorems are `GordieHowe/Language/Library/TableSelect.lean`.

* **Row maps** (`RowLeaf`, `mapWidth`, `mapWfFrom`): a map is leaves end to end, each the identity
  or the negacyclic transform of length `n` at `ψ` in natural or scheme order (`RowMap::Leaf`);
  cell `k` of a leaf has power index `perm k` (`RowLeaf.perm`: `brv(k)` in scheme order, else `k`).
* **Symbolic powers** (`powSym`, `PowCtx`, `gatherL`): the exponent of each coordinate of an
  expression of powers of `γ` (products add, concatenations append, index maps gather), through the
  shared expressions, with the exponents of some values and of one known expression given.
* **The record's digest** (`sliceOf?`, `sumTerm?`, `recTermOk`, `recTermsOk`, `addSpine`): one sum
  `Σ_k rec[off + k] γ^(off + perm k)` per leaf (`table_internal::record_digest`).
* **The fold** (`gatherIdx?`, `foldOf?`): levels `mux(b_t, d[2j+1], d[2j])` (`table_internal::fold`).
* **The digests** (`xOk`, `leafGOk`, `gMatch`, `digTermOk`, `digTermsOk`, `digSumOk`,
  `digestsOk`): `Mᵀ g` as concatenated leaf blocks and one `rowDot` per column block, padded
  (`table_internal::digest_exprs`).
* **The shape** (`TableShape`, `TableShape.okB`, `powerExps`): the identifiers of a selection and
  its checks.
-/

namespace GordieHowe.RealizedProgram

open Export IOP
open scoped NNReal ENNReal

/-! ## Row maps -/

/-- **`⌊log₂ n⌋`** by recursion on a fuel (`n` itself suffices). -/
def log2S : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, n => if n < 2 then 0 else log2S fuel (n / 2) + 1

/-- **A leaf of a row map** (`RowMap::Leaf`, `lib/gordiehowe/lib/table.h`). -/
structure RowLeaf where
  /-- A negacyclic transform (else the identity). -/
  ntt : Bool
  /-- The transform's natural order (else the scheme's). -/
  natural : Bool
  /-- The leaf's number of cells. -/
  n : ℕ
  /-- The leaf's first cell. -/
  off : ℕ
  /-- The transform's root, the natural of the C++ encoding. -/
  psi : ℕ
  deriving DecidableEq, Repr

namespace RowLeaf

/-- **A transform in the scheme's order.** -/
def scheme (l : RowLeaf) : Bool := l.ntt && !l.natural

/-- **The leaf's bit count** `⌊log₂ n⌋`. -/
def lg (l : RowLeaf) : ℕ := log2S l.n l.n

/-- **The power index of cell `k`** (`RowMap::perm`). -/
def perm (l : RowLeaf) (k : ℕ) : ℕ := if l.scheme then bitRevNat l.lg k else k

/-- **The power indices of the leaf's cells.** -/
def permList (l : RowLeaf) : List ℕ := (List.range l.n).map l.perm

/-- **A well-formed leaf.** -/
def wf (l : RowLeaf) : Bool := 0 < l.n && (!l.scheme || l.n == 2 ^ l.lg)

end RowLeaf

/-- **The width of a row map.** -/
def mapWidth (m : List RowLeaf) : ℕ := (m.map (·.n)).sum

/-- **A well-formed row map from offset `o`.** -/
def mapWfFrom : ℕ → List RowLeaf → Bool
  | _, [] => true
  | o, l :: ls => l.off == o && l.wf && mapWfFrom (o + l.n) ls

/-! ## The symbolic powers -/

/-- **The entries of one run of an index map.** -/
def idxRunList (r : ℕ × ℤ × ℕ) : List ℕ :=
  (List.range r.2.2).map fun t : ℕ => ((r.1 : ℤ) + r.2.1 * t).toNat

/-- **The entries of `x` one run of an index map reads**: a slice for step `1`, a broadcast for step
`0`; `none` past the end of `x`. -/
def gatherRunL (x : List ℕ) (r : ℕ × ℤ × ℕ) : Option (List ℕ) :=
  if r.2.1 = 1 then
    if r.1 + r.2.2 ≤ x.length then some ((x.drop r.1).take r.2.2) else none
  else if r.2.1 = 0 then
    if r.2.2 = 0 then some [] else if r.1 < x.length then some (List.replicate r.2.2 (x.getD r.1 0))
    else none
  else if (idxRunList r).all (· < x.length) then some ((idxRunList r).map fun i => x.getD i 0) else none

/-- **The entries of `x` an index map reads**, run by run. -/
def gatherL (x : List ℕ) : IndexMap → Option (List ℕ)
  | [] => some []
  | r :: m =>
    match gatherRunL x r, gatherL x m with
    | some a, some b => some (a ++ b)
    | _, _ => none

/-- **What the symbolic powers read**: the exponents of values (`pub`) and of one known expression
(`known`). -/
structure PowCtx where
  /-- The values' exponents. -/
  pub : ℕ → Option (List ℕ)
  /-- An expression and its exponents. -/
  known : Option (Expr × List ℕ)

/-- **Whether `E` is the context's known expression.** -/
def PowCtx.knownOf? (c : PowCtx) (E : Expr) : Option (List ℕ) :=
  match c.known with
  | some (K, ks) => if E.beq K then some ks else none
  | none => none

variable (ir : RealizedProgram)

/-- **The exponents of an expression of powers of `γ`**, with `n` levels: coordinate `i` is
`γ^(l[i])` (`powSym_sound`). -/
def powSym (c : PowCtx) : ℕ → Expr → Option (List ℕ)
  | 0, _ => none
  | n + 1, E =>
    match c.knownOf? E with
    | some ks => some ks
    | none =>
      match E with
      | .leaf v => c.pub v
      | .mul a b =>
        match powSym c n a, powSym c n b with
        | some x, some y => if x.length = y.length then some (List.zipWith (· + ·) x y) else none
        | _, _ => none
      | .concat a b =>
        match powSym c n a, powSym c n b with
        | some x, some y => some (x ++ y)
        | _, _ => none
      | .reindex m a =>
        match powSym c n a with
        | some x => gatherL x m
        | none => none
      | .ref k => powSym c n (ir.expr k)
      | _ => none

/-- **The constant `1` and `γ`** as exponent lists. -/
def onePub (one gamma : ℕ) (v : ℕ) : Option (List ℕ) :=
  if v = one then some [0] else if v = gamma then some [1] else none

/-- **The levels of the symbolic powers.** -/
abbrev powFuel : ℕ := 64

/-! ## The record's digest -/

/-- **A slice `[s, s + c)` of `rec`.** -/
def sliceOf? (rec : Expr) : Expr → Option (ℕ × ℕ)
  | .reindex [(s, d, c)] e =>
    if d = 1 then
      if e.beq rec then some (s, c)
      else
        match sliceOf? rec e with
        | some (s', c') => if s + c ≤ c' then some (s' + s, c) else none
        | none => none
    else none
  | _ => none

/-- **A sum of products of the record's slice by powers**: `Σ_k rec[s + k] γ^(p_k)`. -/
def sumTerm? (rec : Expr) (c : PowCtx) : Expr → Option (ℕ × ℕ × List ℕ)
  | .apply (.sum n) (.mul R P) =>
    match sliceOf? rec R, ir.powSym c powFuel P with
    | some (s, w), some ps => if w = n ∧ ps.length = n then some (s, n, ps) else none
    | _, _ => none
  | _ => none

/-- **Leaf `l`'s term of the record's digest** (`table_internal::record_digest`). -/
def recTermOk (rec : Expr) (c : PowCtx) (l : RowLeaf) : Expr → Bool
  | .mul M S =>
    l.off != 0 && decide (ir.powSym c powFuel M = some [l.off]) &&
      decide (ir.sumTerm? rec c S = some (l.off, l.n, l.permList))
  | S => l.off == 0 && decide (ir.sumTerm? rec c S = some (l.off, l.n, l.permList))

/-- **The terms of a left-nested sum.** -/
def addSpine : Expr → List Expr
  | .add a b => addSpine a ++ [b]
  | e => [e]

/-- **The terms of the record's digest, one per leaf.** -/
def recTermsOk (rec : Expr) (c : PowCtx) : List RowLeaf → List Expr → Bool
  | [], [] => true
  | l :: ls, t :: ts => ir.recTermOk rec c l t && recTermsOk rec c ls ts
  | _, _ => false

/-! ## The fold -/

/-- **The coordinates of `base` a chain of index maps reads.** -/
def gatherIdx? (base : Expr) : Expr → Option (List ℕ)
  | .reindex m e =>
    if e.beq base then some m.toList
    else
      match gatherIdx? base e with
      | some l => gatherL l m
      | none => none
  | _ => none

/-- **The fold of the digests `dig` by the bits `idx`** (`table_internal::fold`), with `n` levels:
`some (t, c)` for `t` levels and `c` entries. -/
def foldOf? (idx dig nd kb : ℕ) : ℕ → Expr → Option (ℕ × ℕ)
  | 0, _ => none
  | n + 1, E =>
    match E with
    | .leaf v => if v = dig then some (0, nd) else none
    | .ref j => foldOf? idx dig nd kb n (ir.expr j)
    | .mux B (.reindex mh Xe) (.reindex ml Xe') =>
      if Xe.beq Xe' then
        match foldOf? idx dig nd kb n Xe with
        | some (t, c2) =>
          if t < kb ∧ c2 = 2 * mh.toList.length ∧
              mh.toList = (List.range mh.toList.length).map (fun i => 2 * i + 1) ∧
              ml.toList = (List.range mh.toList.length).map (fun i => 2 * i) ∧
              gatherIdx? (.leaf idx) B = some (List.replicate mh.toList.length t) then
            some (t + 1, mh.toList.length)
          else none
        | none => none
      else none
    | _ => none

/-! ## The digests -/

/-- **Leaf `l`'s column vector of `Mᵀ g`** before its multiplier: `γ^k`, or the transposed
transform of `γ^0, …, γ^(n−1)`. -/
def xOk (c : PowCtx) (l : RowLeaf) : Expr → Bool
  | .apply (.nttTranspose n psi) Ye =>
    l.ntt && n == l.n && psi == l.psi && decide (ir.powSym c powFuel Ye = some (List.range l.n))
  | .reindex m Ye =>
    !l.ntt && m.size == l.n && decide (ir.powSym c powFuel (.reindex m Ye) = some (List.range l.n))
  | _ => false

/-- **Leaf `l`'s block of `Mᵀ g`** (`table_internal::digest_exprs`). -/
def leafGOk (c : PowCtx) (l : RowLeaf) : Expr → Bool
  | .mul M Xe =>
    l.off != 0 && decide (ir.powSym c powFuel M = some (List.replicate l.n l.off)) &&
      ir.xOk c l Xe
  | E => l.off == 0 && ir.xOk c l E

/-- **`Mᵀ g`** as concatenated leaf blocks, with `n` levels: the leaves left after the
expression's. -/
def gMatch (c : PowCtx) : ℕ → List RowLeaf → Expr → Option (List RowLeaf)
  | 0, _, _ => none
  | _ + 1, [], _ => none
  | n + 1, l :: rest, E =>
    if ir.leafGOk c l E then some rest
    else
      match E with
      | .ref j => gMatch c n (l :: rest) (ir.expr j)
      | .concat a b =>
        match gMatch c n (l :: rest) a with
        | some ls' => gMatch c n ls' b
        | none => none
      | .reindex [(s, d, w)] e =>
        if s = 0 ∧ d = 1 then
          match gMatch c n (l :: rest) e with
          | some ls' => if mapWidth (l :: rest) = w + mapWidth ls' then some ls' else none
          | none => none
        else none
      | _ => none

/-- **A block's term of the digests**: `rowDot` of the block's rows against `G[o, o + w)`. -/
def digTermOk (rows o v w : ℕ) (G : Expr) : Expr → Bool
  | .apply (.rowDot M R W) (.reindex [(o', d, c)] G') =>
    M == v && R == rows && W == w && o' == o && d == 1 && c == w && G'.beq G
  | _ => false

/-- **The terms of the digests, one per column block, from offset `o`.** -/
def digTermsOk (rows : ℕ) (G : Expr) : ℕ → List (ℕ × ℕ) → List Expr → Bool
  | _, [], [] => true
  | o, (v, w) :: ps, t :: ts => digTermOk rows o v w G t && digTermsOk rows G (o + w) ps ts
  | _, _, _ => false

/-- **The `Mᵀ g` the first term reads.** -/
def digG : List Expr → Expr
  | .apply _ (.reindex _ G) :: _ => G
  | _ => .leaf 0

/-- **The levels of the digests' matcher.** -/
abbrev gFuel : ℕ := 64

/-- **The digests' sum of block terms.** -/
def digSumOk (c : PowCtx) (m : List RowLeaf) (parts : List (ℕ × ℕ)) (rows : ℕ) (S : Expr) :
    Bool :=
  digTermsOk rows (digG (addSpine S)) 0 parts (addSpine S) &&
    decide (ir.gMatch c gFuel m (digG (addSpine S)) = some [])

/-- **The digests** (`<table>.digests`), padded from `rows` to `nd` rows. -/
def digestsOk (c : PowCtx) (m : List RowLeaf) (parts : List (ℕ × ℕ)) (rows nd : ℕ) :
    Expr → Bool
  | .reindex pm S =>
    rows < nd && nd - rows ≤ rows && decide (pm = [(0, 1, rows), (0, 1, nd - rows)]) &&
      ir.digSumOk c m parts rows S
  | S => nd == rows && ir.digSumOk c m parts rows S

/-! ## The table's selection -/

/-- **The widest leaf.** -/
def mapWmax (m : List RowLeaf) : ℕ := m.foldr (fun l a => max l.n a) 0

/-- **The powers' exponents** (`table_internal::digest_exprs`): `0, …, wmax − 1`, then each nonzero
offset. -/
def powerExps (m : List RowLeaf) : List ℕ :=
  List.range (mapWmax m) ++ ((m.filter (·.off != 0)).map (·.off))

/-- **The identifiers and the map of a table's selection** (`lib/gordiehowe/lib/table.h`,
`public_table`, `select_row`). -/
structure TableShape where
  /-- The domain of the selection's predicate. -/
  dom : ℕ
  /-- The constant `1`. -/
  one : ℕ
  /-- The constant `0`. -/
  zero : ℕ
  /-- The natural of `−1`. -/
  mOne : ℕ
  /-- The challenge `γ`'s value. -/
  gamma : ℕ
  /-- The challenge `γ`. -/
  chal : ℕ
  /-- The powers (`<table>.powers`). -/
  pow : ℕ
  /-- The digests (`<table>.digests`). -/
  dig : ℕ
  /-- The index bits. -/
  idx : ℕ
  /-- The selection's predicate. -/
  pred : ℕ
  /-- The index bits' check. -/
  idxPred : ℕ
  /-- The record. -/
  record : Expr
  /-- The row map. -/
  map : List RowLeaf
  /-- The column blocks: value and width. -/
  parts : List (ℕ × ℕ)
  /-- The table's rows. -/
  rows : ℕ
  /-- The index bits' count. -/
  bits : ℕ

namespace TableShape

variable (t : TableShape)

/-- **The powers' expression.** -/
def powExpr : Expr :=
  match (ir.value t.pow).kind with
  | .pub (.expr E) => E
  | _ => .leaf t.pow

/-- **The digests' expression.** -/
def digExpr : Expr :=
  match (ir.value t.dig).kind with
  | .pub (.expr E) => E
  | _ => .leaf t.dig

/-- **The context of the public expressions**: the constant `1`, `γ` and the powers. -/
def pubCtx : PowCtx := ⟨onePub t.one t.gamma, some (t.powExpr ir, powerExps t.map)⟩

/-- **The context of the selection's predicate**: the powers as a value. -/
def predCtx : PowCtx := ⟨fun v => if v = t.pow then some (powerExps t.map) else none, none⟩

/-- **The selection's body.** -/
def bodyOk : PredBody → Bool
  | .equal d (.add T (.scale (.const c) F)) (.leaf z) _ =>
    d == t.dom && c == t.mOne && z == t.zero &&
      ir.recTermsOk t.record t.predCtx t.map (addSpine T) &&
      decide (ir.foldOf? t.idx t.dig (2 ^ t.bits) t.bits (2 * t.bits + 2) F = some (t.bits, 1))
  | _ => false

/-- **The shape's checks.** -/
def okB : Bool :=
  mapWfFrom 0 t.map && mapWidth t.map == (t.parts.map (·.2)).sum &&
    decide (ir.powSym ⟨onePub t.one t.gamma, none⟩ powFuel (t.powExpr ir) = some (powerExps t.map)) &&
    ir.digestsOk (t.pubCtx ir) t.map t.parts t.rows (2 ^ t.bits) (t.digExpr ir) &&
    t.bodyOk ir (ir.predicate t.pred).body

end TableShape

end GordieHowe.RealizedProgram
