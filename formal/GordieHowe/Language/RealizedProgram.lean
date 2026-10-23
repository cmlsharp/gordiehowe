-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Export

@[expose] public section

/-!
# GordieHowe: the plan's program, a deep embedding

The realized program of a compiled plan (its values, predicates, lookups, challenges and messages,
and GKR circuits), as plain data an exporter writes as Lean terms, like the generated plan files
(`GordieHowe/Generated/*`). The meaning of the data is `GordieHowe/Language/RealizedProgram/Semantics.lean`; the
checks of `Plan.Valid` that read it are `GordieHowe/Language/RealizedProgram/Valid.lean`.

**Identifiers.** Every table of the program is a list, and an identifier is a position in its
list: value `v` is `values[v]`, predicate `p` is `predicates[p]`, and so on for fields, domains,
challenges, lookup tables, batches and circuits. The names are provenance only. Value identifiers
are in declaration order, which the message order `MsgBefore` refines (lexicographic in phase, then
identifier).

**Coordinates.** A value is a tensor; its coordinates are numbered row-major, `0` to
`Value.size - 1`. An expression denotes a vector of coordinates of one field
(`Expr.len`); views (slices, rotations, index maps, broadcasting, reshapes) are written as
`Expr.reindex` with the explicit index map, a zero coordinate indexing a constant zero value
concatenated last.

**Shared expressions.** An expression is a DAG: each node read more than once, and each derived
value (a value with no storage: an affine view, a wiring view, a value bound to its digits), is an
entry of `GordieHowe.RealizedProgram.exprs`, read as `Expr.ref k`; entry `k` reads only entries of smaller index.

**Named operators** (`NamedOp`) are the C++ `OpSpec`s exported by name; their meanings are
`GordieHowe/Language/RealizedProgram/Ops.lean`.

**Phases** are numbered from `1`, as in the exported plan; phase `0` holds the values committed
before any challenge.
-/

namespace GordieHowe.RealizedProgram

open Export

/-! ## Fields and domains -/

/-- **A field of the program**: a domain's field, or a MAC field no domain commits. `name` is the
`FieldSpec.name` of the plan and of the registry (`Export.fieldRegistry`). -/
structure FieldDecl where
  /-- The field's name. -/
  name : String
  /-- The characteristic. -/
  characteristic : Nat
  /-- The degree over the prime field. -/
  degree : Nat
  deriving Repr, DecidableEq, Inhabited

/-- **A domain of the program**: its name (the plan's `Domain.name`) and its field (an identifier
in `RealizedProgram.fields`), with the placement of its predicate groups (`Export.Placement`). A MAC field
that no domain commits (the odd/odd MAC's key, powers and tag) is a domain that commits nothing
(`commits = false`). -/
structure DomainDecl where
  /-- The domain's name. -/
  name : String
  /-- The domain's field. -/
  field : Nat
  /-- The domain holds a commitment. -/
  commits : Bool := true
  /-- The placement of each predicate group. -/
  placements : List Placement := []
  deriving Repr, DecidableEq, Inhabited

/-- **A space of field elements**: the whole field, or the packing-tree node named `name` (a
declared subfield, or `bit`, the prime subfield `GF(2)` of a binary field). Challenges are drawn
uniformly from a space, and pads are uniform in one. -/
inductive Space where
  /-- The whole field. -/
  | full
  /-- The packing-tree node `name`. -/
  | node (name : String)
  deriving Repr, DecidableEq, Inhabited

/-! ## Expressions -/

/-- **A coefficient** of a constant multiple or of a linear map: a constant, written as the
natural number of its field element in the C++ encoding, or coordinate `i` of the value `v` (a
public value: a statement value, a constant, a challenge, or a public expression). -/
inductive Coef where
  /-- A constant. -/
  | const (c : Nat)
  /-- Coordinate `i` of the value `v`. -/
  | node (v i : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- **The form of a polynomial operand** of a named operator: its coefficients, or its
negacyclic transform at the root `psi` (the field element of natural `psi` in the C++ encoding, a
primitive `2n`-th root of unity) in scheme order. -/
inductive ConvForm where
  /-- The coefficients. -/
  | coefficients
  /-- The transform at `psi`, in scheme order. -/
  | ntt (psi : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- **The output order of a negacyclic transform**: the scheme order (frequency `m` at
`ψ^(2·br(m) + 1)`, `br` the bit reversal of the C++'s `FieldNtt`) or the natural order (frequency
`m` at `ψ^(2m + 1)`). -/
inductive NttOrder where
  /-- The scheme order. -/
  | scheme
  /-- The natural order. -/
  | natural
  deriving Repr, DecidableEq, Inhabited

/-- **A named linear operator** (`lib/gordiehowe/ops/operators.h`), applied along the last axis of
its operand. A value parameter (`h`, `a`, `t`, `M`, `r`, `d`, `c`) is a value identifier, read as a
public operand; a field-element parameter (`psi`, `base`) is the natural of the C++ encoding. `n` is
the length of the last axis.

* `negacyclicConv h form`: `y_j = Σ_{i+k=j} h_i x_k − Σ_{i+k=j+n} h_i x_k`, `h` of size `n` in
  the form `form`;
* `polyMatVec a K L form`: `y_i = Σ_j a_ij · x_j` in `F[X]/(X^n + 1)`, `[L][n] → [K][n]`;
* `polyBroadcast t K form`: `y_i = t_i · x` in `F[X]/(X^n + 1)`, `[n] → [K][n]`;
* `ntt n psi order`: the negacyclic transform `y_m = Σ_i x_i ψ^((2·br(m)+1) i)` (scheme order) or
  `Σ_i x_i ψ^((2m+1) i)` (natural order);
* `inverseNtt n psi`: the inverse of `ntt n psi scheme`;
* `nttTranspose n psi`: `x = Vᵀ y` for `V[m][i] = ψ^((2m+1) i)`;
* `rowDot M R W`: `y_r = Σ_c M[r][c] · x_c`, `[W] → [R]`;
* `macConv r w nch taps`: `y_b = Σ_c Σ_i x[c·w + i] · fold(R_c · x^i)[b]` over the integers read
  in the field, `R_c` the coefficient bits of `r_c` in the MAC field's polynomial basis, `fold` the
  reduction modulo `x^w + Σ_{d ∈ taps} x^d`, `[nch·w] → [w]`;
* `acyclicConv h lx`: `y_i = Σ_{a+b=i} x_a h_b`, `[lx] → [lx + lh − 1]`;
* `diagonal d`, `constDiagonal d`: `y_i = d_i x_i` (`d` public, or a constant value);
* `scale c`: `y_i = c x_i`;
* `sum w`: `y_j = Σ_{t<w} x_{j w + t}`;
* `fromDigits k base`: `y = Σ_{l<k} base^l x_l`, `[k] → [1]`;
* `batched b op`: `op` on each of `b` consecutive slices. -/
inductive NamedOp where
  /-- The negacyclic convolution with `h`. -/
  | negacyclicConv (h : Nat) (form : ConvForm)
  /-- The polynomial matrix-vector product. -/
  | polyMatVec (a K L : Nat) (form : ConvForm)
  /-- The polynomial broadcast product. -/
  | polyBroadcast (t K : Nat) (form : ConvForm)
  /-- The negacyclic transform. -/
  | ntt (n psi : Nat) (order : NttOrder)
  /-- The inverse transform. -/
  | inverseNtt (n psi : Nat)
  /-- The transposed transform. -/
  | nttTranspose (n psi : Nat)
  /-- The rows of a public matrix. -/
  | rowDot (M R W : Nat)
  /-- The MAC's carry-free convolution. -/
  | macConv (r w nch : Nat) (taps : List Nat)
  /-- The acyclic convolution with `h`. -/
  | acyclicConv (h lx : Nat)
  /-- A public diagonal. -/
  | diagonal (d : Nat)
  /-- A public scalar. -/
  | scale (c : Nat)
  /-- A constant diagonal. -/
  | constDiagonal (d : Nat)
  /-- The sum of groups of `w`. -/
  | sum (w : Nat)
  /-- The number of `k` digits in base `base`. -/
  | fromDigits (k base : Nat)
  /-- `op` on `b` consecutive slices. -/
  | batched (b : Nat) (op : NamedOp)
  deriving Repr, DecidableEq, Inhabited

/-- **A Logic builder** (`circuits/logic/logic.h`) on words of `w` bits along the last axis, bit `0`
the least significant: `lt`, `leq`, `eq` on two word arguments; `any`, `all` on one argument, over
the last axis. -/
inductive LogicOp where
  /-- `a < b`. -/
  | lt
  /-- `a ≤ b`. -/
  | leq
  /-- `a = b`. -/
  | eq
  /-- Some bit is set. -/
  | any
  /-- Every bit is set. -/
  | all
  deriving Repr, DecidableEq, Inhabited

/-- **An index map**: runs of arithmetic progressions, `(start, step, count)` standing for `start,
start + step, …, start + (count − 1)·step`; the map is the concatenation of its runs' entries
(`IndexMap.toList`), entry `i` read off the run containing it (`IndexMap.entry`). -/
abbrev IndexMap : Type := List (Nat × Int × Nat)

namespace IndexMap

/-- **The number of entries** of an index map. -/
def size (m : IndexMap) : Nat := (m.map (·.2.2)).sum

/-- **Entry `i`** of an index map: `start + step · (i − o)` of the run with `o ≤ i < o + count`, `o`
the earlier runs' counts (`0` past the end). -/
def entry : IndexMap → Nat → Nat
  | [], _ => 0
  | (s, d, c) :: rest, i => if i < c then ((s : Int) + d * i).toNat else entry rest (i - c)

/-- **The entries** of an index map, in order. -/
def toList (m : IndexMap) : List Nat :=
  m.flatMap fun r => (List.range r.2.2).map fun t : Nat => ((r.1 : Int) + r.2.1 * t).toNat

/-- **Entry `i` is the `i`-th entry of the concatenated runs.** -/
theorem entry_eq_getD_toList : ∀ (m : IndexMap) (i : Nat), m.entry i = m.toList.getD i 0
  | [], i => by simp [entry, toList]
  | (s, d, c) :: rest, i => by
    have ih := entry_eq_getD_toList rest (i - c)
    simp only [toList] at ih
    simp only [entry, toList, List.flatMap_cons]
    rw [List.getD_eq_getElem?_getD] at ih ⊢
    by_cases h : i < c
    · rw [if_pos h, List.getElem?_append_left (by simpa using h)]
      simp [h]
    · rw [if_neg h, List.getElem?_append_right (by simpa using Nat.le_of_not_lt h)]
      simpa using ih

/-- **Every entry is a natural below `n`**: each run's first and last entries (the entries of a run
lie between them) are in `[0, n)`. -/
def inRange (m : IndexMap) (n : Nat) : Bool :=
  m.all fun r => r.2.2 == 0 ||
    (0 ≤ (r.1 : Int) + r.2.1 * (r.2.2 - 1 : Nat) && r.1 < n &&
      (r.1 : Int) + r.2.1 * (r.2.2 - 1 : Nat) < n)

end IndexMap

/-- **An expression** over the values of one field: a vector of field elements.

* `leaf v`: the coordinates of value `v`;
* `add`, `sub`, `mul`: coordinatewise, on vectors of one length;
* `scale c e`: the constant or public multiple `c · e`;
* `reindex idx e`: coordinate `j` is coordinate `idx[j]` of `e` (slices, rotations, index maps,
  reshapes and broadcasting);
* `concat e e'`: the coordinates of `e`, then those of `e'`;
* `linear rows e`: the linear map with sparse rows `rows[j] = [(column, coefficient), …]`;
* `prod n e`: the product along the last axis of length `n` (coordinate `j` is
  `Π_{t < n} e[j n + t]`);
* `mux b t e`: `b · t + (1 − b) · e`, for `b` a `Bit` expression;
* `apply op e`: the named operator `op` along the last axis of `e`, batched over the leading axes;
* `ref k`: shared expression `k` (`RealizedProgram.exprs`);
* `logic op w args`: the Logic builder `op` on words of `w` bits (`LogicOp`). -/
inductive Expr where
  /-- The coordinates of value `v`. -/
  | leaf (v : Nat)
  /-- The sum. -/
  | add (e e' : Expr)
  /-- The difference. -/
  | sub (e e' : Expr)
  /-- A constant or public multiple. -/
  | scale (c : Coef) (e : Expr)
  /-- The coordinatewise product. -/
  | mul (e e' : Expr)
  /-- A view by an index map. -/
  | reindex (idx : IndexMap) (e : Expr)
  /-- The concatenation. -/
  | concat (e e' : Expr)
  /-- A linear map with constant or public coefficients, by sparse rows. -/
  | linear (rows : List (List (Nat × Coef))) (e : Expr)
  /-- The product along the last axis of length `n`. -/
  | prod (n : Nat) (e : Expr)
  /-- The multiplexer `b · t + (1 − b) · e`. -/
  | mux (b t e : Expr)
  /-- A named operator along the last axis. -/
  | apply (op : NamedOp) (e : Expr)
  /-- Shared expression `k`. -/
  | ref (k : Nat)
  /-- A Logic builder on words of `w` bits. -/
  | logic (op : LogicOp) (w : Nat) (args : List Expr)
  deriving Repr, Inhabited

/-! ## Structural equality of expressions -/

mutual

/-- **Structural equality of expressions**, a `Bool` function (`Expr` has no derived decidable
equality: it is a nested inductive; the decidable equality of `Expr` is decided by it). -/
def Expr.beq : Expr → Expr → Bool
  | .leaf v, .leaf v' => v == v'
  | .add a b, .add a' b' => a.beq a' && b.beq b'
  | .sub a b, .sub a' b' => a.beq a' && b.beq b'
  | .scale c a, .scale c' a' => decide (c = c') && a.beq a'
  | .mul a b, .mul a' b' => a.beq a' && b.beq b'
  | .reindex idx a, .reindex idx' a' => decide (idx = idx') && a.beq a'
  | .concat a b, .concat a' b' => a.beq a' && b.beq b'
  | .linear rows a, .linear rows' a' => decide (rows = rows') && a.beq a'
  | .prod n a, .prod n' a' => n == n' && a.beq a'
  | .mux b t a, .mux b' t' a' => b.beq b' && t.beq t' && a.beq a'
  | .apply op a, .apply op' a' => decide (op = op') && a.beq a'
  | .ref k, .ref k' => k == k'
  | .logic op w args, .logic op' w' args' =>
      decide (op = op') && w == w' && Expr.beqList args args'
  | _, _ => false

/-- Structural equality of lists of expressions. -/
def Expr.beqList : List Expr → List Expr → Bool
  | [], [] => true
  | e :: es, e' :: es' => e.beq e' && Expr.beqList es es'
  | _, _ => false

end

mutual

/-- **Structurally equal expressions are equal.** -/
theorem Expr.eq_of_beq : ∀ {e e' : Expr}, e.beq e' = true → e = e'
  | .leaf _, e', h => by
    cases e' <;> first | exact absurd h Bool.false_ne_true | skip
    simp only [Expr.beq, beq_iff_eq] at h
    rw [h]
  | .add _ _, e', h => by
    cases e' <;> first | exact absurd h Bool.false_ne_true | skip
    simp only [Expr.beq, Bool.and_eq_true] at h
    rw [Expr.eq_of_beq h.1, Expr.eq_of_beq h.2]
  | .sub _ _, e', h => by
    cases e' <;> first | exact absurd h Bool.false_ne_true | skip
    simp only [Expr.beq, Bool.and_eq_true] at h
    rw [Expr.eq_of_beq h.1, Expr.eq_of_beq h.2]
  | .mul _ _, e', h => by
    cases e' <;> first | exact absurd h Bool.false_ne_true | skip
    simp only [Expr.beq, Bool.and_eq_true] at h
    rw [Expr.eq_of_beq h.1, Expr.eq_of_beq h.2]
  | .concat _ _, e', h => by
    cases e' <;> first | exact absurd h Bool.false_ne_true | skip
    simp only [Expr.beq, Bool.and_eq_true] at h
    rw [Expr.eq_of_beq h.1, Expr.eq_of_beq h.2]
  | .scale _ _, e', h => by
    cases e' <;> first | exact absurd h Bool.false_ne_true | skip
    simp only [Expr.beq, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [h.1, Expr.eq_of_beq h.2]
  | .reindex _ _, e', h => by
    cases e' <;> first | exact absurd h Bool.false_ne_true | skip
    simp only [Expr.beq, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [h.1, Expr.eq_of_beq h.2]
  | .linear _ _, e', h => by
    cases e' <;> first | exact absurd h Bool.false_ne_true | skip
    simp only [Expr.beq, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [h.1, Expr.eq_of_beq h.2]
  | .apply _ _, e', h => by
    cases e' <;> first | exact absurd h Bool.false_ne_true | skip
    simp only [Expr.beq, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [h.1, Expr.eq_of_beq h.2]
  | .prod _ _, e', h => by
    cases e' <;> first | exact absurd h Bool.false_ne_true | skip
    simp only [Expr.beq, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1, Expr.eq_of_beq h.2]
  | .mux _ _ _, e', h => by
    cases e' <;> first | exact absurd h Bool.false_ne_true | skip
    simp only [Expr.beq, Bool.and_eq_true] at h
    rw [Expr.eq_of_beq h.1.1, Expr.eq_of_beq h.1.2, Expr.eq_of_beq h.2]
  | .ref _, e', h => by
    cases e' <;> first | exact absurd h Bool.false_ne_true | skip
    simp only [Expr.beq, beq_iff_eq] at h
    rw [h]
  | .logic _ _ _, e', h => by
    cases e' <;> first | exact absurd h Bool.false_ne_true | skip
    simp only [Expr.beq, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    rw [h.1.1, h.1.2, Expr.eq_of_beqList h.2]

/-- **Structurally equal lists of expressions are equal.** -/
theorem Expr.eq_of_beqList : ∀ {es es' : List Expr}, Expr.beqList es es' = true → es = es'
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
    simp only [Expr.beqList, Bool.and_eq_true] at h
    rw [Expr.eq_of_beq h.1, Expr.eq_of_beqList h.2]
  | [], _ :: _, h | _ :: _, [], h => absurd h Bool.false_ne_true

end

mutual

/-- **Every expression is structurally equal to itself.** -/
theorem Expr.beq_self : ∀ e : Expr, e.beq e = true
  | .leaf _ => by simp [Expr.beq]
  | .add a b => by simp [Expr.beq, Expr.beq_self a, Expr.beq_self b]
  | .sub a b => by simp [Expr.beq, Expr.beq_self a, Expr.beq_self b]
  | .scale _ a => by simp [Expr.beq, Expr.beq_self a]
  | .mul a b => by simp [Expr.beq, Expr.beq_self a, Expr.beq_self b]
  | .reindex _ a => by simp [Expr.beq, Expr.beq_self a]
  | .concat a b => by simp [Expr.beq, Expr.beq_self a, Expr.beq_self b]
  | .linear _ a => by simp [Expr.beq, Expr.beq_self a]
  | .prod _ a => by simp [Expr.beq, Expr.beq_self a]
  | .mux b t a => by simp [Expr.beq, Expr.beq_self b, Expr.beq_self t, Expr.beq_self a]
  | .apply _ a => by simp [Expr.beq, Expr.beq_self a]
  | .ref _ => by simp [Expr.beq]
  | .logic _ _ args => by simp [Expr.beq, Expr.beqList_self args]

/-- **Every list of expressions is structurally equal to itself.** -/
theorem Expr.beqList_self : ∀ es : List Expr, Expr.beqList es es = true
  | [] => rfl
  | e :: es => by simp [Expr.beqList, Expr.beq_self e, Expr.beqList_self es]

end

/-- **Decidable equality of expressions**, by structural equality (`Expr.beq`). -/
instance : DecidableEq Expr := fun a b =>
  decidable_of_iff (a.beq b = true) ⟨Expr.eq_of_beq, fun h => h ▸ Expr.beq_self a⟩

/-! ## Values -/

/-- **A value type**. -/
inductive VType where
  /-- `0` or `1`. -/
  | bit
  /-- An element of the subfield named `E`. -/
  | sub (E : String)
  /-- Any element. -/
  | field
  deriving Repr, DecidableEq, Inhabited

/-- **How a public value is given**: a statement member, an opaque named function of statement
members and messages `args` (hash-to-field, decoding; it never reads a challenge), or an expression
over statement members, constants and challenges (a challenge-dependent public value, evaluated by
both parties). -/
inductive PubDef where
  /-- A statement member. -/
  | input
  /-- An opaque named function of the values `args`. -/
  | opaque (name : String) (args : List Nat)
  /-- An expression. -/
  | expr (e : Expr)
  deriving Repr, Inhabited

/-- **The kind of a value**: committed in phase `0` (`priv`), public, a constant (its coordinates in
the C++ encoding), the challenge `c` (an identifier in `RealizedProgram.challenges`), late (sent masked in
its phase), a bit view (`bits w sel`: the canonical bits of the committed `Sub(E)` words `sel` of
value `w`, `deg E` bits per word, bit `j` the coefficient of the subfield's basis element `j`;
`Domain::bits`), a pad copy (`padCopy v map`: the image of late value `v`'s pad under the named map,
committed in phase `0`; `polynomialBits`, the pad's coefficient bits in the binary field's
polynomial basis, the MAC's blind), a message (`message v`: the masked message `v + pad(v)` of late
value `v`, public in its phase), or a value bound to its digits (`bound e`: a source value the range
lowering bound to its digits, with no cell; the source program `Π_P` commits it in phase `0`, and
the realized program reads it as the expression `e` over the digits). -/
inductive Kind where
  /-- A committed value of phase `0`. -/
  | priv
  /-- A public value. -/
  | pub (d : PubDef)
  /-- A constant. -/
  | constant (entries : List Nat)
  /-- The challenge `c`. -/
  | challenge (c : Nat)
  /-- A late value. -/
  | late
  /-- The bit view of the words `sel` of value `w`. -/
  | bits (w : Nat) (sel : IndexMap)
  /-- The image of late value `v`'s pad under the map `map`. -/
  | padCopy (v : Nat) (map : String)
  /-- The masked message of late value `v`. -/
  | message (v : Nat)
  /-- A source value bound to its digits, read as `e` in the realized program. -/
  | bound (e : Expr)
  deriving Repr, Inhabited

/-- Whether a kind is `late`. -/
def Kind.isLate : Kind → Bool
  | .late => true
  | _ => false

/-- **Whether a kind may lie in a field no domain commits**: a challenge, a public expression, a
late value or a message (the odd–odd MAC's key, chunk powers, tag and the tag's message). -/
def Kind.allowsField : Kind → Bool
  | .challenge _ => true
  | .pub (.expr _) => true
  | .late => true
  | .message _ => true
  | _ => false

/-- Whether a kind is `priv`. -/
def Kind.isPriv : Kind → Bool
  | .priv => true
  | _ => false

/-- Whether a kind is `bound`. -/
def Kind.isBound : Kind → Bool
  | .bound _ => true
  | _ => false

/-- The packing-tree node of a value type (`bit`, or the subfield's name); none for `Field`. -/
def VType.nodeName : VType → Option String
  | .bit => some "bit"
  | .sub E => some E
  | .field => none

/-- **Where a value's type is enforced** (`RealizedProgram.TypeSources`): by its packing-tree node, or by
the realized program's predicate `p`. -/
inductive TypeSource where
  /-- Stored at a packing-tree node of that subfield. -/
  | node
  /-- Enforced by predicate `p`. -/
  | pred (p : Nat)
  /-- No source (a public value, or a `Field` value). -/
  | none
  deriving Repr, DecidableEq, Inhabited

/-- **How a late value is realized**: masked by a pad uniform over `padSpace` (a node of its
domain's packing tree; `Plan.MessageSpacesValid`), sent as `x + P`; or committed in a Ligero
commitment of its own phase `k` (reserved; `Plan.Valid` rejects it). -/
inductive LateRealization where
  /-- A pad over `padSpace`. -/
  | pad (padSpace : Space)
  /-- A commitment of phase `k`. -/
  | commitment (k : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- **What a late value or a predicate reads from the run and the pads**: the challenge `c`, the
late value `v` (as message minus pad), or the pad of late value `v`. -/
inductive Read where
  /-- The challenge `c`. -/
  | chal (c : Nat)
  /-- The late value `v`. -/
  | late (v : Nat)
  /-- The pad of late value `v`. -/
  | pad (v : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- **The position of a committed value in its domain's packing tree**: the node and the first
coordinate. -/
structure NodeRef where
  /-- The node's name. -/
  name : String
  /-- The first coordinate. -/
  offset : Nat := 0
  deriving Repr, DecidableEq, Inhabited

/-- **The role of a value**: a value of the source program, or a value the compiler introduced to
realize predicate `owner` (a range request's digits and the table groups' histograms: the `in`; the
domain's `alpha`: the first member of its first table group). The source program `Π_P` is the values
and predicates of role `source`. -/
inductive ValueRole where
  /-- A value of the source program. -/
  | source
  /-- A value realizing predicate `owner`. -/
  | realization (owner : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- **A value node**. For a late value, `reads` lists the challenges and pads its honest computation
reads (never its own pad) and `realization` its realization; for a challenge-dependent public
expression, `degree` lists its degree in each challenge, as `(challenge, degree)`. A value of a
field that no domain commits (the odd–odd MAC's key powers, tag and message) names that field in
`field`, and `domain` is then not read (`RealizedProgram.valueField`); validity admits such a value only of
a kind `Kind.allowsField` allows (`RealizedProgram.FieldOk`). -/
structure Value where
  /-- The C++ node name. -/
  name : String
  /-- The domain (an identifier in `RealizedProgram.domains`; not read when `field` is set). -/
  domain : Nat := 0
  /-- The shape. -/
  shape : List Nat
  /-- The kind. -/
  kind : Kind
  /-- The type. -/
  type : VType
  /-- The phase. -/
  phase : Nat := 0
  /-- The packing-tree node of a committed value. -/
  node : Option NodeRef := none
  /-- Where the type is enforced. -/
  typeSource : TypeSource := .none
  /-- What the honest computation of a late value reads. -/
  reads : List Read := []
  /-- The realization of a late value. -/
  realization : LateRealization := .pad .full
  /-- The degree in each challenge of a public expression. -/
  degree : List (Nat × Nat) := []
  /-- **The statement bound** `N` of a bounded public value (`v := stmt(N)`): the statements are
  the assignments with every coordinate of the value in `[0, N − 1]` (`RealizedProgram.StmtBounded`); the
  verifier rejects any other before the transcript starts. -/
  bound : Option Nat := none
  /-- The role. -/
  role : ValueRole := .source
  /-- The field (in `RealizedProgram.fields`) of a value that no domain holds. -/
  field : Option Nat := none
  deriving Repr, Inhabited

/-- The number of coordinates of a value. -/
def Value.size (x : Value) : Nat := x.shape.prod

/-- The pad space of a value (the whole field for a value that is not pad-realized). -/
def Value.padSpace (x : Value) : Space :=
  match x.realization with
  | .pad s => s
  | .commitment _ => .full

/-! ## Predicates -/

/-- **The target of a field `equal`** (`RealizedProgram.TargetsAdmit`): affine rows, the quadratic test, the
batch `id` (an identifier in `RealizedProgram.batches`), the GKR circuit `circuit` (in
`RealizedProgram.circuits`), or the realization predicate `pred`: an `equal` whose sides are this
predicate's sides with each convolution read through its spectral realization
(`RealizedProgram.SpectralConv`, compiler/conv.h). -/
inductive Target where
  /-- Affine rows of the linear test. -/
  | affine
  /-- The quadratic test. -/
  | quadratic
  /-- The batch `id`. -/
  | batch (id : Nat)
  /-- The GKR circuit `circuit`. -/
  | gkr (circuit : Nat)
  /-- The field equation of predicate `pred`, the sides' convolutions read through their
  spectral realizations. -/
  | realized (pred : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- **The set of an `in` predicate**: the range `[0, n)`, the rows of lookup table `t`, or the
entries of an expression `e'` (the set of the paper's `in(e, e')`, `def:o-preds`). -/
inductive InSet where
  /-- The range `[0, n)`. -/
  | range (n : Nat)
  /-- The rows of table `t`. -/
  | table (t : Nat)
  /-- The entries of expression `e'`. -/
  | expr (e' : Expr)
  deriving Repr, DecidableEq, Inhabited

/-- **The kind of a lookup realization** (`RealizationKind`, `lib/gordiehowe/core.h`): a direct
lookup, a scaled or shifted needle, the needle's digits, two digit sets (`e` and `e + (T^k − n)`),
or the complement. -/
inductive LookupKind where
  /-- A direct lookup. -/
  | direct
  /-- A scaled needle. -/
  | scaled
  /-- A shifted needle. -/
  | shifted
  /-- The digits. -/
  | digits
  /-- Two digit sets. -/
  | twoSided
  /-- The complement. -/
  | complement
  deriving Repr, DecidableEq, Inhabited

/-- **A lookup realization of an `in` predicate**: lookups of `digits` digits in base `base` into
group `group` of table `table`, of kind `kind`; the digits committed as the values `digitValues`
(one per position, `range.<r>.d<j>`) and the second digit set as the values `second`
(`range.<r>.h<j>`, two-sided); the needles, the expressions looked up in the table in order
(`direct`: the value; `scaled`: `s·v`; `shifted`: `v` and `v + (T − n)`; `complement`:
`(n − 1) − v`; `digits`: the digits; `twoSided`: the digits, then those of `(n − 1) − v`); the
request's honest bound `n` and largest admissible bound `m` (`n ≤ N ≤ m` for the established bound
`N`); the scale `s` (`scaled`) and the shift `T − n` (`shifted`). -/
structure LookupRealization where
  /-- The table. -/
  table : Nat
  /-- The group of the first needle. -/
  group : Nat
  /-- The kind. -/
  kind : LookupKind
  /-- The digit count `k`. -/
  digits : Nat
  /-- The base `T`. -/
  base : Nat
  /-- The digit values. -/
  digitValues : List Nat := []
  /-- The second digit set. -/
  second : List Nat := []
  /-- The needles. -/
  needles : List Expr := []
  /-- The honest bound `n`. -/
  honest : Nat := 0
  /-- The largest admissible bound `m`. -/
  max : Nat := 0
  /-- The scale. -/
  scale : Nat := 0
  /-- The shift. -/
  shift : Nat := 0
  deriving Repr, Inhabited

/-- **The realization of an `in` predicate**: lookups (`LookupRealization`), or implied by interval
propagation, `v ∈ [lo, hi]` (no lookup). -/
inductive InRealization where
  /-- Lookups into a table group. -/
  | lookup (r : LookupRealization)
  /-- Implied by the intervals. -/
  | implied (lo hi : Int)
  deriving Repr, Inhabited

/-- **The form of a `mod_q` realization** (`lib/gordiehowe/compiler/mod.h`):
`e − e' = q (quotientLo + Q)` with `Q` zero (`constant`), a Boolean derived quotient (`bit`), a
derived quotient bounded by one `in` (`oneDigit`), digits in base `radix` with the top one derived
(`digits`) or all committed (`committedDigits`), the field equation itself for `q = p` (`field`),
the grouped form when the left side reaches `p` (`grouped`), or integer equality (`integer`,
`q = 0`, `assert_int_equal`: the field equation `e = e'` with the sides' intervals and their span
below `p`). -/
inductive ModForm where
  /-- The field equation, `q = p`. -/
  | field
  /-- `Q = 0`. -/
  | constant
  /-- A Boolean quotient. -/
  | bit
  /-- A quotient bounded by one `in`. -/
  | oneDigit
  /-- Digits, the top one derived. -/
  | digits
  /-- Digits, all committed. -/
  | committedDigits
  /-- The grouped form. -/
  | grouped
  /-- Integer equality, `q = 0` (`assert_int_equal`). -/
  | integer
  deriving Repr, DecidableEq, Inhabited

/-- **The grouped form of a `mod_q`**: per group `g` of units `(first, count)` the accumulator `S_g`,
its quotient digits in base `base` (`digitCount` digits, `groupDigits`), the residue
`r_g = S_g − q · from_digits(gq_g)` (`residues`), each group sum below `groupBound`. -/
structure GroupedMod where
  /-- The base `T` of the quotient digits. -/
  base : Nat
  /-- The digit count `k`. -/
  digitCount : Nat
  /-- The groups `(first, count)`. -/
  groups : List (Nat × Nat)
  /-- The bound on a group's sum. -/
  groupBound : Nat
  /-- The groups' quotient digits. -/
  groupDigits : Expr
  /-- The residues. -/
  residues : Expr
  /-- The accumulators. -/
  accumulators : Option Expr := none
  deriving Repr, Inhabited

/-- **The realization of a `mod_q`**: with `[lhsLo, lhsHi]` and `[rhsLo, rhsHi]` the sides'
intervals, `e − e' = q (quotientLo + Q)` with `Q ∈ [0, qmax]` given by `form`: the derived quotient
`quotient`, or the digits `digits` in base `radix`; `ranges` the `in` predicates bounding the
quotient or its digits with their bounds `(n, N, m)`; the grouped form; the target of the field
equation (`q = 0`, or `q = p`); and for the integer form the span
`max(lhsHi, rhsHi) − min(lhsLo, rhsLo)` of the sides' intervals (`none` for the other forms). -/
structure ModRealization where
  /-- The form. -/
  form : ModForm := .field
  /-- The left side's interval. -/
  lhsLo : Int := 0
  lhsHi : Int := 0
  /-- The right side's interval. -/
  rhsLo : Int := 0
  rhsHi : Int := 0
  /-- The quotient's lower end `⌈(lhsLo − rhsHi)/q⌉`. -/
  quotientLo : Int := 0
  /-- The quotient's range `qmax`. -/
  qmax : Nat := 0
  /-- The derived quotient. -/
  quotient : Option Expr := none
  /-- The quotient's digits. -/
  digits : List Expr := []
  /-- The digits' radix. -/
  radix : Nat := 0
  /-- The `in` predicates bounding the quotient or its digits. -/
  ranges : List Nat := []
  /-- Their bounds `(n, N, m)`. -/
  bounds : List (Nat × Nat × Nat) := []
  /-- The grouped form. -/
  grouped : Option GroupedMod := none
  /-- The target of the field equation. -/
  target : Option Target := none
  /-- The span of the sides' intervals (the integer form). -/
  span : Option Nat := none
  deriving Repr, Inhabited

/-- **What a cross-field `equal` states**: the same bits (`width = 1`), or the same integers of
`width` bits. -/
structure CrossKind where
  /-- The width in bits of each coordinate. -/
  width : Nat := 1
  deriving Repr, DecidableEq, Inhabited

/-- **The realization of a cross-field `equal`** (the polynomial MAC): the MAC field (in
`RealizedProgram.fields`), the key (a challenge), the blind (a committed value of the binary domain, the pad
of the tag), the tag (a late value), the H half (the predicate `<mac>.H`, an ordinary `equal` with
its own target), the chunking (`chunks` chunks of `width` bits), the accumulators and the quotient
digits (values). When no domain hosts the MAC (two odd domains, or an `x` domain of characteristic
`2` other than the MAC field) `blindX` is the `x` side's blind and `blind` the `y` side's, and the
key, the powers, the tag and its message lie in the MAC field with no domain (`Value.field`). -/
structure MacRealization where
  /-- The MAC field. -/
  macField : Nat
  /-- The key. -/
  key : Nat
  /-- The blind (the `y` side's when no domain hosts the MAC). -/
  blind : Option Nat := none
  /-- The `x` side's blind, when no domain hosts the MAC. -/
  blindX : Option Nat := none
  /-- The tag. -/
  tag : Nat
  /-- The H half. -/
  hPredicate : Option Nat := none
  /-- The chunks. -/
  chunks : Nat
  /-- The chunk width. -/
  width : Nat
  /-- The accumulators. -/
  accumulators : List Nat := []
  /-- The quotient digits. -/
  quotientDigits : List Nat := []
  deriving Repr, DecidableEq, Inhabited

/-- **A core predicate** with its realization:

* `equal d e e' target`: `e = e'` in domain `d`'s field;
* `mem d records set real`: every record (the coordinates of `records` at one index) is in the
  set; the records of a range are of arity one;
* `mod d q e e' real`: `⟦e⟧ ≡ ⟦e'⟧ (mod q)` on integers, `q = 0` meaning integer equality;
* `cross dx x dy y kind real`: `x` in domain `dx` and `y` in domain `dy` are the same bits or
  integers. -/
inductive PredBody where
  /-- A field equality. -/
  | equal (domain : Nat) (lhs rhs : Expr) (target : Target)
  /-- A lookup. -/
  | mem (domain : Nat) (records : List Expr) (set : InSet) (real : InRealization)
  /-- An integer congruence. -/
  | mod (domain : Nat) (q : Nat) (lhs rhs : Expr) (real : ModRealization)
  /-- A cross-field equality. -/
  | cross (dx : Nat) (x : Expr) (dy : Nat) (y : Expr) (kind : CrossKind) (real : MacRealization)
  deriving Repr, Inhabited

/-- **The role of a predicate**: written in the source program; part of the realization of predicate
`owner` (the H half `<mac>.H` of a cross-field `equal`, a MAC tail's rows and quotient ranges, a
range's reconstruction and top rows); or the type check of value `v` (`v · v = v`). A realization's
part reads the late values its realization sends in the phase of its challenge (the MAC tag after
the key), so the predicate order of `RealizedProgram.ChallengeOrder` (`preds`: a predicate reads the late values
each challenge of positive degree tests before it) applies to source predicates
only; its phase conditions are its owner's (`ChallengeOrder.realizations`). -/
inductive PredRole where
  /-- Written in the source program. -/
  | source
  /-- Part of the realization of predicate `owner`. -/
  | realization (owner : Nat)
  /-- The type check of value `v`. -/
  | type (v : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- Whether a role is `source`. -/
def PredRole.isSource : PredRole → Bool
  | .source => true
  | _ => false

/-- **A predicate of the realized program**: its body, the challenges and late values it reads (`Read.chal`,
`Read.late`), its degree in each challenge it reads, as `(challenge, degree)` (data: the C++'s
`deg_c(p)`), and its role. -/
structure Predicate where
  /-- The C++ name. -/
  name : String
  /-- The body. -/
  body : PredBody
  /-- The reads. -/
  reads : List Read := []
  /-- The degree in each challenge. -/
  degree : List (Nat × Nat) := []
  /-- The role. -/
  role : PredRole := .source
  deriving Repr, Inhabited

/-- The degree of a predicate in challenge `c`, `0` when not listed. -/
def Predicate.deg (p : Predicate) (c : Nat) : Nat := (p.degree.lookup c).getD 0

/-! ## Lookups, challenges, messages, batches and circuits -/

/-- **The rows of a lookup table**: the range `[0, size)`, the rows of the values `columns`
(one per record field, public or committed, of one length), or the coordinates of an expression `e`
(the table of an `in` whose set is the entries of `e`, `InSet.expr`). -/
inductive TableRows where
  /-- The range `[0, size)`. -/
  | range (size : Nat)
  /-- The rows of the columns. -/
  | columns (cols : List Nat)
  /-- The coordinates of expression `e`. -/
  | expr (e : Expr)
  deriving Repr, DecidableEq, Inhabited

/-- **A group of a lookup table**: its needle capacity (below the characteristic,
`Plan.LookupsFit`), its multiplicity values (the static histogram, committed in phase `0`, and the
late histogram, a late value; a `merged` group's late histogram counts every needle, and it has no
static histogram), and the members of its LogUp sum. -/
structure TableGroup where
  /-- The needle capacity. -/
  capacity : Nat
  /-- The static histogram. -/
  staticMult : Option Nat := none
  /-- The late histogram. -/
  lateMult : Option Nat := none
  /-- The late histogram counts every needle. -/
  merged : Bool := false
  /-- The members of its LogUp sum, in sum order (static needles first):
  `(pred, needle, first, count)`, coordinates `[first, first + count)` of needle `needle` of the
  `in` predicate `pred`. -/
  members : List (Nat × Nat × Nat × Nat) := []
  deriving Repr, DecidableEq, Inhabited

/-- **A lookup table** of a domain: its rows, its challenge `α` (one per domain), and its groups. -/
structure Table where
  /-- The name. -/
  name : String
  /-- The domain. -/
  domain : Nat
  /-- The rows. -/
  rows : TableRows
  /-- The challenge `α`. -/
  alpha : Nat
  /-- The groups. -/
  groups : List TableGroup := []
  deriving Repr, DecidableEq, Inhabited

/-- **How the packed rows of a public table are packed**: by the powers of the fixed element of
natural `kappa` (C++ encoding), or by the powers of challenge `g` (`in.gamma:<D>`). -/
inductive ExcludedPacking where
  /-- Powers of a fixed element. -/
  | fixed (kappa : Nat)
  /-- Powers of challenge `g`. -/
  | gamma (g : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- **A public table whose packed rows a challenge avoids**: the public value holding its rows
(`count` rows of `arity` coordinates, row-major) and the packing. -/
structure ExcludedTable where
  /-- The value holding the rows. -/
  rows : Nat
  /-- The number of rows. -/
  count : Nat
  /-- The coordinates of a row. -/
  arity : Nat
  /-- The packing. -/
  packing : ExcludedPacking
  deriving Repr, DecidableEq, Inhabited

/-- **The values a LogUp challenge avoids**: the integers `[0, tmax)` (`alpha:<D>`), or the packed
rows of the domain's public `assert_in` tables (`in.alpha:<D>`), or the union of two such sets
(`alpha:<D>` when the domain has both range tables and a public `assert_in` table:
`.union (.range tmax) (.packedRows tables)`). -/
inductive Excluded where
  /-- `[0, tmax)`. -/
  | range (tmax : Nat)
  /-- The packed rows of public tables. -/
  | packedRows (tables : List ExcludedTable)
  /-- The union of the values `a` and `b` avoid. -/
  | union (a b : Excluded)
  deriving Repr, DecidableEq, Inhabited

/-- **The distribution a challenge coordinate is drawn from**: uniform in the field, in the
packing-tree node `E`, or in the field minus the values `U` (LogUp's `α`, by rejection). The
exported plan writes these as the constructors of `Space`; a separate type keeps `Space` the
additive subgroups that pads and messages range over. -/
inductive Sampler where
  /-- Uniform in the field. -/
  | full
  /-- Uniform in the node `E`. -/
  | node (E : String)
  /-- Uniform in the field minus `U`. -/
  | fieldMinusTables (U : Excluded)
  deriving Repr, DecidableEq, Inhabited

/-- **The role of a challenge**: a challenge the source program declares; a challenge a core
realization draws, owned by the predicate `owner` whose realization draws it (`alpha:<D>`: the first
member `in` of the domain's first table group; the MAC key `<mac>.beta`: the cross-field `equal`);
or a realization challenge whose owner the program does not export (`assert_in`'s `in.alpha:<D>`,
`in.gamma:<D>`), which validity rejects. -/
inductive ChallengeRole where
  /-- A challenge of the source program. -/
  | source
  /-- A challenge the realization of predicate `owner` draws. -/
  | realization (owner : Nat)
  /-- A realization challenge whose owner the program does not export. -/
  | unmodeled
  deriving Repr, DecidableEq, Inhabited

/-- **A challenge**: its field (a domain's field, or a MAC field), its phase, its number of
coordinates (`size ≥ 1`), the distribution each coordinate is drawn from, and its role. -/
structure Challenge where
  /-- The name. -/
  name : String
  /-- The field. -/
  field : Nat
  /-- The phase. -/
  phase : Nat
  /-- The coordinates. -/
  size : Nat := 1
  /-- The sampler. -/
  sampler : Sampler := .full
  /-- The role. -/
  role : ChallengeRole := .source
  deriving Repr, DecidableEq, Inhabited

/-- **A message**: the late value it sends, its domain, phase, size, space, whether it lies in a
packed subfield, its codec, and its late realization: the pad uniform over a packing-tree node, the
prover sending `value + pad`, and the pad's C++ name (provenance). Messages are listed in
`MsgBefore` order. The tag of a MAC between two odd domains has `field`, the MAC field, and no
domain; validity rejects it. -/
structure Message where
  /-- The late value. -/
  value : Nat
  /-- The domain (not read when `field` is set). -/
  domain : Nat := 0
  /-- The phase. -/
  phase : Nat
  /-- The elements. -/
  size : Nat
  /-- The space. -/
  space : Space
  /-- The message lies in a packed subfield. -/
  subfieldMessage : Bool := false
  /-- The codec. -/
  codec : String := ""
  /-- The late realization. -/
  realization : LateRealization := .pad .full
  /-- The pad's name. -/
  pad : String := ""
  /-- The field (in `RealizedProgram.fields`) of a message no domain holds. -/
  field : Option Nat := none
  deriving Repr, DecidableEq, Inhabited

/-- **The operand map of a batch**: table columns, or affine forms in the bits of table words
(characteristic two). -/
inductive OperandMap where
  /-- Columns. -/
  | columns
  /-- Affine in bits. -/
  | bits
  deriving Repr, DecidableEq, Inhabited

/-- **The instances of a lane** of an operand map: one coordinate on columns, `64` coordinates on
bits (`BitOperandMap`'s bit-sliced lanes; the batch's `instances` counts lanes). -/
def OperandMap.lane : OperandMap → Nat
  | .columns => 1
  | .bits => 64

/-- **A batch** of a domain: its operand map, degree `D`, instances `N`, skip width `w`, rounds
`n`, pads and skip domain; the predicates sharing it, and the challenge `γ`
merging them (when there are several). -/
structure Batch where
  /-- The name. -/
  name : String
  /-- The domain. -/
  domain : Nat
  /-- The operand map. -/
  operands : OperandMap := .columns
  /-- The relation's degree `D`. -/
  degree : Nat
  /-- The instances `N`. -/
  instances : Nat
  /-- The skip width `w`. -/
  width : Nat
  /-- The rounds `n`. -/
  rounds : Nat
  /-- The pads. -/
  pads : Nat := 0
  /-- The skip domain. -/
  skipDomain : String := ""
  /-- The predicates sharing the batch. -/
  parts : List Nat := []
  /-- The merging challenge. -/
  gamma : Option Nat := none
  /-- Whether the C++ reduces the batch's opening claim by the masked bit sumcheck
  (`GordieHowe.FieldProof.MaskedReduction.bitSumcheck`). Every batch on bits takes the bit sumcheck, and
  the domain's batch check (`GordieHowe.RealizedProgram.BatchesOk`) requires this flag on every
  covered batch on bits, so an export whose C++ skips it is rejected. -/
  bitSumcheck : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- **A realization circuit**: a lowering's own circuit, not a predicate of the realized program. `logup table group`:
the LogUp sum of group `group` of lookup table `table` (`range.lookup:<D>.<T>[.g<k>]`); `macH pred`:
the H part of the cross-field `equal` `pred` stated by the compiler's own circuit (the non-affine
`<mac>.H`); `named name`: a realization circuit by its C++ name; `unmodeled k`: a realization
circuit the program does not model (an `assert_in` lookup, `<table>.lookup`). -/
inductive RealCircuit where
  /-- The LogUp sum of a table group. -/
  | logup (table group : Nat)
  /-- The H part of a cross-field `equal`. -/
  | macH (pred : Nat)
  /-- A realization circuit by its C++ name. -/
  | named (name : String)
  /-- The `k`-th realization circuit the program does not model (an `assert_in` lookup). -/
  | unmodeled (k : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- A C++ name read as a realization circuit (`RealCircuit.named`). -/
instance : Coe String RealCircuit := ⟨.named⟩

/-- **A public input only a realization circuit reads**: `weights table`, the weights `1/(α − j)`,
`j < T`, of lookup table `table` (`range.weights:<D>.<T>`); `named name`: a realization input by its
C++ name; `unmodeled k`: an input only an unmodeled realization circuit reads. -/
inductive RealPub where
  /-- The lookup weights of a table. -/
  | weights (table : Nat)
  /-- A realization input by its C++ name. -/
  | named (name : String)
  /-- The `k`-th input only an unmodeled realization circuit reads. -/
  | unmodeled (k : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- A C++ name read as a realization input (`RealPub.named`). -/
instance : Coe String RealPub := ⟨.named⟩

/-- **A block of a GKR circuit's input layout**, with its first input `at` and length `n`: a public
input (a statement value, a constant value, a public computation or expression, a challenge, or the
message of late value `v`), a public input only a realization circuit reads (`realizationPub`: the
lookups' weights), the committed coordinates of a value (a phase-0 cell or the MAC's blind), the pad
of late value `v`, the bits of a bit view, the pads of a batch's zerocheck, or alignment filler
(each input zero). -/
inductive InputBlock where
  /-- A public input. -/
  | pub (v «at» n : Nat)
  /-- A public input of a realization circuit. -/
  | realizationPub (w : RealPub) («at» n : Nat)
  /-- Committed coordinates. -/
  | committed (v «at» n : Nat)
  /-- The pad of a late value. -/
  | pad (v «at» n : Nat)
  /-- A bit view. -/
  | view (v «at» n : Nat)
  /-- The pads of batch `b`. -/
  | batchPads (b «at» n : Nat)
  /-- Filler. -/
  | filler («at» n : Nat)
  deriving Repr, DecidableEq, Inhabited

namespace InputBlock

/-- The first input of a block. -/
def first : InputBlock → Nat
  | .pub _ a _ | .realizationPub _ a _ | .committed _ a _ | .pad _ a _ | .view _ a _
  | .batchPads _ a _ | .filler a _ => a

/-- The length of a block. -/
def len : InputBlock → Nat
  | .pub _ _ n | .realizationPub _ _ n | .committed _ _ n | .pad _ _ n | .view _ _ n
  | .batchPads _ _ n | .filler _ n => n

/-- **Block `b` holds input `q`**: `q` lies in `[first, first + len)`. -/
def Holds (q : Nat) (b : InputBlock) : Prop := b.first ≤ q ∧ q < b.first + b.len

/-- Whether a block is public. -/
def isPublic : InputBlock → Bool
  | .pub _ _ _ | .realizationPub _ _ _ => true
  | _ => false

/-- Whether a block is the public input of value `v`. -/
def isPubOf (v : Nat) : InputBlock → Bool
  | .pub u _ _ => u == v
  | _ => false

/-- Whether a block is the committed coordinates of value `v`. -/
def isCommittedOf (v : Nat) : InputBlock → Bool
  | .committed u _ _ => u == v
  | _ => false

/-- Whether a block is the pad of late value `v`. -/
def isPadOf (v : Nat) : InputBlock → Bool
  | .pad u _ _ => u == v
  | _ => false

/-- Whether a block is bit view `v`. -/
def isViewOf (v : Nat) : InputBlock → Bool
  | .view u _ _ => u == v
  | _ => false

end InputBlock

/-- **An entry of a GKR circuit's emission order**: a Boolean check (the realized program's predicate `p`), the zero
checks of `n` alignment inputs, a predicate placed in the circuit, or a lowering's own circuit
(`RealCircuit`). -/
inductive CircuitEntry where
  /-- A Boolean check. -/
  | typeCheck (p : Nat)
  /-- Alignment zero checks. -/
  | alignment (n : Nat)
  /-- A placed predicate. -/
  | pred (p : Nat)
  /-- A realization circuit. -/
  | realization (r : RealCircuit)
  deriving Repr, DecidableEq, Inhabited

/-- **A GKR circuit** of a domain: the predicates it enforces, exhaustively, in emission order; the
whole emission order; its input layout as positioned blocks, contiguous from input `1` (input `0` is
the constant one), the public blocks being inputs `1` to `publicInputs − 1`; its input count; and
its shape for `ShapeAtMost`. -/
structure Circuit where
  /-- The name. -/
  name : String
  /-- The domain. -/
  domain : Nat
  /-- The predicates. -/
  predicates : List Nat
  /-- The emission order. -/
  entries : List CircuitEntry := []
  /-- The input layout. -/
  inputs : List InputBlock
  /-- The public inputs, the constant one included. -/
  publicInputs : Nat := 1
  /-- The input count. -/
  inputCount : Nat := 1
  /-- The layers. -/
  layers : Nat := 0
  /-- The wires. -/
  wires : Nat := 0
  /-- The quadratic terms. -/
  terms : Nat := 0
  deriving Repr, DecidableEq, Inhabited

/-! ## The program -/

/-- **A member check of the statement**: a statement member's codec check `m.check(id, pred)`
(`lib/gordiehowe/relation.h`): the member's name (`hhat`, `ring`; a record's member dotted), its
canonical bytes `[offset, offset + bytes)` in the statement's bytes, and the check's id and naturals
(`computes(check, args)`). The meaning of the known ids is `MemberCheck.kind?` and
`RealizedProgram.MemberHolds`. -/
structure MemberCheck where
  /-- The member's name. -/
  member : String
  /-- The first byte of the member in the statement's bytes. -/
  offset : Nat
  /-- The member's number of bytes. -/
  bytes : Nat
  /-- The check's id. -/
  check : String
  /-- The check's naturals. -/
  args : List Nat := []
  deriving Repr, DecidableEq, Inhabited

/-- **The meaning of a member check**: the C++ codec check `m.check(id, pred)` that its id and
naturals name (`MemberCheck.kind?`).

* `below q w`: every coordinate of the member's value, read as a natural, is below `q`, the member
  stored in `w`-byte entries;
* `p256Point`: the member's value is the two coordinates `(x, y)` of an affine point of P-256,
  `y² = x³ + a x + b` (`p256A`, `p256B`), in 32-byte entries;
* `limbBits b w L`: the value is `L` limbs `n_i` below `2^w` of an integer
  `N = Σ_i n_i 2^(w i)` of exactly `b` bits, `2^(b−1) ≤ N < 2^b`, decoded from the member's
  `b / 8` bytes. -/
inductive MemberCheck.Kind where
  /-- Every coordinate below `q`, in `w`-byte entries. -/
  | below (q w : Nat)
  /-- An affine point of P-256. -/
  | p256Point
  /-- `L` limbs of `w` bits of a `b`-bit integer. -/
  | limbBits (b w L : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- **The kind of a member check** (`MemberCheck.Kind`), from the C++ checks:

* the Falcon statements' (`lib/gordiehowe/examples/falcon/falcon_emulated.h`, `falcon_ring.h`):
  `falcon_key_canonical [q]`, `falcon_challenge_canonical [q]` and `falcon_ring_key_u16le [n, q]`
  (`n` the coefficients of one key) accept 16-bit little-endian entries below `q`;
* the ECDSA mDL's (`lib/gordiehowe/examples/mdoc/mdoc_signatures.h`, `mdoc_signature_inputs`):
  `p256_affine_point []` accepts the issuer key `(x, y)` when `p256.is_on_curve(x, y)`
  (`third_party/longfellow/lib/ec/elliptic_curve.h`: `y² = x³ + a x + b` in `F_p256`), and
  `u128_halves []` accepts `e2`'s halves when the two upper 64-bit limbs of each canonical
  element are zero, that is each below `2^128`;
* RSA's (`lib/gordiehowe/examples/rsa/rsa_pkcs1.h`, `rsa_key`): `rsa_modulus_2048 [2048, w, L]`
  accepts the modulus's 256 big-endian bytes when the top bit is set, recorded against the
  statement value `key.n` the verifier computes from them, its `L` limbs of `w` bits
  (`rsa_digits`): `N` has exactly 2048 bits.

Any other check gives `none`, which validity rejects. -/
def MemberCheck.kind? (m : MemberCheck) : Option MemberCheck.Kind :=
  match m.check, m.args with
  | "falcon_key_canonical", [q] => some (.below q 2)
  | "falcon_challenge_canonical", [q] => some (.below q 2)
  | "falcon_ring_key_u16le", [_, q] => some (.below q 2)
  | "u128_halves", [] => some (.below (2 ^ 128) 32)
  | "p256_affine_point", [] => some .p256Point
  | "rsa_modulus_2048", [b, w, L] => some (.limbBits b w L)
  | _, _ => none

/-- **The bound of a member check on its entries**: `some q` for a check that accepts a member
whose every coordinate is below `q` (`MemberCheck.Kind.below`), `none` for any other. -/
def MemberCheck.entryBound? (m : MemberCheck) : Option Nat :=
  match m.kind? with
  | some (.below q _) => some q
  | _ => none

/-- **The prime of P-256's base field** `F_p256` (SEC 2 v2.0, §2.4.2, `secp256r1`;
`third_party/longfellow/lib/ec/p256.h`). -/
def p256Prime : Nat :=
  115792089210356248762697446949407573530086143415290314195533631308867097853951

/-- **The coefficient `a = −3` of P-256**, as the natural `p − 3` (SEC 2 v2.0, §2.4.2, `secp256r1`;
`third_party/longfellow/lib/ec/p256.cc`). -/
def p256A : Nat :=
  115792089210356248762697446949407573530086143415290314195533631308867097853948

/-- **The coefficient `b` of P-256** (SEC 2 v2.0, §2.4.2, `secp256r1`;
`third_party/longfellow/lib/ec/p256.cc`). -/
def p256B : Nat :=
  41058363725152142129326129780047268409114441015993725554835256314039467401291

/-- **The statement's parameters**: the message and context lengths in bytes, and the member checks
in declaration order (`[]` when no member has one). A statement a check refuses is rejected before
the transcript starts (`RealizedProgram.StatementOk`). -/
structure StatementHeader where
  /-- The message length. -/
  msgLen : Nat := 0
  /-- The context length. -/
  ctxLen : Nat := 0
  /-- The member checks. -/
  checks : List MemberCheck := []
  deriving Repr, DecidableEq, Inhabited

/-- **A convolution realized through a negacyclic transform** (compiler/conv.h, the batch form):
`B` acyclic convolutions `conv(a, b)` of operand rows of lengths `la` and `lb`, the shared
expression `source` (`.apply (.sum la) (.mul (.reindex (IndexMap.convLeft B la lb) (.concat a 0))
(.reindex (IndexMap.convRight B la lb) (.concat b 0)))`), read as the shared expression `read`,
the first `la + lb − 1` coordinates of each block of `INTT_M(z)` (`.reindex (IndexMap.blockPrefix B
M (la + lb − 1)) (.apply (.batched B (.inverseNtt M ψ)) (.leaf z))`), where the predicate
`products` states `z = NTT_M(a) · NTT_M(b)` on the operands zero-extended to `M`, at the root `ψ`
(the natural of the C++ encoding). The checks are `RealizedProgram.convOkB`. -/
structure SpectralConv where
  /-- The shared expression of the source convolution. -/
  source : Nat
  /-- The shared expression reading it through the transform. -/
  read : Nat
  /-- The predicate of the spectral products. -/
  products : Nat
  /-- The blocks `B`. -/
  blocks : Nat
  /-- The left operand's length `la`. -/
  left : Nat
  /-- The right operand's length `lb`. -/
  right : Nat
  /-- The transform length `M`. -/
  length : Nat
  /-- The root `ψ`. -/
  root : Nat
  deriving Repr, DecidableEq, Inhabited

/-- **The realized program of a plan**: the phases, the statement's parameters, fields, domains,
values, shared expressions, predicates, lookup tables, challenges, messages (in `MsgBefore`
order), batches, GKR circuits, the realization circuits (the compiler's own circuits,
with their domains; not predicates of the realized program), and the spectrally realized
convolutions. -/
structure _root_.GordieHowe.RealizedProgram where
  /-- The number of challenge phases. -/
  phases : Nat
  /-- The statement's parameters. -/
  statement : StatementHeader := {}
  /-- The fields. -/
  fields : List FieldDecl
  /-- The domains. -/
  domains : List DomainDecl
  /-- The values. -/
  values : List Value
  /-- The shared expressions. -/
  exprs : List Expr := []
  /-- The predicates. -/
  predicates : List Predicate
  /-- The lookup tables. -/
  tables : List Table := []
  /-- The challenges. -/
  challenges : List Challenge := []
  /-- The messages. -/
  messages : List Message := []
  /-- The batches. -/
  batches : List Batch := []
  /-- The GKR circuits. -/
  circuits : List Circuit := []
  /-- The realization circuits, with their domains. -/
  realizationCircuits : List (RealCircuit × Nat) := []
  /-- The convolutions realized through a transform. -/
  convs : List SpectralConv := []
  deriving Repr

section

variable (ir : RealizedProgram)

/-- Value `v` (a default value when out of range). -/
def value (v : Nat) : Value := ir.values.getD v default

/-- Predicate `p`. -/
def predicate (p : Nat) : Predicate := ir.predicates.getD p default

/-- Challenge `c`. -/
def challenge (c : Nat) : Challenge := ir.challenges.getD c default

/-- Domain `d`. -/
def domain (d : Nat) : DomainDecl := ir.domains.getD d default

/-- Field `f`. -/
def field (f : Nat) : FieldDecl := ir.fields.getD f default

/-- Lookup table `t`. -/
def table (t : Nat) : Table := ir.tables.getD t default

/-- Shared expression `k`. -/
def expr (k : Nat) : Expr := ir.exprs.getD k default

/-- Batch `b`. -/
def batch (b : Nat) : Batch := ir.batches.getD b default

/-- Circuit `c`. -/
def circuit (c : Nat) : Circuit := ir.circuits.getD c default

/-- The field of domain `d`. -/
def domainField (d : Nat) : Nat := (ir.domain d).field

/-- The field of value `v`: `Value.field` for a value of a field no domain commits (the odd–odd
MAC's key powers, tag and message: a kind `Kind.allowsField` allows), its domain's field otherwise.
A value of any other kind has its domain's field whatever its `field` (validity rejects a `field` on
it, `RealizedProgram.FieldOk`). -/
def valueField (v : Nat) : Nat :=
  match (ir.value v).kind.allowsField, (ir.value v).field with
  | true, some f => f
  | _, _ => ir.domainField (ir.value v).domain

/-- **A value of a kind that lies in its domain has its domain's field.** -/
theorem valueField_of_allowsField {v : Nat} (hk : (ir.value v).kind.allowsField = false) :
    ir.valueField v = ir.domainField (ir.value v).domain := by
  simp [valueField, hk]

/-- **A value outside every domain has its domain's field.** -/
theorem valueField_of_field_none {v : Nat} (h : (ir.value v).field = none) :
    ir.valueField v = ir.domainField (ir.value v).domain := by
  unfold valueField
  rw [h]
  split <;> simp_all

/-- **A value of a field no domain commits has that field.** -/
theorem valueField_of_field_some {v f : Nat} (hk : (ir.value v).kind.allowsField = true)
    (h : (ir.value v).field = some f) : ir.valueField v = f := by
  simp [valueField, hk, h]

/-- The field of challenge `c`. -/
def chalField (c : Nat) : Nat := (ir.challenge c).field

/-- **Whether value `v` is the statement member `member`**: a public opaque value of no argument
named `statement.<member>` (the member decoded from its slice of the statement's bytes; the export
names a statement member's value so), or named `member` itself (a statement value the verifier
computes from a member, against which the export records the member's check, `In::check_value`). -/
def isMemberOf (member : String) (v : Nat) : Bool :=
  match (ir.value v).kind with
  | .pub (.«opaque» name []) => name == "statement." ++ member || name == member
  | _ => false

/-- **The value of the statement member `member`**: the first value that is it (`isMemberOf`). -/
def memberValue? (member : String) : Option Nat :=
  (List.range ir.values.length).find? (ir.isMemberOf member)

end

end GordieHowe.RealizedProgram
