-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Std.Data.HashMap

@[expose] public section

/-!
# GordieHowe: the data types of the GKR circuit certificates

The types of the exported circuit data and its certificates, which the `.ghc` decoders build
(`GordieHoweNative/Ghc.lean`, derived per type in `GordieHoweNative/Codecs.lean`). They import no
Mathlib so that the library `GordieHoweNative` is compiled to native code that every module
importing it loads (`precompileModules`): the loader and native mode's run-time reader then decode
a certificate file in compiled code instead of Lean's interpreter. The
modules that define the operations on each type import this one; the declarations keep their
names.
-/

namespace GordieHowe.RealizedProgram

/-- **An index map**: runs of arithmetic progressions, `(start, step, count)` standing for `start,
start + step, …, start + (count − 1)·step`; the map is the concatenation of its runs' entries
(`IndexMap.toList`), entry `i` read off the run containing it (`IndexMap.entry`). -/
abbrev IndexMap : Type := List (Nat × Int × Nat)

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
primitive `2n`-th root of unity) in scheme order or in natural order. -/
inductive ConvForm where
  /-- The coefficients. -/
  | coefficients
  /-- The transform at `psi`, in scheme order. -/
  | ntt (psi : Nat)
  /-- The transform at `psi`, in natural order. -/
  | nttNatural (psi : Nat)
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

end GordieHowe.RealizedProgram

namespace GordieHowe.GKR.Rel

open GordieHowe.RealizedProgram

/-- **A wire** `c0 + c1 · n`: the codes `c0`, `c1` and the DAG node `n` (the C++ `BitW`). -/
structure Wire where
  /-- The constant term's code. -/
  c0 : Nat
  /-- The coefficient's code. -/
  c1 : Nat
  /-- The DAG node. -/
  n : Nat
  deriving Repr, DecidableEq, Inhabited

/-- **Where a value leaf of the node table reads its value** in its circuit (the placement
pointers): the checker reads the named block or node and checks it holds the value. -/
inductive Place where
  /-- Input block `b` of the circuit holds the value: its committed block (a committed value or a
  pad copy), its view block (a bit view), or its public block (any public value: a statement
  value, a constant, a public expression, a challenge, a message). -/
  | block (b : Nat)
  /-- A late value: the public block `pub` of its message value and its pad block `pad`; the
  value is message minus pad. -/
  | late (pub pad : Nat)
  /-- A value read through its definition (a source value bound to its digits, `.bound e`; a
  public expression the circuit computes, `.pub (.expr e)`): node `x` of the table computes `e`. -/
  | defined (x : Nat)
  deriving Repr, DecidableEq, Inhabited

end GordieHowe.GKR.Rel

namespace GordieHowe.GKR.Certificate

open GordieHowe.RealizedProgram GordieHowe.GKR.Rel

/-- A binary trie of chunks keyed by natural numbers, least significant bit first. -/
inductive NTree where
  | nil
  | leaf (c : Nat)
  | node (l r : NTree)

/-- A depth's node table: the identity (the inputs: wire `i` carries node `i`), or packed
`w`-bit entries, `2 ^ e` to a chunk, the chunks in a trie by chunk index, so an access is a trie
descent and a shift within one bounded chunk. -/
inductive Table where
  | ident
  | packed (e : Nat) (tree : NTree)

/-- The layered circuit: input count and each layer's gate chunks in wire order, from the
first layer above the inputs to the output layer. -/
structure Layered where
  /-- The number of inputs. -/
  inputs : Nat
  /-- The layers' gates. -/
  layers : List (List Nat)

/-- The certificate: the encoding width, each layer's node table (aligned with the layers; the
inputs' is the identity), and the last-layer assertions `(wire, node)`. -/
structure Cert where
  /-- Field width in bits. -/
  width : Nat
  /-- The layers' node tables. -/
  tables : List Table
  /-- Output wires and the assertion node each discharges. -/
  outputs : List (Nat × Nat)
  /-- The output wire of each of the DAG's output nodes, aligned with them. -/
  outWires : List Nat

end GordieHowe.GKR.Certificate

namespace GordieHowe.RealizedProgram

open GordieHowe.GKR.Rel GordieHowe.GKR.Certificate

/-- **The combine of a chain** (`ExprOp` `kAdd kMul kAnd kOr kXor`, `lib/gordiehowe/expr.h`). -/
inductive BinOp where
  /-- `kAdd`. -/
  | add
  /-- `kMul`. -/
  | mul
  /-- `kAnd`. -/
  | and
  /-- `kOr`. -/
  | or
  /-- `kXor`. -/
  | xor
  deriving Repr, DecidableEq, Inhabited

/-- **A word comparison** (`ExprOp` `kLt kLeq kEq`). -/
inductive CmpOp where
  /-- `kLt`. -/
  | lt
  /-- `kLeq`. -/
  | leq
  /-- `kEq`. -/
  | eq
  deriving Repr, DecidableEq, Inhabited

/-- **The second operand of a comparison**: a node, or an immediate constant `v` whose bits the
printer reads by the index map `idx`. -/
inductive CmpArg where
  /-- Node `k`. -/
  | node (k : Nat)
  /-- The constant value `v`, read by `idx`. -/
  | imm (v : Nat) (idx : IndexMap)
  deriving Repr, DecidableEq, Inhabited

/-- **An operator a circuit expands** (`expand_operator`, `lib/gordiehowe/expr.h`). -/
inductive EOp where
  /-- A gather, `zero_extend` or batched view by `idx`, over the operand followed by the constant
  value `z` of one zero when a row is empty (`zero = some z`). -/
  | view (idx : IndexMap) (zero : Option Nat)
  /-- A named operator with constant rows. -/
  | named (op : NamedOp)
  /-- An unnamed sparse matrix. -/
  | sparse (rows : List (List (Nat × Coef)))
  /-- A staged transform (`.ntt` or its `.batched` form) with its stage mask. -/
  | staged (op : NamedOp) (mask : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- **A term of an affine leaf** (`Term<F>`, `lib/gordiehowe/expr.h`): its scale's code, the node of
its value's view, and its chain of operators, applied first to last. -/
structure ETerm where
  /-- The scale's code. -/
  scale : Nat
  /-- The view's node. -/
  view : Nat
  /-- The operators. -/
  ops : List EOp
  deriving Repr, DecidableEq, Inhabited

/-- **A node of the emitted DAG.** The expression nodes are the `ExprOp`s of
`ExprEmitter::operator()` (`lib/gordiehowe/expr.h`); the leaf is a value read through its
placement (`CompiledDomain::view`, `lib/gordiehowe/compiler/compiled_domain.h`). Kid ids are below
the node's own id. The constructor numbers are the binary certificate's tags. -/
inductive ENode where
  /-- `kLin`: an affine combination of terms, printed as the constant value `zeros` when it has
  none. -/
  | lin (terms : List ETerm) (zeros : Nat)
  /-- `kConst`: the constant value `v`. -/
  | const (v : Nat)
  /-- A chain combine `kAdd kMul kAnd kOr kXor` of nodes `a`, `b`, as built. -/
  | bin (op : BinOp) (a b : Nat)
  /-- `kScale` by the code `c`. -/
  | scale (c a : Nat)
  /-- `kSum` in groups of `w` (the printed group width: the operand's length for one total). -/
  | sum (w a : Nat)
  /-- `kProd` in groups of `w`. -/
  | prod (w a : Nat)
  /-- `kBroadcast` of a node of length one by `idx`. -/
  | broadcast (idx : IndexMap) (a : Nat)
  /-- `kNot`, `ones` the constant value of ones it is printed with. -/
  | lnot (ones a : Nat)
  /-- `kMux` with its `bit` flag (the Bit form against the field form). -/
  | mux (bit : Bool) (c t e : Nat)
  /-- `kLt kLeq kEq` on words of `w` bits. -/
  | cmp (op : CmpOp) (w a : Nat) (b : CmpArg)
  /-- `kAny` (`any = true`) or `kAll` on words of `w` bits. -/
  | tree (any : Bool) (w a : Nat)
  /-- `kMaterialize`. -/
  | materialize (a : Nat)
  /-- `kGather` of the parts by `idx`. -/
  | gather (idx : IndexMap) (parts : List Nat)
  /-- `kApply` of an operator. -/
  | apply (op : EOp) (a : Nat)
  /-- Value `u` read through its placement `pl` (`GKR.Rel.Place`): an input block, a late value's
  message and pad blocks, or the node computing its definition. -/
  | value (u : Nat) (pl : GKR.Rel.Place)
  deriving Repr

/-- **A node of the table with what the printer drops**: its length; `cut`, a check point the
compiler marked (an operand the relational check needs as an atom, an entry root, a leaf, or a node
read by more than one parent: only a cut node carries wires); `ref`, the shared expression
it is printed as; per coordinate, the wire the emitter produced for it (`wires`, `len` of them);
and the wires of its own emission that feed a product and are no kid's wire (`aux`). -/
structure ENodeInfo where
  /-- The node. -/
  node : ENode
  /-- Its length. -/
  len : Nat
  /-- A check point: the node carries its wires. -/
  cut : Bool := true
  /-- The shared expression it is printed as. -/
  ref : Option Nat := none
  /-- The wire of each coordinate. -/
  wires : List GKR.Rel.Wire
  /-- The wires of its emission that feed a product, coordinate-major. -/
  aux : List GKR.Rel.Wire := []
  deriving Repr

/-- **A binary trie keyed by natural numbers**, least significant bit first (as
`GKR.Certificate.NTree`); the default where a key has no entry. -/
inductive Trie (α : Type) where
  /-- No entry. -/
  | nil
  /-- One entry for every remaining key. -/
  | leaf (x : α)
  /-- The even keys left, the odd keys right. -/
  | node (l r : Trie α)
  deriving Repr

/-- **The node table of one circuit's emission**: its node count and its nodes by id. -/
structure ETable where
  /-- The node count. -/
  size : Nat
  /-- The nodes by id. -/
  tree : Trie ENodeInfo

end GordieHowe.RealizedProgram

namespace GordieHowe.GKR.Rel

open GordieHowe.RealizedProgram GordieHowe.GKR.Certificate

/-- **The assertion of one coordinate of an entry's root**: the asserted DAG node `Z`, whose
assertion term `0 · 1 · U` reads the node `U` (the root's wire, materialized). `Z = 0` marks an
assertion the compiler folded away (the root's wire is zero); `U` is then `0`. -/
structure Assert where
  /-- The asserted node (`0`: folded away). -/
  Z : Nat
  /-- The node its assertion term reads. -/
  U : Nat
  deriving Repr, DecidableEq, Inhabited

end GordieHowe.GKR.Rel

namespace GordieHowe.GKR.Certificate

open GordieHowe.RealizedProgram GordieHowe.GKR.Rel

/-- The DAG: the nodes below `inputs` are the inputs (node `i` the input `i`, as Longfellow
numbers them when every input precedes every gate), the other nodes' chunks by id, the bound on
node ids, and the asserted nodes. -/
structure Dag where
  /-- The node chunks by id. -/
  tree : NTree
  /-- The number of inputs. -/
  inputs : Nat
  /-- Every node id is below `size`. -/
  size : Nat
  /-- The asserted nodes. -/
  asserts : List Nat
  /-- The output nodes (each must be zero). -/
  outputs : List Nat

end GordieHowe.GKR.Certificate

namespace GordieHowe.GKR.Rel

open GordieHowe.RealizedProgram GordieHowe.GKR.Certificate

/-- **An inner node of a fraction tree**: its kids `l` and `r`, indices into the tree's fractions
(the leaves `0, …, n − 1`, then the inner nodes from `n` in record order), and the wires of its
numerator and denominator. -/
structure Frac where
  /-- The left kid. -/
  l : Nat
  /-- The right kid. -/
  r : Nat
  /-- The numerator's wire. -/
  num : Wire
  /-- The denominator's wire. -/
  den : Wire
  deriving Repr, DecidableEq, Inhabited

/-- **A fraction tree as the compiler built it**: per leaf the wire of its denominator (its
numerator is one), then the inner nodes, the root last (the one leaf when there are no inner
nodes). -/
structure FracTree where
  /-- The leaves' denominators. -/
  dens : List Wire
  /-- The inner nodes. -/
  inner : List Frac
  deriving Repr, DecidableEq, Inhabited

/-- **The record of a range LogUp entry** (group `g` of table `t`, named by the entry itself). -/
structure LogupCert where
  /-- The table node of `α`'s view. -/
  alpha : Nat
  /-- Per member of the group, in member order, the table node of its needle's view. -/
  needles : List Nat
  /-- The table nodes of the static, then the late histogram's view (the present ones). -/
  hists : List Nat
  /-- The circuit's input block of the weights (`.realizationPub (.weights t) a T`). -/
  weights : Nat
  /-- The fraction tree over the needles. -/
  tree : FracTree
  /-- The wire of `S = Σ_h Σ_j m_h[j] · w_j`. -/
  sum : Wire
  deriving Repr, DecidableEq, Inhabited

/-- **The record of a MAC H entry** (`.macH p`). -/
structure MacHCert where
  /-- The table node of the H operand's view, `chunks · width` coordinates. -/
  bits : Nat
  /-- The table node of the powers' view. -/
  powers : Nat
  /-- The table node of the tag's view. -/
  tag : Nat
  /-- Per chunk `c`, the wire of `chunk_c`. -/
  chunks : List Wire
  deriving Repr, DecidableEq, Inhabited

/-- **The family record of an entry**: the filler block an alignment entry asserts, a range
LogUp's record, a MAC H's record. -/
inductive FamCert where
  /-- An alignment entry's filler block (an index into the circuit's inputs). -/
  | alignment (block : Nat)
  /-- A range LogUp. -/
  | logup (lc : LogupCert)
  /-- A MAC H half. -/
  | macH (mc : MacHCert)
  deriving Repr, DecidableEq, Inhabited

/-- **The certificate block of one circuit entry.**

* `entry`: the entry's index in the circuit's entries (`Circuit.entries`).
* `lo`, `hi`: the node ids `[lo, hi)` the entry introduced. Ids are assigned in completion order, so
  an entry's new nodes are contiguous; the blocks of a circuit's entries partition `[0, size)` of
  its node table, in entry order.
* `root`: the asserted root node (`none` for an alignment or realization entry, whose assertions
  read filler inputs or the family's item).
* `asserts`: per coordinate of the root (or per filler input of an alignment entry), the assertion
  pair, in coordinate order; a realization entry's one pair.
* `fam`: the family record of an alignment or realization entry. -/
structure EntryCert where
  /-- The entry's index in the circuit's entries. -/
  entry : Nat
  /-- The first node id the entry introduced. -/
  lo : Nat
  /-- One past the last node id the entry introduced. -/
  hi : Nat
  /-- The asserted root (`none`: an alignment entry). -/
  root : Option Nat
  /-- The assertion pairs, by coordinate. -/
  asserts : List Assert
  /-- The family record (`none`: a placed or Boolean entry). -/
  fam : Option FamCert := none
  deriving Repr, Inhabited

end GordieHowe.GKR.Rel

namespace GordieHowe.GKR.Fold

open GordieHowe.RealizedProgram GordieHowe.GKR.Rel GordieHowe.GKR.Certificate

/-- **The constant table**: the code of every constant index, `width`-bit entries in a packed
table (`Table`). -/
structure Consts where
  /-- The entries' width in bits. -/
  width : Nat
  /-- The codes by constant index. -/
  table : Table

end GordieHowe.GKR.Fold

namespace GordieHowe.RealizedProgram

open GordieHowe.GKR.Rel GordieHowe.GKR.Certificate GordieHowe.GKR.Fold

/-- **The certificate of one GKR circuit**, as the generated module loads it: the circuit's index,
the term width of its DAG and schedule, the field's characteristic, the fast path's prime (`0`:
none), the characteristic-two flag, the codes of `−1` and `1/2`, the constant table, the DAG, the
layered circuit, the scheduling certificate, the node table and the entries' blocks. -/
structure CircuitData where
  /-- The circuit's index. -/
  c : Nat
  /-- The term width of `dag` and `sched`. -/
  w : Nat
  /-- The field's characteristic. -/
  chr : Nat
  /-- The fast path's prime (`0`: none). -/
  prime : Nat
  /-- Whether the field has characteristic two. -/
  char2 : Bool
  /-- The code of `−1`. -/
  neg1 : Nat
  /-- The code of `1/2` (`0` in characteristic two). -/
  half : Nat
  /-- The constant table. -/
  consts : Consts
  /-- The DAG. -/
  dag : Dag
  /-- The layered circuit. -/
  layered : Layered
  /-- The scheduling certificate. -/
  sched : Cert
  /-- The node table. -/
  table : ETable
  /-- The entries' blocks. -/
  entries : List EntryCert

end GordieHowe.RealizedProgram
