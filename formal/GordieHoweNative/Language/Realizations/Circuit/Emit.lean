-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.Realizations.RealizeLookup
public import GordieHoweNative.ProofSystem.GKR.RelCert

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.Realizations.Circuit.Emit`

The definitions of `GordieHowe.Language.Realizations.Circuit.Emit` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/Realizations/Circuit/Emit.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

mutual

/-- **The expression with every reference `ref k` replaced by `g k`.** -/
def Expr.substRefs (g : ℕ → Expr) : Expr → Expr
  | .leaf v => .leaf v
  | .add e e' => .add (e.substRefs g) (e'.substRefs g)
  | .sub e e' => .sub (e.substRefs g) (e'.substRefs g)
  | .scale c e => .scale c (e.substRefs g)
  | .mul e e' => .mul (e.substRefs g) (e'.substRefs g)
  | .reindex idx e => .reindex idx (e.substRefs g)
  | .concat e e' => .concat (e.substRefs g) (e'.substRefs g)
  | .linear rows e => .linear rows (e.substRefs g)
  | .prod n e => .prod n (e.substRefs g)
  | .mux b t e => .mux (b.substRefs g) (t.substRefs g) (e.substRefs g)
  | .apply op e => .apply op (e.substRefs g)
  | .ref k => g k
  | .logic op w args => .logic op w (Expr.substRefsList g args)

/-- The expressions of a list with every reference `ref k` replaced by `g k`. -/
def Expr.substRefsList (g : ℕ → Expr) : List Expr → List Expr
  | [] => []
  | e :: es => e.substRefs g :: Expr.substRefsList g es

end

/-- **What the table's checks read besides the table**: the constant table (index to code), the
code arithmetic, the codes of `−1` and of `1/2`, whether the field has characteristic two, and the
number of circuit inputs (the DAG nodes below it are the inputs). -/
structure TEnv where
  /-- The constant table: the code of the constant of an index. -/
  consts : GKR.Fold.Consts
  /-- The code arithmetic. -/
  ar : GKR.Fold.CodeArith
  /-- The code of `−1`. -/
  neg1 : ℕ
  /-- The code of `1/2` (read in odd characteristic only). -/
  half : ℕ
  /-- Whether the field has characteristic two. -/
  char2 : Bool
  /-- The number of inputs. -/
  inputs : ℕ

/-- The Logic builder of a comparison. -/
def CmpOp.logic : CmpOp → LogicOp
  | .lt => .lt
  | .leq => .leq
  | .eq => .eq

/-- **The printed form of an operator around its operand `x`.** -/
def EOp.wrap : EOp → Expr → Expr
  | .view idx none, x => .reindex idx x
  | .view idx (some z), x => .reindex idx (.concat x (.leaf z))
  | .named op, x => .apply op x
  | .sparse rows, x => .linear rows x
  | .staged op _, x => .apply op x

/-- **A term's printed form**, its view written `.ref view`: the operators around the view, scaled
by `.scale (.const scale)` unless the scale's code is `1`. -/
def ETerm.row (t : ETerm) : Expr :=
  cond (Nat.beq t.scale 1) (t.ops.foldl (fun x op => op.wrap x) (.ref t.view))
    (.scale (.const t.scale) (t.ops.foldl (fun x op => op.wrap x) (.ref t.view)))

/-- **An affine combination's printed form**: the terms left-nested by `.add`, the constant value
`z` when there is no term. -/
def linRow : List ETerm → ℕ → Expr
  | [], z => .leaf z
  | t :: ts, _ => ts.foldl (fun acc t' => .add acc t'.row) t.row

/-- **A concatenation's printed form**, right-nested; one part alone; `.leaf 0` for none. -/
def concatRow : List Expr → Expr
  | [] => .leaf 0
  | [x] => x
  | x :: y :: xs => .concat x (concatRow (y :: xs))

/-- The default node, an empty gather: no kids, length `0`. -/
instance : Inhabited ENode := ⟨.gather [] []⟩

/-- **A node's printed form one level deep**, each kid `a` written `.ref a`, in the field whose
characteristic-two flag and code of `2` the environment holds. -/
def ENode.row (env : TEnv) : ENode → Expr
  | .lin ts z => linRow ts z
  | .const v => .leaf v
  | .bin .add a b => .add (.ref a) (.ref b)
  | .bin .mul a b => .mul (.ref a) (.ref b)
  | .bin .and a b => .mul (.ref a) (.ref b)
  | .bin .or a b => .sub (.add (.ref a) (.ref b)) (.mul (.ref a) (.ref b))
  | .bin .xor a b =>
    cond env.char2 (.add (.ref a) (.ref b))
      (.sub (.add (.ref a) (.ref b)) (.scale (.const (env.ar.add 1 1)) (.mul (.ref a) (.ref b))))
  | .scale c a => cond (Nat.beq c 1) (.ref a) (.scale (.const c) (.ref a))
  | .sum w a => .apply (.sum w) (.ref a)
  | .prod w a => .prod w (.ref a)
  | .broadcast idx a => .reindex idx (.ref a)
  | .lnot o a => .sub (.leaf o) (.ref a)
  | .mux _ c t e => .mux (.ref c) (.ref t) (.ref e)
  | .cmp op w a (.node b) => .logic op.logic w [.ref a, .ref b]
  | .cmp op w a (.imm v idx) => .logic op.logic w [.ref a, .reindex idx (.leaf v)]
  | .tree any w a => .logic (cond any .any .all) w [.ref a]
  | .materialize a => .ref a
  | .gather idx ps => .reindex idx (concatRow (ps.map Expr.ref))
  | .apply op a => op.wrap (.ref a)
  | .value u _ => .leaf u

/-- The default entry: the default node, of length `0`, with no wires. -/
instance : Inhabited ENodeInfo := ⟨⟨default, 0, false, none, [], []⟩⟩

/-- The entry at key `k`. -/
def Trie.get {α : Type} [Inhabited α] : Trie α → ℕ → α
  | .nil, _ => default
  | .leaf x, _ => x
  | .node l r, k => cond (Nat.beq (k % 2) 0) (l.get (k / 2)) (r.get (k / 2))

/-- **Node `k`** of the table; the default entry at and past the node count. -/
def ETable.get (E : ETable) (k : ℕ) : ENodeInfo := cond (Nat.blt k E.size) (E.tree.get k) default

/-- **Node `k` rendered with `n` levels**: its row with every kid rendered in turn; with `refs`, a
node printed as `.ref j` is `.ref j`. -/
def ETable.render (env : TEnv) (E : ETable) (refs : Bool) : ℕ → ℕ → Expr
  | 0, _ => default
  | n + 1, k =>
    match refs, (E.get k).ref with
    | true, some j => .ref j
    | _, _ => ((E.get k).node.row env).substRefs (E.render env refs n)

/-- **The print of node `k`**: its printed form, stopping at every node printed as `.ref j`. -/
def ETable.print (env : TEnv) (E : ETable) (k : ℕ) : Expr := E.render env true (k + 1) k

/-- **The check of a printed expression `e` against node `k`**: `e` is the node's print. -/
def ETable.eqB (env : TEnv) (E : ETable) (k : ℕ) (e : Expr) : Bool := (E.print env k).beq e

end GordieHowe.RealizedProgram
