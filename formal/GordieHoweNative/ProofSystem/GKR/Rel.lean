-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.ProofSystem.GKR.Codes

/-!
# GordieHowe: the compiled definitions of `GordieHowe.ProofSystem.GKR.Rel`

The definitions of `GordieHowe.ProofSystem.GKR.Rel` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/ProofSystem/GKR/Rel.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.GKR.Rel

open GordieHowe.GKR.Certificate GordieHowe.GKR.Fold

/-- **The wire of a node**: `0 + 1 · n`. -/
def Wire.node (n : ℕ) : Wire := ⟨0, 1, n⟩

/-- **A monomial** `κc c · v a · v b`. -/
structure Mono where
  /-- The first factor's node (`0`: the constant one). -/
  a : ℕ
  /-- The second factor's node. -/
  b : ℕ
  /-- The coefficient's code. -/
  c : ℕ
  deriving Repr, DecidableEq, Inhabited

/-- **A polynomial**: a list of monomials (sorted by `(a, b)` when normalized). -/
abbrev Poly := List Mono

/-- The order on monomials' keys. -/
def Mono.lt (m n : Mono) : Bool := Nat.blt m.a n.a || (Nat.beq m.a n.a && Nat.blt m.b n.b)

/-- Equal keys. -/
def Mono.same (m n : Mono) : Bool := Nat.beq m.a n.a && Nat.beq m.b n.b

/-- Structural equality of monomials. -/
def Mono.beq (m n : Mono) : Bool := Nat.beq m.a n.a && Nat.beq m.b n.b && Nat.beq m.c n.c

/-- Structural equality of polynomials. -/
def Poly.beq : Poly → Poly → Bool
  | [], [] => true
  | m :: p, n :: q => Mono.beq m n && Poly.beq p q
  | _, _ => false

/-- `m` in front of `p`, unless its coefficient is the code `0`. -/
def Poly.push (m : Mono) (p : Poly) : Poly := cond (Nat.beq m.c 0) p (m :: p)

/-- The monomial `c · v x · v y`, its factors in order. -/
def mono2 (x y c : ℕ) : Mono := cond (Nat.ble x y) ⟨x, y, c⟩ ⟨y, x, c⟩

/-- The constant `c`. -/
def Poly.const (c : ℕ) : Poly := Poly.push ⟨0, 0, c⟩ []

/-- Every monomial has degree at most one. -/
def Poly.lin (p : Poly) : Bool := p.all fun m => Nat.beq m.a 0

section Arith

variable (ar : CodeArith)

/-- **The sum of two polynomials sorted by `lt`**, a merge on the keys with `f` steps of fuel (out of
fuel, the concatenation). -/
def Poly.addBy (lt : Mono → Mono → Bool) : ℕ → Poly → Poly → Poly
  | 0, p, q => p ++ q
  | _ + 1, [], q => q
  | _ + 1, m :: p, [] => m :: p
  | f + 1, m :: p, n :: q =>
    cond (lt m n) (m :: Poly.addBy lt f p (n :: q))
      (cond (lt n m) (n :: Poly.addBy lt f (m :: p) q)
        (cond (Mono.same m n) (Poly.push ⟨m.a, m.b, ar.add m.c n.c⟩ (Poly.addBy lt f p q))
          (m :: n :: Poly.addBy lt f p q)))

/-- The sum in the order `lt`, with enough fuel for any two polynomials the checks build (`2^40`
steps; a fuel read from the lengths would cost the kernel a recursion as deep as the lists). -/
def Poly.add2By (lt : Mono → Mono → Bool) (p q : Poly) : Poly :=
  Poly.addBy ar lt (2 ^ 40) p q

/-- The sum, with enough fuel. -/
def Poly.add2 (p q : Poly) : Poly := Poly.add2By ar Mono.lt p q

/-- **`c` times a polynomial**: every coefficient multiplied, zeros dropped. -/
def Poly.scale (c : ℕ) (p : Poly) : Poly :=
  p.foldr (fun m acc => Poly.push ⟨m.a, m.b, cmul ar c m.c⟩ acc) []

/-- One round of pairwise sums in the order `lt`. -/
def Poly.pairsBy (lt : Mono → Mono → Bool) : List Poly → List Poly
  | p :: q :: r => Poly.add2By ar lt p q :: Poly.pairsBy lt r
  | r => r

/-- Pairwise sums until one polynomial is left, with fuel (out of fuel, the concatenation). -/
def Poly.sumAllBy (lt : Mono → Mono → Bool) : ℕ → List Poly → Poly
  | _, [] => []
  | _, [p] => p
  | 0, ps => ps.flatten
  | f + 1, ps => Poly.sumAllBy lt f (Poly.pairsBy ar lt ps)

/-- **The sum of a list of polynomials** sorted by `lt`: `64` rounds of pairwise sums, enough for any
list the checks build. -/
def Poly.sumBy (lt : Mono → Mono → Bool) (ps : List Poly) : Poly :=
  Poly.sumAllBy ar lt 64 ps

/-- **The sum of a list of polynomials**, normalized. -/
def Poly.sum (ps : List Poly) : Poly := Poly.sumBy ar Mono.lt ps

/-- **The product of two polynomials of degree at most one.** -/
def Poly.mulLin (p q : Poly) : Poly :=
  Poly.sum ar (p.map fun m => Poly.sum ar (q.map fun n => Poly.push (mono2 m.b n.b (cmul ar m.c n.c)) []))

/-- **An operand of a product**: a polynomial part of degree at most one, plus at most one atom
`κc c · v x`, given with the normal form `fx` of `x`. -/
structure Opnd where
  /-- The polynomial part. -/
  p : Poly
  /-- The atom `(c, x, fx)`, if any. -/
  a : Option (ℕ × ℕ × Poly)

/-- **A polynomial of degree at most one times an atom**; a constant times the atom expands it. -/
def rowA (p : Poly) : Option (ℕ × ℕ × Poly) → Poly
  | none => []
  | some (c, x, fx) => Poly.sum ar (p.map fun m =>
      cond (Nat.beq m.b 0) (Poly.scale ar (cmul ar m.c c) fx)
        (Poly.push (mono2 m.b x (cmul ar m.c c)) []))

/-- **The product of two atoms.** -/
def monoA : Option (ℕ × ℕ × Poly) → Option (ℕ × ℕ × Poly) → Poly
  | some (c, x, _), some (d, y, _) => Poly.push (mono2 x y (cmul ar c d)) []
  | _, _ => []

/-- **The product of two operands** (`none` if a polynomial part has degree two):
`(p + A)(q + B) = pq + pB + qA + AB`. -/
def mulp (x y : Opnd) : Option Poly :=
  cond (x.p.lin && y.p.lin)
    (some (Poly.sum ar [Poly.mulLin ar x.p y.p, rowA ar x.p y.a, rowA ar y.p x.a, monoA ar x.a y.a]))
    none

end Arith

section Dag

variable (w : ℕ) (D : Dag) (Kc : Consts) (ar : CodeArith)

/-- **Peel a node**: a non-input node with the one term `k · 1 · z` is `κ k · z`, repeated; `none`
for a zero node (no terms); otherwise the node itself with coefficient `1`. -/
def peel : ℕ → ℕ → Option (ℕ × ℕ)
  | 0, n => some (1, n)
  | f + 1, n =>
    cond (Nat.blt n D.inputs) (some (1, n))
      (match terms w (D.tree.get n) with
       | [] => none
       | [t] =>
         cond (Nat.beq t.a 0 && Nat.blt t.b n)
           ((peel f t.b).map fun p => (cmul ar (Kc.code t.k) p.1, p.2)) (some (1, n))
       | _ :: _ :: _ => some (1, n))

/-- **A product operand** given the normal forms `flatF` of smaller nodes: the constant of a peeled
constant node, else the peeled node as an atom. -/
def nodeOpnd (flatF : ℕ → Option Poly) (n : ℕ) : Option Opnd :=
  match peel w D Kc ar (n + 1) n with
  | none => some ⟨[], none⟩
  | some (c, x) =>
    cond (Nat.beq x 0) (some ⟨Poly.const c, none⟩)
      (match flatF x with
       | some fx => some ⟨[], some (c, x, fx)⟩
       | none => none)

/-- **The normal form of a wire** `c0 + c1 · n`; the node's own for `0 + 1 · n`. -/
def wirePoly (flatF : ℕ → Option Poly) (W : Wire) : Option Poly :=
  cond (Nat.beq W.c0 0 && Nat.beq W.c1 1) (flatF W.n)
    (match flatF W.n with
     | some p => some (Poly.add2 ar (Poly.const W.c0) (Poly.scale ar W.c1 p))
     | none => none)

/-- **A tree node's one-level expression** over its children's wires `c0 + c1 · n`. -/
inductive TE where
  /-- A child's wire `c0 + c1 · n`. -/
  | wire (c0 c1 n : ℕ)
  /-- A constant's code. -/
  | const (c : ℕ)
  /-- A sum. -/
  | add (a b : TE)
  /-- A multiple by a code. -/
  | scale (c : ℕ) (a : TE)
  /-- A product (of wires or constants). -/
  | mul (a b : TE)
  deriving Repr, Inhabited

/-- **The expression is the wire `W`** itself. -/
def TE.isWire (W : Wire) : TE → Bool
  | .wire c0 c1 n => Nat.beq c0 W.c0 && Nat.beq c1 W.c1 && Nat.beq n W.n
  | _ => false

/-- **The expression is a multiple** `0 + c · n` of the node `n`. -/
def TE.scalesNode (n : ℕ) : TE → Bool
  | .wire c0 _ m => Nat.beq c0 0 && Nat.beq m n
  | _ => false

/-- **A product operand of the tree**: a wire or a constant. -/
def TE.opnd (flatF : ℕ → Option Poly) : TE → Option Opnd
  | .const c => some ⟨Poly.const c, none⟩
  | .wire c0 c1 n =>
    (nodeOpnd w D Kc ar flatF n).map fun o =>
      ⟨Poly.add2 ar (Poly.const c0) (Poly.scale ar c1 o.p),
        o.a.map fun q => (cmul ar c1 q.1, q.2.1, q.2.2)⟩
  | _ => none

/-- **The normal form of a tree node's expression.** -/
def TE.poly (flatF : ℕ → Option Poly) : TE → Option Poly
  | .wire c0 c1 n => wirePoly ar flatF ⟨c0, c1, n⟩
  | .const c => some (Poly.const c)
  | .add a b =>
    match TE.poly flatF a, TE.poly flatF b with
    | some p, some q => some (Poly.add2 ar p q)
    | _, _ => none
  | .scale c a => (TE.poly flatF a).map (Poly.scale ar c)
  | .mul a b =>
    match TE.opnd w D Kc ar flatF a, TE.opnd w D Kc ar flatF b with
    | some x, some y => mulp ar x y
    | _, _ => none

end Dag

/-- **A linear atom** `c·[b]`, `b ≠ 0`. -/
def Mono.isLin (m : Mono) : Bool := Nat.beq m.a 0 && !Nat.beq m.b 0

/-- **The number of bits of `n`**, `f` steps of fuel. -/
def bitLen : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f + 1, n => cond (Nat.beq n 0) 0 (bitLen f (n / 2) + 1)

/-- **The coefficients of linear atoms by node**: a binary trie on the node's bits with the common
prefix of a subtree stored in its node (a Patricia trie), most significant bit first; its leaves
carry their node and code. A node `node p b l r` holds the nodes whose bits above `b` are `p`, those
with bit `b` clear in `l` and set in `r`. The largest node is found and removed along one path
(`popMax`), as is an insertion (`insert`); a path is as long as the branching on it, not the bit
length. The value of a trie is the sum over its leaves, wherever they sit: the shape only orders
the nodes. -/
inductive KTrie where
  /-- No atom. -/
  | nil
  /-- The code `c` of node `k`. -/
  | leaf (k c : ℕ)
  /-- The prefix `p` above bit `b`, the nodes with bit `b` clear, and those with it set. -/
  | node (p b : ℕ) (l r : KTrie)
  deriving Repr, Inhabited

/-- **`k t`, with `t` evaluated first** (the kernel reduces `t` to its constructor before it goes
on). A trie built by repeated inserts and removals passes through `seq` at every step, so the
kernel nests no chain of pending updates. -/
def KTrie.seq {α : Sort _} (t : KTrie) (k : KTrie → α) : α :=
  match t with
  | .nil => k .nil
  | .leaf n c => k (.leaf n c)
  | .node p b l r => k (.node p b l r)

/-- A node, collapsed to its other half when one half is `.nil`. -/
def KTrie.node' (p b : ℕ) (l r : KTrie) : KTrie :=
  match l, r with
  | .nil, r => r
  | l, .nil => l
  | l, r => .node p b l r

/-- **Bit `d` of `k` is set.** -/
def KTrie.bit (k d : ℕ) : Bool := Nat.beq (k >>> d % 2) 1

/-- **Two subtrees joined** at the highest bit where their representative nodes `k₁ ≠ k₂` differ. -/
def KTrie.join (k₁ : ℕ) (t₁ : KTrie) (k₂ : ℕ) (t₂ : KTrie) : KTrie :=
  let b := bitLen 64 (k₁ ^^^ k₂) - 1
  cond (KTrie.bit k₂ b) (.node (k₁ >>> (b + 1)) b t₁ t₂) (.node (k₁ >>> (b + 1)) b t₂ t₁)

/-- **Add the code `c` at node `k`**: the codes of one node add (`ar.add`), a zero code removes the
leaf; a node off a subtree's prefix joins it at the bit where they differ. -/
def KTrie.insert (ar : CodeArith) : KTrie → ℕ → ℕ → KTrie
  | .nil, k, c => cond (Nat.beq c 0) .nil (.leaf k c)
  | .leaf k' c', k, c =>
    cond (Nat.beq k' k)
      (cond (Nat.beq (ar.add c' c) 0) .nil (.leaf k (ar.add c' c)))
      (cond (Nat.beq c 0) (.leaf k' c') (KTrie.join k' (.leaf k' c') k (.leaf k c)))
  | .node p b l r, k, c =>
    cond (Nat.beq (k >>> (b + 1)) p)
      (cond (KTrie.bit k b)
        (KTrie.seq (KTrie.insert ar r k c) fun r' => KTrie.node' p b l r')
        (KTrie.seq (KTrie.insert ar l k c) fun l' => KTrie.node' p b l' r))
      (cond (Nat.beq c 0) (.node p b l r)
        (KTrie.join (p <<< (b + 1)) (.node p b l r) k (.leaf k c)))

/-- **The largest node**, its code, and the trie without it (the right half first). -/
def KTrie.popMax : KTrie → Option (ℕ × ℕ × KTrie)
  | .nil => none
  | .leaf k c => some (k, c, .nil)
  | .node p b l r =>
    match KTrie.popMax r with
    | some (k, c, r') => KTrie.seq (KTrie.node' p b l r') fun t => some (k, c, t)
    | none =>
      match KTrie.popMax l with
      | some (k, c, l') => KTrie.seq (KTrie.node' p b l' r) fun t => some (k, c, t)
      | none => none

/-- **Add the linear atoms `ms`** (each `c · [b]`) to the trie; `none` if one is not a linear
atom. -/
def KTrie.insertAll (ar : CodeArith) : KTrie → Poly → Option KTrie
  | t, [] => some t
  | t, m :: ms =>
    cond (Nat.beq m.a 0)
      (KTrie.seq (KTrie.insert ar t m.b m.c) fun t' => KTrie.insertAll ar t' ms)
      none

/-- **Why the difference check refuses.** -/
inductive Reason where
  /-- The tree expression has no normal form (a product operand not a wire or a constant, or a
  product of degree above two). -/
  | treeForm
  /-- The largest linear atom left is an input. -/
  | input
  /-- A node to unfold has a term reading a node not below it. -/
  | operand
  /-- Out of fuel. -/
  | fuel
  /-- No linear atom is left and the rests differ. -/
  | differ
  /-- The asserted node lacks the assertion term `0 · 1 · U`. -/
  | assertTerm
  /-- The asserted node is an input. -/
  | assertInput
  /-- A folded assertion's expression is not zero. -/
  | notZero
  /-- The asserted nodes are not among the DAG's (or not increasing). -/
  | asserted
  deriving Repr, DecidableEq, Inhabited

section Dag

variable (w : ℕ) (D : Dag) (Kc : Consts) (ar : CodeArith)

/-- **A node as its peeled atom** `c·[x]` for `peel n = (c, x)` (the constant `c` for `x = 0`), zero
for a zero node. -/
def peelPoly (n : ℕ) : Poly :=
  match peel w D Kc ar (n + 1) n with
  | none => []
  | some (c, x) => Poly.push ⟨0, x, c⟩ []

/-- The peeled atoms, as the normal forms the tree side reads. -/
def peelF (n : ℕ) : Option Poly := some (peelPoly w D Kc ar n)

/-- **A term `k · a · b` times the code `c`**, over peeled atoms: `c κk · [peel a] · [peel b]`, at
most one monomial. -/
def termMono (c : ℕ) (t : Term) : Poly :=
  match peel w D Kc ar (t.a + 1) t.a, peel w D Kc ar (t.b + 1) t.b with
  | some (ca, xa), some (cb, xb) =>
    Poly.push (mono2 xa xb (cmul ar c (cmul ar (Kc.code t.k) (cmul ar ca cb)))) []
  | _, _ => []

/-- **Node `b`'s terms times `c`**: the linear atoms and the rest (sorted); `none` when a term reads a
node not below `b`. -/
def unfold (b c : ℕ) : Option (Poly × Poly) :=
  let ts := terms w (D.tree.get b)
  cond (ts.all fun t => Nat.blt t.a b && Nat.blt t.b b)
    (let ms := ts.map (termMono w D Kc ar c)
     some ((ms.map (List.filter Mono.isLin)).flatten,
       Poly.sum ar (ms.map (List.filter fun m => !m.isLin))))
    none

/-- **Unfold the linear atom `c · [b]` of a side** (its linear atoms `t`, the rest `r`) and go on
with `k`: `b`'s terms times `c`, the linear ones added to `t`, the others pushed on `r`; an input
atom refuses. -/
def side (b c : ℕ) (t : KTrie) (r : List Poly) (k : KTrie → List Poly → Option Reason) :
    Option Reason :=
  cond (Nat.blt b D.inputs) (some .input)
    (match unfold w D Kc ar b c with
     | none => some .operand
     | some (ul, ur) =>
       match KTrie.insertAll ar t ul with
       | some t' => k t' (ur :: r)
       | none => some .operand)

/-- **The lazy difference loop** (A14) on two sides `P` and `Q`, each its linear atoms by node
(`KTrie`) and the rest: `P − Q`'s largest linear atom is unfolded on each side that carries it (an
atom with equal codes on both sides cancels); with no linear atom left, the rests agree. `none`:
accepted. -/
def diffLoop : ℕ → KTrie → List Poly → KTrie → List Poly → Option Reason
  | f, tp, rp, tq, rq =>
    match KTrie.popMax tp, KTrie.popMax tq with
    | none, none => cond (Poly.beq (Poly.sum ar rp) (Poly.sum ar rq)) none (some .differ)
    | mp, mq =>
      match f with
      | 0 => some .fuel
      | f + 1 =>
        match mp, mq with
        | some (kp, cp, tp'), none =>
          side w D Kc ar kp cp tp' rp fun a b => diffLoop f a b tq rq
        | none, some (kq, cq, tq') =>
          side w D Kc ar kq cq tq' rq fun a b => diffLoop f tp rp a b
        | some (kp, cp, tp'), some (kq, cq, tq') =>
          cond (Nat.blt kq kp) (side w D Kc ar kp cp tp' rp fun a b => diffLoop f a b tq rq)
            (cond (Nat.blt kp kq) (side w D Kc ar kq cq tq' rq fun a b => diffLoop f tp rp a b)
              (cond (Nat.beq cp cq) (diffLoop f tp' rp tq' rq)
                (side w D Kc ar kp cp tp' rp fun a b =>
                  side w D Kc ar kq cq tq' rq fun a' b' => diffLoop f a b a' b')))
        | none, none => cond (Poly.beq (Poly.sum ar rp) (Poly.sum ar rq)) none (some .differ)

/-- **The difference check of `p` and `q`**, `f` unfolds: each split into its linear atoms (a
trie) and the rest. -/
def diffCheck (f : ℕ) (p q : Poly) : Option Reason :=
  match KTrie.insertAll ar .nil (p.filter Mono.isLin),
    KTrie.insertAll ar .nil (q.filter Mono.isLin) with
  | some tp, some tq =>
    diffLoop w D Kc ar f tp [p.filter fun m => !m.isLin] tq [q.filter fun m => !m.isLin]
  | _, _ => some .operand

/-- **A cut's verdict** (A14; `none`: accepted): `e` is `W`, or `c0 + c1·[peel W.n]` minus `e`'s
normal form over peeled atoms vanishes by the lazy difference check, `W.n + 1` unfolds. -/
def cutR (W : Wire) (e : TE) : Option Reason :=
  cond (e.isWire W) none
    (match TE.poly w D Kc ar (peelF w D Kc ar) e with
     | none => some .treeForm
     | some q =>
       diffCheck w D Kc ar (W.n + 1)
         (Poly.add2 ar (Poly.const W.c0) (Poly.scale ar W.c1 (peelPoly w D Kc ar W.n))) q)

/-- **Node `Z` has the assertion term** `0 · 1 · U`. -/
def assertTermB (Z U : ℕ) : Bool :=
  (terms w (D.tree.get Z)).any fun t => Nat.beq t.k 0 && Nat.beq t.a 0 && Nat.beq t.b U

/-- **An assertion's verdict** (`none`: accepted). -/
def zeroR (Z U : ℕ) (e : TE) : Option Reason :=
  cond (Nat.beq Z 0)
    (match TE.poly w D Kc ar (peelF w D Kc ar) e with
     | none => some .treeForm
     | some q => (diffCheck w D Kc ar D.size [] q).map fun _ => .notZero)
    (cond (assertTermB w D Z U)
      (cond (Nat.ble D.inputs Z)
        (cond (e.scalesNode U) none (cutR w D Kc ar (Wire.node U) e))
        (some .assertInput))
      (some .assertTerm))

/-- The asserted nodes of the assertions, `Z = 0` left out. -/
def assertedNodes (zs : List (ℕ × ℕ × TE)) : List ℕ :=
  zs.filterMap fun z => cond (Nat.beq z.1 0) none (some z.1)

end Dag

end GordieHowe.GKR.Rel
