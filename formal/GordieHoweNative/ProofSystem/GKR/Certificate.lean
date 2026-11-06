-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Data

/-!
# GordieHowe: the compiled definitions of `GordieHowe.ProofSystem.GKR.Certificate`

The definitions of `GordieHowe.ProofSystem.GKR.Certificate` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/ProofSystem/GKR/Certificate.lean`, which imports this module.
-/

local notation "ℕ" => Nat

public section

namespace GordieHowe.GKR.Certificate

/-- A quadratic term `κ k · v a · v b`. -/
structure Term where
  /-- The constant's index. -/
  k : ℕ
  /-- The left operand. -/
  a : ℕ
  /-- The right operand. -/
  b : ℕ

/-- The `i`-th `w`-bit field of `T`. -/
@[expose] def field (w T i : ℕ) : ℕ := (T >>> (i * w)) % 2 ^ w

/-- `n` terms read from `c`, three fields each, least significant first. -/
@[expose] def decodeTerms (w : ℕ) : ℕ → ℕ → List Term
  | 0, _ => []
  | n + 1, c =>
    ⟨c % 2 ^ w, (c >>> w) % 2 ^ w, (c >>> (2 * w)) % 2 ^ w⟩ :: decodeTerms w n (c >>> (3 * w))

/-- A chunk's terms. -/
@[expose] def terms (w c : ℕ) : List Term := decodeTerms w (c % 2 ^ w / 2) (c >>> w)

/-- The chunk at key `k` (`0`, the zero node, where there is none). -/
@[expose] def NTree.get : NTree → ℕ → ℕ
  | .nil, _ => 0
  | .leaf c, _ => c
  | .node l r, k => cond (Nat.beq (k % 2) 0) (l.get (k / 2)) (r.get (k / 2))

/-- The `i`-th entry of a table. -/
@[expose] def cell (w : ℕ) : Table → ℕ → ℕ
  | .ident, i => i
  | .packed e t, i => field w (t.get (i >>> e)) (i % 2 ^ e)

/-- A chunk's flag: a copy wire (gate) or an input (DAG node). -/
@[expose] def flagged (w c : ℕ) : Bool := Nat.beq (c % 2 ^ w % 2) 1

/-- A gate chunk's wire index (the field after the header). -/
@[expose] def gateIndex (w c : ℕ) : ℕ := (c >>> w) % 2 ^ w

/-- The node a gate chunk carries (the second field after the header). -/
@[expose] def gateNode (w c : ℕ) : ℕ := (c >>> (2 * w)) % 2 ^ w

/-- A gate chunk's terms, after its header, index and node. -/
@[expose] def gateTerms (w c : ℕ) : List Term := decodeTerms w (c % 2 ^ w / 2) (c >>> (3 * w))

/-- A node's terms: none for an input. -/
@[expose] def nodeTerms (w : ℕ) (D : Dag) (n : ℕ) : List Term :=
  cond (Nat.blt n D.inputs) [] (terms w (D.tree.get n))

/-- `a` and `b` carry `A` and `B` in some order. -/
@[expose] def carries (w : ℕ) (T : Table) (a b A B : ℕ) : Bool :=
  (Nat.beq (cell w T a) A && Nat.beq (cell w T b) B) ||
    (Nat.beq (cell w T a) B && Nat.beq (cell w T b) A)

/-- A gate's terms against its node's: pairwise equal constants, wires below `wp` carrying the
node's operands, operands below `r`. -/
@[expose] def termsOk (w : ℕ) (T : Table) (wp r : ℕ) : List Term → List Term → Bool
  | [], [] => true
  | t :: ts, u :: us =>
    Nat.beq t.k u.k && Nat.blt t.a wp && Nat.blt t.b wp && Nat.blt u.a r && Nat.blt u.b r &&
      carries w T t.a t.b u.a u.b && termsOk w T wp r ts us
  | _, _ => false

/-- A copy gate's terms: one term `1 · a · b`, its wires carrying node `0` and `r`. -/
@[expose] def copyOk (w : ℕ) (T : Table) (wp r : ℕ) : List Term → Bool
  | [t] => Nat.beq t.k 1 && Nat.blt t.a wp && Nat.blt t.b wp && carries w T t.a t.b 0 r
  | _ => false

/-- The gate chunk `c` of a layer whose wires the table `Tc` maps to nodes, over the previous
depth's table `Tp` and width `wp`: the table maps its index to its node. -/
@[expose] def gateOk (w : ℕ) (D : Dag) (Tp : Table) (wp : ℕ) (Tc : Table) (c : ℕ) : Bool :=
  Nat.beq (cell w Tc (gateIndex w c)) (gateNode w c) && Nat.blt (gateNode w c) D.size &&
    cond (flagged w c) (copyOk w Tp wp (gateNode w c) (gateTerms w c))
      (Nat.ble D.inputs (gateNode w c) &&
        termsOk w Tp wp (gateNode w c) (gateTerms w c) (terms w (D.tree.get (gateNode w c))))

/-- The gates from wire `g` on, each chunk carrying its index (so no index is a growing sum). -/
@[expose] def gatesOk (w : ℕ) (D : Dag) (Tp : Table) (wp : ℕ) (Tc : Table) : ℕ → List ℕ → Bool
  | _, [] => true
  | g, c :: cs =>
    Nat.beq (gateIndex w c) g && gateOk w D Tp wp Tc c && gatesOk w D Tp wp Tc (gateIndex w c + 1) cs

/-- One layer. -/
@[expose] def layerOk (w : ℕ) (D : Dag) (Tp : Table) (wp : ℕ) (Tc : Table) (gates : List ℕ) : Bool :=
  gatesOk w D Tp wp Tc 0 gates

/-- A last-layer assertion: the node `n` is an assertion `0 · 1 · b` (one term, constant `0`, first
operand the constant one, node `0`), and the output wire `g` carries its operand `b`. -/
@[expose] def outputOk (w : ℕ) (D : Dag) (T : Table) (wl : ℕ) (o : ℕ × ℕ) : Bool :=
  Nat.blt o.1 wl && Nat.ble D.inputs o.2 &&
    match terms w (D.tree.get o.2) with
    | [t] => Nat.beq t.k 0 && Nat.beq t.a 0 && Nat.beq (cell w T o.1) t.b
    | _ => false

/-- Output nodes against output wires: each wire is in the last layer and carries its node. -/
@[expose] def outWiresOk (w : ℕ) (T : Table) (wl : ℕ) : List ℕ → List ℕ → Bool
  | [], [] => true
  | n :: ns, g :: gs => Nat.blt g wl && Nat.beq (cell w T g) n && outWiresOk w T wl ns gs
  | _, _ => false

/-- Merge two lists, smaller first (`fuel` bounds the steps; out of fuel, concatenation). -/
@[expose] def mergeNat : ℕ → List ℕ → List ℕ → List ℕ
  | 0, xs, ys => xs ++ ys
  | _ + 1, [], ys => ys
  | _ + 1, x :: xs, [] => x :: xs
  | f + 1, x :: xs, y :: ys =>
    cond (Nat.ble x y) (x :: mergeNat f xs (y :: ys)) (y :: mergeNat f (x :: xs) ys)

/-- Merge adjacent runs pairwise. -/
@[expose] def mergePairs : List (List ℕ) → List (List ℕ)
  | a :: b :: rest => mergeNat (a.length + b.length) a b :: mergePairs rest
  | l => l

/-- Merge the runs until one is left (`fuel` rounds). -/
@[expose] def mergeAll : ℕ → List (List ℕ) → List ℕ
  | _, [] => []
  | _, [a] => a
  | 0, ls => ls.flatten
  | f + 1, a :: b :: rest => mergeAll f (mergePairs (a :: b :: rest))

/-- Bottom-up merge sort of a list of naturals. -/
@[expose] def sortNat (l : List ℕ) : List ℕ := mergeAll l.length (l.map fun n => [n])

/-- **The wires `g, …, g + n − 1` all occur in the sorted list `l`**: past the entries below `g`,
the next one is `g`. -/
@[expose] def coverRun : ℕ → ℕ → List ℕ → Bool
  | 0, _, _ => true
  | n + 1, g, l =>
    match l.dropWhile (fun y => Nat.blt y g) with
    | y :: ys => Nat.beq y g && coverRun n (g + 1) (y :: ys)
    | [] => false

/-- Every layer, then the last-layer assertions and the output nodes against the last table. -/
@[expose] def layersOk (w : ℕ) (D : Dag) (outs : List (ℕ × ℕ)) (outw : List ℕ) :
    Table → ℕ → List Table → List (List ℕ) → Bool
  | Tp, wp, [], [] => outs.all (outputOk w D Tp wp) && outWiresOk w Tp wp D.outputs outw
  | Tp, wp, T :: Ts, l :: ls => layerOk w D Tp wp T l && layersOk w D outs outw T l.length Ts ls
  | _, _, _, _ => false

/-- Whether a term list has an assertion term. -/
@[expose] def hasAssert : List Term → Bool
  | [] => false
  | t :: ts => Nat.beq t.k 0 || hasAssert ts

/-- The nodes of a layer's non-copy gates with an assertion term, prepended to `acc` in
reverse wire order. -/
@[expose] def collectGates (w : ℕ) : List ℕ → List ℕ → List ℕ
  | [], acc => acc
  | c :: cs, acc =>
    collectGates w cs (cond (!flagged w c && hasAssert (gateTerms w c)) (gateNode w c :: acc) acc)

/-- The asserted nodes the circuit carries, from `acc` on. -/
@[expose] def collect (w : ℕ) : List (List ℕ) → List ℕ → List ℕ
  | l :: ls, acc => collect w ls (collectGates w l acc)
  | [], acc => acc

/-- List equality by `Nat.beq`. -/
@[expose] def listEq : List ℕ → List ℕ → Bool
  | [], [] => true
  | a :: as, b :: bs => Nat.beq a b && listEq as bs
  | _, _ => false

/-- **The wires of a layer's assertion gates**: the gates every term of which is an assertion term
(`k = 0`; such a gate's value is zero). -/
@[expose] def zeroGates (w : ℕ) (l : List ℕ) : List ℕ :=
  l.zipIdx.filterMap fun p => cond ((gateTerms w p.1).all fun t => Nat.beq t.k 0) (some p.2) none

/-- **Every wire of the last layer is constrained to zero**: an assertion's output wire, an output
node's wire, or an assertion gate; at least one layer. -/
@[expose] def lastCoverB (w : ℕ) (outs : List (ℕ × ℕ)) (outw : List ℕ) (layers : List (List ℕ)) : Bool :=
  match layers.getLast? with
  | some l => coverRun l.length 0 (sortNat (outs.map Prod.fst ++ outw ++ zeroGates w l))
  | none => false

/-- The node `0` is the input `0`. -/
@[expose] def oneOk (D : Dag) : Bool := Nat.blt 0 D.inputs

/-- The asserted nodes, in increasing id order, are the ones the circuit carries, sorted. -/
@[expose] def assertsOk (D : Dag) (C : Layered) (K : Cert) : Bool :=
  listEq D.asserts (sortNat (collect K.width C.layers (K.outputs.map Prod.snd)))

/-- The checker. -/
@[expose] def check (D : Dag) (C : Layered) (K : Cert) : Bool :=
  oneOk D && Nat.beq C.inputs D.inputs &&
    layersOk K.width D K.outputs K.outWires .ident C.inputs K.tables C.layers && assertsOk D C K &&
      lastCoverB K.width K.outputs K.outWires C.layers

/-- **A slice of a layer**: the `n` gates from position `s` on (every gate from `s` on when
`n = 0`), the first carrying the index `s`. A large layer is checked slice by slice, one theorem
each, so no kernel check grows with the layer. -/
@[expose] def layerSliceOk (w : ℕ) (D : Dag) (Tp : Table) (wp : ℕ) (Tc : Table) (gates : List ℕ)
    (s n : ℕ) : Bool :=
  gatesOk w D Tp wp Tc s (cond (Nat.beq n 0) (gates.drop s) ((gates.drop s).take n))

/-- **The `n` entries of `l` from position `s`** (every entry from `s` on when `n = 0`). -/
@[expose] def sliceL (l : List ℕ) (s n : ℕ) : List ℕ := cond (Nat.beq n 0) (l.drop s) ((l.drop s).take n)

/-- The number of a layer's non-copy gates with an assertion term, the nodes `collectGates`
adds. -/
@[expose] def countGates (w : ℕ) : List ℕ → ℕ
  | [] => 0
  | c :: cs => cond (!flagged w c && hasAssert (gateTerms w c)) 1 0 + countGates w cs

/-- **Per layer, its gate count and asserting-gate count.** -/
@[expose] def layersCountB (w : ℕ) : List (List ℕ) → List ℕ → List ℕ → Bool
  | [], [], [] => true
  | l :: ls, m :: ms, c :: cs =>
    Nat.beq l.length m && Nat.beq (countGates w l) c && layersCountB w ls ms cs
  | _, _, _ => false

/-- **`lo < l₀ < l₁ < ⋯`, the last of `lo :: l` being `hi`.** -/
@[expose] def chainLast : ℕ → List ℕ → ℕ → Bool
  | lo, [], hi => Nat.beq lo hi
  | lo, x :: xs, hi => Nat.blt lo x && chainLast x xs hi

/-- **A witness that the asserted node `n` is collected** by the layers `Ts`, of widths `ws`:
`(0, j)`, the node of the `j`-th last-layer assertion `outs`; `(d + 1, g)`, a wire `g` below
the width of layer `d` whose table entry is `n`, a node with an assertion term. Either way `n` is
at or above the inputs. -/
@[expose] def assertWitOk (w : ℕ) (D : Dag) (outs : List (ℕ × ℕ)) (Ts : List Table) (ws : List ℕ) (n : ℕ)
    (p : ℕ × ℕ) : Bool :=
  Nat.ble D.inputs n &&
    cond (Nat.beq p.1 0) (Nat.beq (outs.getD p.2 (0, 0)).2 n)
      (hasAssert (terms w (D.tree.get n)) && Nat.blt p.2 (ws.getD (p.1 - 1) 0) &&
        Nat.beq (cell w (Ts.getD (p.1 - 1) .ident) p.2) n)

/-- Witnesses for a list of asserted nodes, one each. -/
@[expose] def witsOk (w : ℕ) (D : Dag) (outs : List (ℕ × ℕ)) (Ts : List Table) (ws : List ℕ) :
    List ℕ → List (ℕ × ℕ) → Bool
  | [], [] => true
  | n :: ns, p :: ps => assertWitOk w D outs Ts ws n p && witsOk w D outs Ts ws ns ps
  | _, _ => false

/-- **A slice of the asserted nodes**: the `n` from position `s` (every one from `s` on when
`n = 0`) increase from above `lo` to `hi`, with the witnesses `wit`. -/
@[expose] def assertSliceOk (w : ℕ) (D : Dag) (outs : List (ℕ × ℕ)) (Ts : List Table) (ws : List ℕ)
    (s n lo hi : ℕ) (wit : List (ℕ × ℕ)) : Bool :=
  chainLast lo (sliceL D.asserts s n) hi && witsOk w D outs Ts ws (sliceL D.asserts s n) wit

/-- Defining equation for the gate check, used by its semantic soundness proofs. -/
theorem gateOk_eq (w : ℕ) (D : Dag) (Tp : Table) (wp : ℕ) (Tc : Table) (c : ℕ) :
    gateOk w D Tp wp Tc c =
      (Nat.beq (cell w Tc (gateIndex w c)) (gateNode w c) && Nat.blt (gateNode w c) D.size &&
        cond (flagged w c) (copyOk w Tp wp (gateNode w c) (gateTerms w c))
          (Nat.ble D.inputs (gateNode w c) &&
            termsOk w Tp wp (gateNode w c) (gateTerms w c) (terms w (D.tree.get (gateNode w c))))) := rfl

end GordieHowe.GKR.Certificate
