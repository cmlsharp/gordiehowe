-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Ring.Defs
public import GordieHoweNative.Data
public import GordieHoweNative.ProofSystem.GKR.Certificate

@[expose] public section

/-!
# Translation validation of the GKR circuit compiler: arithmetic gates and copy wires

Longfellow's compiler (`lib/circuits/compiler/compiler.h`, `lib/circuits/compiler/schedule.h`)
turns a DAG of quadratic-form nodes into layered quads: every needed node gets a wire at its
depth, and a copy wire `1 · one · w` at every later depth up to the deepest layer reading it.
This file checks one compilation, for one exported circuit, by a `Bool` checker that
`decide +kernel` evaluates, and proves it sound (`check_sound`).

**Encoding.** Every number is a field of `w` bits of a natural number (`field`), read by
`>>>` and `%`, which the kernel evaluates on GMP numerals. A *chunk* is one gate or one DAG
node: a header (`flag + 2 · count`) and `count` terms `(k, a, b)`, the term `κ k · v a · v b`
with `k` an index into the constant table `κ`. The DAG is a binary trie keyed by node id,
least significant bit first (`NTree.get`); a node's flag marks an input (its index is the
first field after the header). A layer is the list of its gates in wire order; a gate's flag
marks a copy wire. The certificate is one packed table per depth: the DAG node each wire of
that depth carries (`cell w T g`), in chunks of `2 ^ e` entries under a trie (`Table`), so no
access touches a number that grows with the circuit.

**The layered circuit.** `Layered` is the circuit the Lean GKR model is about: per layer, the
quad terms grouped by gate, each gate's terms in its node's term order. The C++ circuit stores
the same terms as a Morton-sorted quad (`EQuad::canonicalize`); per gate the two are the same
multiset of terms, which the C++ exporter checks when it writes the certificate
(`compiler.h`, `write_cert`). That correspondence is part of the existing export-fidelity
assumption, not of this file.

**The DAG** is the compiler's node table as `push_node` creates it: inputs and quadratic forms
`Σ κ k · n_a · n_b` over a constant table, `assert0 n` being the form `κ 0 · n_0 · n_n`. Its
asserted nodes are listed in increasing id order.

**Checker.** One pass over each layer's gates in wire order. A non-copy gate `g` carrying node
`r` must list `r`'s terms in order, with equal constant indices and with each term's wires
carrying `r`'s operands (in either order, the product commuting), all operands below `r`. A
copy gate is one term `1 · a · b` whose wires carry node `0` (the input `0`, the constant one)
and `r`. Inputs carry input nodes with their own index. The DAG's asserted nodes are the
non-copy nodes with an assertion term (`k = 0`) and the nodes `0 · a · b` whose operand is
an output wire (`Longfellow`'s last-layer assertions become outputs); the checker sorts them and
compares with the DAG's list.

**Soundness.** If the checker accepts, every wire's value is the value of its node
(`layerOk_carried`), and if the layered circuit is satisfied (every assertion product
vanishes, every output is zero) every asserted DAG node's assertion products vanish
(`check_sound`).

The definitions are in `GordieHoweNative/ProofSystem/GKR/Certificate.lean`
(the compiled library `GordieHoweNative`); this module has their lemmas.
-/

namespace GordieHowe.GKR.Certificate

/-- A chunk's flag: a copy wire (gate) or an input (DAG node). -/
def flagged (w c : ℕ) : Bool := Nat.beq (c % 2 ^ w % 2) 1

/-- A gate chunk's wire index (the field after the header). -/
def gateIndex (w c : ℕ) : ℕ := (c >>> w) % 2 ^ w

/-- The node a gate chunk carries (the second field after the header). -/
def gateNode (w c : ℕ) : ℕ := (c >>> (2 * w)) % 2 ^ w

/-- A gate chunk's terms, after its header, index and node. -/
def gateTerms (w c : ℕ) : List Term := decodeTerms w (c % 2 ^ w / 2) (c >>> (3 * w))

section Semantics

variable {F : Type*} [CommSemiring F]

/-- A node's terms: none for an input. -/
def nodeTerms (w : ℕ) (D : Dag) (n : ℕ) : List Term :=
  cond (Nat.blt n D.inputs) [] (terms w (D.tree.get n))

/-- The value of every DAG node on the input `x` with constants `κ`: an input node is its
input, any other node the sum of its terms (a term reading a node not below it counts zero;
the checker excludes it). -/
def Dag.val (w : ℕ) (D : Dag) (κ x : ℕ → F) (n : ℕ) : F :=
  cond (Nat.blt n D.inputs) (x n)
    ((terms w (D.tree.get n)).map fun t =>
      if _h : t.a < n ∧ t.b < n then κ t.k * D.val w κ x t.a * D.val w κ x t.b else 0).sum
termination_by n

/-- Every assertion term (`k = 0`) of the node `n` has vanishing product. -/
def Dag.AssertHolds (w : ℕ) (D : Dag) (κ x : ℕ → F) (n : ℕ) : Prop :=
  ∀ t ∈ nodeTerms w D n, t.k = 0 → D.val w κ x t.a * D.val w κ x t.b = 0

/-- The DAG's assertions hold. -/
def Dag.Holds (w : ℕ) (D : Dag) (κ x : ℕ → F) : Prop :=
  (∀ n ∈ D.asserts, D.AssertHolds w κ x n) ∧ ∀ n ∈ D.outputs, D.val w κ x n = 0

/-- A layer's wire values from the previous depth's values. -/
def layerValue (w : ℕ) (κ : ℕ → F) (gates : List ℕ) (v : ℕ → F) (g : ℕ) : F :=
  ((gateTerms w (gates.getD g 0)).map fun t => κ t.k * v t.a * v t.b).sum

/-- Satisfaction from a depth with values `v`: every assertion product of every later layer
vanishes and every output is zero. -/
def Sat (w : ℕ) (κ : ℕ → F) : List (List ℕ) → (ℕ → F) → Prop
  | [], v => ∀ g, v g = 0
  | l :: ls, v =>
    (∀ g < l.length, ∀ t ∈ gateTerms w (l.getD g 0), t.k = 0 → v t.a * v t.b = 0) ∧
      Sat w κ ls (layerValue w κ l v)

/-- The layered circuit is satisfied on the input `x`. -/
def Layered.Satisfied (w : ℕ) (C : Layered) (κ x : ℕ → F) : Prop := Sat w κ C.layers x

end Semantics

section Checker

/-- `a` and `b` carry `A` and `B` in some order. -/
def carries (w : ℕ) (T : Table) (a b A B : ℕ) : Bool :=
  (Nat.beq (cell w T a) A && Nat.beq (cell w T b) B) ||
    (Nat.beq (cell w T a) B && Nat.beq (cell w T b) A)

/-- A gate's terms against its node's: pairwise equal constants, wires below `wp` carrying the
node's operands, operands below `r`. -/
def termsOk (w : ℕ) (T : Table) (wp r : ℕ) : List Term → List Term → Bool
  | [], [] => true
  | t :: ts, u :: us =>
    Nat.beq t.k u.k && Nat.blt t.a wp && Nat.blt t.b wp && Nat.blt u.a r && Nat.blt u.b r &&
      carries w T t.a t.b u.a u.b && termsOk w T wp r ts us
  | _, _ => false

/-- A copy gate's terms: one term `1 · a · b`, its wires carrying node `0` and `r`. -/
def copyOk (w : ℕ) (T : Table) (wp r : ℕ) : List Term → Bool
  | [t] => Nat.beq t.k 1 && Nat.blt t.a wp && Nat.blt t.b wp && carries w T t.a t.b 0 r
  | _ => false

/-- The gate chunk `c` of a layer whose wires the table `Tc` maps to nodes, over the previous
depth's table `Tp` and width `wp`: the table maps its index to its node. -/
def gateOk (w : ℕ) (D : Dag) (Tp : Table) (wp : ℕ) (Tc : Table) (c : ℕ) : Bool :=
  Nat.beq (cell w Tc (gateIndex w c)) (gateNode w c) && Nat.blt (gateNode w c) D.size &&
    cond (flagged w c) (copyOk w Tp wp (gateNode w c) (gateTerms w c))
      (Nat.ble D.inputs (gateNode w c) &&
        termsOk w Tp wp (gateNode w c) (gateTerms w c) (terms w (D.tree.get (gateNode w c))))

/-- The gates from wire `g` on, each chunk carrying its index (so no index is a growing sum). -/
def gatesOk (w : ℕ) (D : Dag) (Tp : Table) (wp : ℕ) (Tc : Table) : ℕ → List ℕ → Bool
  | _, [] => true
  | g, c :: cs =>
    Nat.beq (gateIndex w c) g && gateOk w D Tp wp Tc c && gatesOk w D Tp wp Tc (gateIndex w c + 1) cs

/-- One layer. -/
def layerOk (w : ℕ) (D : Dag) (Tp : Table) (wp : ℕ) (Tc : Table) (gates : List ℕ) : Bool :=
  gatesOk w D Tp wp Tc 0 gates

/-- A last-layer assertion: the node `n` is an assertion `0 · 1 · b` (one term, constant `0`, first
operand the constant one, node `0`), and the output wire `g` carries its operand `b`. -/
def outputOk (w : ℕ) (D : Dag) (T : Table) (wl : ℕ) (o : ℕ × ℕ) : Bool :=
  Nat.blt o.1 wl && Nat.ble D.inputs o.2 &&
    match terms w (D.tree.get o.2) with
    | [t] => Nat.beq t.k 0 && Nat.beq t.a 0 && Nat.beq (cell w T o.1) t.b
    | _ => false

/-- Output nodes against output wires: each wire is in the last layer and carries its node. -/
def outWiresOk (w : ℕ) (T : Table) (wl : ℕ) : List ℕ → List ℕ → Bool
  | [], [] => true
  | n :: ns, g :: gs => Nat.blt g wl && Nat.beq (cell w T g) n && outWiresOk w T wl ns gs
  | _, _ => false

/-- Merge two lists, smaller first (`fuel` bounds the steps; out of fuel, concatenation). -/
def mergeNat : ℕ → List ℕ → List ℕ → List ℕ
  | 0, xs, ys => xs ++ ys
  | _ + 1, [], ys => ys
  | _ + 1, x :: xs, [] => x :: xs
  | f + 1, x :: xs, y :: ys =>
    cond (Nat.ble x y) (x :: mergeNat f xs (y :: ys)) (y :: mergeNat f (x :: xs) ys)

/-- Merge adjacent runs pairwise. -/
def mergePairs : List (List ℕ) → List (List ℕ)
  | a :: b :: rest => mergeNat (a.length + b.length) a b :: mergePairs rest
  | l => l

/-- Merge the runs until one is left (`fuel` rounds). -/
def mergeAll : ℕ → List (List ℕ) → List ℕ
  | _, [] => []
  | _, [a] => a
  | 0, ls => ls.flatten
  | f + 1, a :: b :: rest => mergeAll f (mergePairs (a :: b :: rest))

/-- Bottom-up merge sort of a list of naturals. -/
def sortNat (l : List ℕ) : List ℕ := mergeAll l.length (l.map fun n => [n])

/-- **The wires `g, …, g + n − 1` all occur in the sorted list `l`**: past the entries below `g`,
the next one is `g`. -/
def coverRun : ℕ → ℕ → List ℕ → Bool
  | 0, _, _ => true
  | n + 1, g, l =>
    match l.dropWhile (fun y => Nat.blt y g) with
    | y :: ys => Nat.beq y g && coverRun n (g + 1) (y :: ys)
    | [] => false

/-- Every layer, then the last-layer assertions and the output nodes against the last table. -/
def layersOk (w : ℕ) (D : Dag) (outs : List (ℕ × ℕ)) (outw : List ℕ) :
    Table → ℕ → List Table → List (List ℕ) → Bool
  | Tp, wp, [], [] => outs.all (outputOk w D Tp wp) && outWiresOk w Tp wp D.outputs outw
  | Tp, wp, T :: Ts, l :: ls => layerOk w D Tp wp T l && layersOk w D outs outw T l.length Ts ls
  | _, _, _, _ => false

/-- Whether a term list has an assertion term. -/
def hasAssert : List Term → Bool
  | [] => false
  | t :: ts => Nat.beq t.k 0 || hasAssert ts

/-- The nodes of a layer's non-copy gates with an assertion term, prepended to `acc` in
reverse wire order. -/
def collectGates (w : ℕ) : List ℕ → List ℕ → List ℕ
  | [], acc => acc
  | c :: cs, acc =>
    collectGates w cs (cond (!flagged w c && hasAssert (gateTerms w c)) (gateNode w c :: acc) acc)

/-- The asserted nodes the circuit carries, from `acc` on. -/
def collect (w : ℕ) : List (List ℕ) → List ℕ → List ℕ
  | l :: ls, acc => collect w ls (collectGates w l acc)
  | [], acc => acc

/-- List equality by `Nat.beq`. -/
def listEq : List ℕ → List ℕ → Bool
  | [], [] => true
  | a :: as, b :: bs => Nat.beq a b && listEq as bs
  | _, _ => false

/-- **The wires of a layer's assertion gates**: the gates every term of which is an assertion term
(`k = 0`; such a gate's value is zero). -/
def zeroGates (w : ℕ) (l : List ℕ) : List ℕ :=
  l.zipIdx.filterMap fun p => cond ((gateTerms w p.1).all fun t => Nat.beq t.k 0) (some p.2) none

/-- **Every wire of the last layer is constrained to zero**: an assertion's output wire, an output
node's wire, or an assertion gate; at least one layer. -/
def lastCoverB (w : ℕ) (outs : List (ℕ × ℕ)) (outw : List ℕ) (layers : List (List ℕ)) : Bool :=
  match layers.getLast? with
  | some l => coverRun l.length 0 (sortNat (outs.map Prod.fst ++ outw ++ zeroGates w l))
  | none => false

/-- The node `0` is the input `0`. -/
def oneOk (D : Dag) : Bool := Nat.blt 0 D.inputs

/-- The asserted nodes, in increasing id order, are the ones the circuit carries, sorted. -/
def assertsOk (D : Dag) (C : Layered) (K : Cert) : Bool :=
  listEq D.asserts (sortNat (collect K.width C.layers (K.outputs.map Prod.snd)))

/-- The checker. -/
def check (D : Dag) (C : Layered) (K : Cert) : Bool :=
  oneOk D && Nat.beq C.inputs D.inputs &&
    layersOk K.width D K.outputs K.outWires .ident C.inputs K.tables C.layers && assertsOk D C K &&
      lastCoverB K.width K.outputs K.outWires C.layers

/-- The checker from its parts, one theorem each. -/
theorem check_of_parts {D : Dag} {C : Layered} {K : Cert} (h1 : oneOk D = true)
    (h2 : Nat.beq C.inputs D.inputs = true)
    (h3 : layersOk K.width D K.outputs K.outWires .ident C.inputs K.tables C.layers = true)
    (h4 : assertsOk D C K = true) (h5 : lastCoverB K.width K.outputs K.outWires C.layers = true) :
    check D C K = true := by
  simp [check, h1, h2, h3, h4, h5]

/-- The gates' checker on a concatenation, from each part's: the second part starts at the
first's index plus its length. One theorem per block keeps each kernel check (and its caches)
bounded. -/
theorem gatesOk_append {w : ℕ} {D : Dag} {Tp Tc : Table} {wp : ℕ} :
    ∀ {g n : ℕ} {l₁ l₂ : List ℕ}, gatesOk w D Tp wp Tc g l₁ = true → g + l₁.length = n →
      gatesOk w D Tp wp Tc n l₂ = true → gatesOk w D Tp wp Tc g (l₁ ++ l₂) = true
  | g, n, [], l₂, _, hl, h₂ => by simp only [List.length_nil, Nat.add_zero] at hl; subst hl; simpa
  | g, n, c :: cs, l₂, h₁, hl, h₂ => by
    simp only [gatesOk, Bool.and_eq_true, Nat.beq_eq] at h₁
    obtain ⟨⟨hi, hc⟩, hrest⟩ := h₁
    simp only [List.cons_append, gatesOk, Bool.and_eq_true, Nat.beq_eq]
    refine ⟨⟨hi, hc⟩, gatesOk_append hrest ?_ h₂⟩
    simp only [List.length_cons] at hl
    omega

/-- **A slice of a layer**: the `n` gates from position `s` on (every gate from `s` on when
`n = 0`), the first carrying the index `s`. A large layer is checked slice by slice, one theorem
each, so no kernel check grows with the layer. -/
def layerSliceOk (w : ℕ) (D : Dag) (Tp : Table) (wp : ℕ) (Tc : Table) (gates : List ℕ)
    (s n : ℕ) : Bool :=
  gatesOk w D Tp wp Tc s (cond (Nat.beq n 0) (gates.drop s) ((gates.drop s).take n))

/-- **A slice and the rest after it** check as the rest from the slice's start. -/
theorem layerSliceOk_cons {w : ℕ} {D : Dag} {Tp : Table} {wp : ℕ} {Tc : Table} {gates : List ℕ}
    {s n : ℕ} (hn : 0 < n) (h₁ : layerSliceOk w D Tp wp Tc gates s n = true)
    (h₂ : layerSliceOk w D Tp wp Tc gates (s + n) 0 = true) :
    layerSliceOk w D Tp wp Tc gates s 0 = true := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hb : Nat.beq (m + 1) 0 = false := rfl
  simp only [layerSliceOk, hb, Nat.beq_refl, Bool.cond_true, Bool.cond_false] at h₁ h₂ ⊢
  rw [← List.take_append_drop (m + 1) (gates.drop s)]
  by_cases hl : m + 1 ≤ (gates.drop s).length
  · refine gatesOk_append (n := s + (m + 1)) h₁ ?_ ?_
    · rw [List.length_take, Nat.min_eq_left hl]
    · rwa [List.drop_drop]
  · rw [List.drop_eq_nil_of_le (Nat.le_of_not_le hl), List.append_nil]
    exact h₁

/-- **A layer from its slices**: every gate from position `0` on checks. -/
theorem layerOk_of_slices {w : ℕ} {D : Dag} {Tp : Table} {wp : ℕ} {Tc : Table} {gates : List ℕ}
    (h : layerSliceOk w D Tp wp Tc gates 0 0 = true) : layerOk w D Tp wp Tc gates = true := by
  simpa [layerSliceOk, layerOk] using h

/-- The layers' checker from the first layer's and the rest's. -/
theorem layersOk_cons {w : ℕ} {D : Dag} {outs : List (ℕ × ℕ)} {outw : List ℕ} {Tp T : Table} {wp : ℕ} {Ts : List Table}
    {l : List ℕ} {ls : List (List ℕ)} (h1 : layerOk w D Tp wp T l = true)
    (h2 : layersOk w D outs outw T l.length Ts ls = true) :
    layersOk w D outs outw Tp wp (T :: Ts) (l :: ls) = true := by
  simp [layersOk, h1, h2]

/-- The layers' checker after the last layer: the last-layer assertions. -/
theorem layersOk_nil {w : ℕ} {D : Dag} {outs : List (ℕ × ℕ)} {outw : List ℕ} {Tp : Table}
    {wp : ℕ} (h : outs.all (outputOk w D Tp wp) = true)
    (h' : outWiresOk w Tp wp D.outputs outw = true) :
    layersOk w D outs outw Tp wp [] [] = true := by
  simp [layersOk, h, h']

end Checker

section Soundness

variable {F : Type*} [CommSemiring F]

/-- The unfolding of `Dag.val`, without the decreasing proofs. -/
theorem Dag.val_eq (w : ℕ) (D : Dag) (κ x : ℕ → F) (n : ℕ) :
    D.val w κ x n =
      cond (Nat.blt n D.inputs) (x n)
        ((terms w (D.tree.get n)).map fun t =>
          if t.a < n ∧ t.b < n then κ t.k * D.val w κ x t.a * D.val w κ x t.b else 0).sum := by
  rw [Dag.val]
  simp only [dite_eq_ite]

/-- The values of a depth's wires are their nodes' values, below the width `wd`. -/
def Carried (w : ℕ) (D : Dag) (κ x : ℕ → F) (T : Table) (wd : ℕ) (v : ℕ → F) : Prop :=
  ∀ g < wd, v g = D.val w κ x (cell w T g)

/-- Wires carrying `A` and `B` (in some order) have the product of their nodes' values. -/
theorem carries_prod {w : ℕ} {T : Table} {a b A B : ℕ} (h : carries w T a b A B = true) (v val : ℕ → F)
    (hv : v a = val (cell w T a)) (hvb : v b = val (cell w T b)) :
    v a * v b = val A * val B := by
  simp only [carries, Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [hv, hvb, h1, h2]
  · rw [hv, hvb, h1, h2, mul_comm]

/-- Accepted term lists have equal sums: the gate's over the previous depth's values, the
node's over the DAG's. -/
theorem termsOk_sum {w : ℕ} {D : Dag} {κ x : ℕ → F} {T : Table} {wp r : ℕ} {v : ℕ → F}
    (hv : Carried w D κ x T wp v) :
    ∀ ts us, termsOk w T wp r ts us = true →
      (ts.map fun t => κ t.k * v t.a * v t.b).sum =
        (us.map fun t =>
          if t.a < r ∧ t.b < r then κ t.k * D.val w κ x t.a * D.val w κ x t.b else 0).sum
  | [], [], _ => rfl
  | t :: ts, u :: us, h => by
    simp only [termsOk, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨hk, hta⟩, htb⟩, hua⟩, hub⟩, hc⟩, hrest⟩ := h
    simp only [List.map_cons, List.sum_cons, hua, hub, and_self, ite_true]
    rw [termsOk_sum hv ts us hrest, mul_assoc, mul_assoc,
      carries_prod hc v (D.val w κ x) (hv _ hta) (hv _ htb), hk]
  | [], _ :: _, h => by simp [termsOk] at h
  | _ :: _, [], h => by simp [termsOk] at h

/-- Accepted term lists carry assertions: if the gate's assertion products vanish, so do the
node's. -/
theorem termsOk_assert {w : ℕ} {D : Dag} {κ x : ℕ → F} {T : Table} {wp r : ℕ} {v : ℕ → F}
    (hv : Carried w D κ x T wp v) :
    ∀ ts us, termsOk w T wp r ts us = true →
      (∀ t ∈ ts, t.k = 0 → v t.a * v t.b = 0) →
        ∀ u ∈ us, u.k = 0 → D.val w κ x u.a * D.val w κ x u.b = 0
  | [], [], _, _ => by simp
  | t :: ts, u :: us, h, ha => by
    simp only [termsOk, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨hk, hta⟩, htb⟩, _⟩, _⟩, hc⟩, hrest⟩ := h
    intro u' hu' hk'
    rcases List.mem_cons.mp hu' with rfl | hu'
    · rw [← carries_prod hc v (D.val w κ x) (hv _ hta) (hv _ htb)]
      exact ha t (List.mem_cons_self ..) (hk.trans hk')
    · exact termsOk_assert hv ts us hrest (fun t' ht' => ha t' (List.mem_cons_of_mem _ ht'))
        u' hu' hk'
  | [], _ :: _, h, _ => by simp [termsOk] at h
  | _ :: _, [], h, _ => by simp [termsOk] at h

/-- The node `0` (the input `0`) has value one. -/
theorem val_zero {w : ℕ} {D : Dag} {κ x : ℕ → F} (hD : oneOk D = true) (hx : x 0 = 1) :
    D.val w κ x 0 = 1 := by
  rw [Dag.val_eq, show Nat.blt 0 D.inputs = true from hD, Bool.cond_true, hx]

/-- A node at or above the inputs has its chunk's terms. -/
theorem nodeTerms_of_le {w : ℕ} {D : Dag} {n : ℕ} (h : Nat.ble D.inputs n = true) :
    nodeTerms w D n = terms w (D.tree.get n) := by
  have : Nat.blt n D.inputs = false := by
    rw [Nat.ble_eq] at h
    exact Bool.eq_false_iff.mpr (by rw [ne_eq, Nat.blt_eq]; omega)
  simp [nodeTerms, this]

/-- A node at or above the inputs is the sum of its terms. -/
theorem val_of_le {w : ℕ} {D : Dag} {κ x : ℕ → F} {n : ℕ} (h : Nat.ble D.inputs n = true) :
    D.val w κ x n = ((terms w (D.tree.get n)).map fun t =>
      if t.a < n ∧ t.b < n then κ t.k * D.val w κ x t.a * D.val w κ x t.b else 0).sum := by
  have : Nat.blt n D.inputs = false := by
    rw [Nat.ble_eq] at h
    exact Bool.eq_false_iff.mpr (by rw [ne_eq, Nat.blt_eq]; omega)
  rw [Dag.val_eq, this, Bool.cond_false]

/-- An accepted gate's value is its node's. -/
theorem gateOk_value {w : ℕ} {D : Dag} {κ x : ℕ → F} {Tp Tc : Table} {wp c : ℕ} {v : ℕ → F}
    (hκ : κ 1 = 1) (hone : D.val w κ x 0 = 1) (hv : Carried w D κ x Tp wp v)
    (h : gateOk w D Tp wp Tc c = true) :
    ((gateTerms w c).map fun t => κ t.k * v t.a * v t.b).sum = D.val w κ x (gateNode w c) := by
  unfold gateOk at h
  simp only [Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨_, h⟩ := h
  cases hf : flagged w c
  · rw [hf, Bool.cond_false] at h
    simp only [Bool.and_eq_true] at h
    rw [termsOk_sum hv _ _ h.2, val_of_le h.1]
  · rw [hf, Bool.cond_true] at h
    generalize gateTerms w c = ts at h ⊢
    match ts, h with
    | [t], h =>
      simp only [copyOk, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at h
      obtain ⟨⟨⟨hk, ha⟩, hb⟩, hc⟩ := h
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      rw [mul_assoc, carries_prod hc v (D.val w κ x) (hv _ ha) (hv _ hb), hk, hκ, hone]
      simp

/-- An accepted gate's table entry is its node. -/
theorem gateOk_cell {w : ℕ} {D : Dag} {Tp Tc : Table} {wp c : ℕ}
    (h : gateOk w D Tp wp Tc c = true) : cell w Tc (gateIndex w c) = gateNode w c := by
  unfold gateOk at h
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  exact h.1.1

/-- An accepted node gate's assertion terms carry its node's. -/
theorem gateOk_assert {w : ℕ} {D : Dag} {κ x : ℕ → F} {Tp Tc : Table} {wp c : ℕ} {v : ℕ → F}
    (hv : Carried w D κ x Tp wp v) (h : gateOk w D Tp wp Tc c = true)
    (hcopy : flagged w c = false) (ha : ∀ t ∈ gateTerms w c, t.k = 0 → v t.a * v t.b = 0) :
    D.AssertHolds w κ x (gateNode w c) := by
  unfold gateOk at h
  simp only [Bool.and_eq_true, hcopy, Bool.cond_false] at h
  intro u hu
  rw [nodeTerms_of_le h.2.1] at hu
  exact termsOk_assert hv _ _ h.2.2 ha u hu

/-- Accepted gates from index `g`: the `j`-th carries index `g + j` and is accepted. -/
theorem gatesOk_get {w : ℕ} {D : Dag} {Tp Tc : Table} {wp : ℕ} :
    ∀ (g : ℕ) (cs : List ℕ), gatesOk w D Tp wp Tc g cs = true →
      ∀ j < cs.length, gateIndex w (cs.getD j 0) = g + j ∧
        gateOk w D Tp wp Tc (cs.getD j 0) = true
  | _, [], _, j, hj => by simp at hj
  | g, c :: cs, h, j, hj => by
    simp only [gatesOk, Bool.and_eq_true, Nat.beq_eq] at h
    obtain ⟨⟨hi, hc⟩, hrest⟩ := h
    cases j with
    | zero => simpa using ⟨hi, hc⟩
    | succ j =>
      have := gatesOk_get _ cs hrest j (by simpa using hj)
      rw [hi] at this
      simpa [Nat.add_assoc, Nat.add_comm 1 j] using this

/-- An accepted layer carries its nodes. -/
theorem layerOk_carried {w : ℕ} {D : Dag} {κ x : ℕ → F} {Tp Tc : Table} {wp : ℕ} {l : List ℕ}
    {v : ℕ → F} (hκ : κ 1 = 1) (hone : D.val w κ x 0 = 1) (hv : Carried w D κ x Tp wp v)
    (h : layerOk w D Tp wp Tc l = true) :
    Carried w D κ x Tc l.length (layerValue w κ l v) := by
  intro g hg
  obtain ⟨hi, hc⟩ := gatesOk_get 0 l h g hg
  rw [Nat.zero_add] at hi
  rw [layerValue, gateOk_value hκ hone hv hc, ← gateOk_cell hc, hi]

/-- Every node a satisfied, accepted layer adds to the collected assertions holds. -/
theorem collectGates_mem {w : ℕ} {D : Dag} {κ x : ℕ → F} {Tp Tc : Table} {wp : ℕ} {v : ℕ → F}
    (hv : Carried w D κ x Tp wp v) :
    ∀ (g : ℕ) (cs acc : List ℕ), gatesOk w D Tp wp Tc g cs = true →
      (∀ j < cs.length, ∀ t ∈ gateTerms w (cs.getD j 0), t.k = 0 → v t.a * v t.b = 0) →
        (∀ n ∈ acc, D.AssertHolds w κ x n) →
          ∀ n ∈ collectGates w cs acc, D.AssertHolds w κ x n
  | _, [], _, _, _, hacc => hacc
  | g, c :: cs, acc, h, ha, hacc => by
    simp only [gatesOk, Bool.and_eq_true] at h
    refine collectGates_mem hv _ cs _ h.2
      (fun j hj => ha (j + 1) (by simpa using hj)) ?_
    cases hc : (!flagged w c && hasAssert (gateTerms w c))
    · simpa using hacc
    · simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
      intro n hn
      rcases List.mem_cons.mp hn with rfl | hn
      · exact gateOk_assert hv h.1.2 hc.1 (ha 0 (by simp))
      · exact hacc n hn

/-- Soundness of the layers: from a carried depth, every asserted node the rest of the circuit
carries holds, when the rest of the circuit is satisfied. -/
theorem layersOk_sound {w : ℕ} {D : Dag} {κ x : ℕ → F} {outs : List (ℕ × ℕ)} {outw : List ℕ}
    (hκ : κ 1 = 1) (hone : D.val w κ x 0 = 1) :
    ∀ (Tp : Table) (wp : ℕ) (Ts : List Table) (ls : List (List ℕ)) (v : ℕ → F) (acc : List ℕ),
      layersOk w D outs outw Tp wp Ts ls = true → Carried w D κ x Tp wp v → Sat w κ ls v →
        (∀ n ∈ acc, D.AssertHolds w κ x n) →
          ∀ n ∈ collect w ls acc, D.AssertHolds w κ x n
  | Tp, wp, [], [], v, acc, h, hv, hs, hacc => by
    simpa [collect] using hacc
  | Tp, wp, T :: Ts, l :: ls, v, acc, h, hv, hs, hacc => by
    simp only [layersOk, Bool.and_eq_true] at h
    simp only [collect]
    exact layersOk_sound hκ hone T l.length Ts ls (layerValue w κ l v) _ h.2
      (layerOk_carried hκ hone hv h.1) hs.2
      (collectGates_mem hv 0 l acc h.1 hs.1 hacc)
  | _, _, [], _ :: _, _, _, h, _, _, _ => by simp [layersOk] at h
  | _, _, _ :: _, [], _, _, h, _, _, _ => by simp [layersOk] at h

/-- The last depth: its table and width, after the layers. -/
theorem layersOk_outputs {w : ℕ} {D : Dag} {κ x : ℕ → F} {outs : List (ℕ × ℕ)} {outw : List ℕ}
    (hκ : κ 1 = 1) (hone : D.val w κ x 0 = 1) :
    ∀ (Tp : Table) (wp : ℕ) (Ts : List Table) (ls : List (List ℕ)) (v : ℕ → F),
      layersOk w D outs outw Tp wp Ts ls = true → Carried w D κ x Tp wp v → Sat w κ ls v →
        ∀ o ∈ outs, D.AssertHolds w κ x o.2
  | Tp, wp, [], [], v, h, hv, hs, o, ho => by
    simp only [layersOk, Bool.and_eq_true, List.all_eq_true] at h
    have h := h.1 o ho
    simp only [outputOk, Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨⟨hg, hle⟩, h⟩ := h
    intro u hu _
    rw [nodeTerms_of_le hle] at hu
    generalize hts : terms w (D.tree.get o.2) = ts at h hu
    match ts, h, hu with
    | [t], h, hu =>
      rw [List.mem_singleton.mp hu]
      have hz : D.val w κ x (cell w Tp o.1) = 0 := by rw [← hv _ hg]; exact hs o.1
      simp only [Bool.and_eq_true, Nat.beq_eq] at h
      rw [← h.2, hz, mul_zero]
  | Tp, wp, T :: Ts, l :: ls, v, h, hv, hs, o, ho => by
    simp only [layersOk, Bool.and_eq_true] at h
    exact layersOk_outputs hκ hone T l.length Ts ls (layerValue w κ l v) h.2
      (layerOk_carried hκ hone hv h.1) hs.2 o ho
  | _, _, [], _ :: _, _, h, _, _, _, _ => by simp [layersOk] at h
  | _, _, _ :: _, [], _, h, _, _, _, _ => by simp [layersOk] at h

/-- Output nodes on zero output wires are zero. -/
theorem outWiresOk_zero {w : ℕ} {D : Dag} {κ x : ℕ → F} {T : Table} {wl : ℕ} {v : ℕ → F}
    (hv : Carried w D κ x T wl v) (hz : ∀ g, v g = 0) :
    ∀ ns gs, outWiresOk w T wl ns gs = true → ∀ n ∈ ns, D.val w κ x n = 0
  | [], [], _ => by simp
  | n :: ns, g :: gs, h => by
    simp only [outWiresOk, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
    obtain ⟨⟨hg, hn⟩, hrest⟩ := h
    intro m hm
    rcases List.mem_cons.mp hm with rfl | hm
    · rw [← hn, ← hv _ hg, hz]
    · exact outWiresOk_zero hv hz ns gs hrest m hm
  | [], _ :: _, h => by simp [outWiresOk] at h
  | _ :: _, [], h => by simp [outWiresOk] at h

/-- The output nodes vanish when the circuit is satisfied. -/
theorem layersOk_outWires {w : ℕ} {D : Dag} {κ x : ℕ → F} {outs : List (ℕ × ℕ)} {outw : List ℕ}
    (hκ : κ 1 = 1) (hone : D.val w κ x 0 = 1) :
    ∀ (Tp : Table) (wp : ℕ) (Ts : List Table) (ls : List (List ℕ)) (v : ℕ → F),
      layersOk w D outs outw Tp wp Ts ls = true → Carried w D κ x Tp wp v → Sat w κ ls v →
        ∀ n ∈ D.outputs, D.val w κ x n = 0
  | Tp, wp, [], [], v, h, hv, hs => by
    simp only [layersOk, Bool.and_eq_true] at h
    exact outWiresOk_zero hv hs _ _ h.2
  | Tp, wp, T :: Ts, l :: ls, v, h, hv, hs => by
    simp only [layersOk, Bool.and_eq_true] at h
    exact layersOk_outWires hκ hone T l.length Ts ls (layerValue w κ l v) h.2
      (layerOk_carried hκ hone hv h.1) hs.2
  | _, _, [], _ :: _, _, h, _, _ => by simp [layersOk] at h
  | _, _, _ :: _, [], _, h, _, _ => by simp [layersOk] at h

/-- `listEq` decides list equality. -/
theorem listEq_eq : ∀ a b : List ℕ, listEq a b = true → a = b
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [listEq, Bool.and_eq_true, Nat.beq_eq] at h
    rw [h.1, listEq_eq as bs h.2]
  | [], _ :: _, h => by simp [listEq] at h
  | _ :: _, [], h => by simp [listEq] at h

/-- A merge keeps only elements of its inputs. -/
theorem mem_mergeNat {n : ℕ} : ∀ (f : ℕ) (xs ys : List ℕ), n ∈ mergeNat f xs ys → n ∈ xs ∨ n ∈ ys
  | 0, xs, ys, h => List.mem_append.mp h
  | _ + 1, [], ys, h => Or.inr h
  | _ + 1, x :: xs, [], h => Or.inl h
  | f + 1, x :: xs, y :: ys, h => by
    simp only [mergeNat] at h
    cases hb : Nat.ble x y
    · rw [hb, Bool.cond_false] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact Or.inr (List.mem_cons_self ..)
      · rcases mem_mergeNat f (x :: xs) ys h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)
    · rw [hb, Bool.cond_true] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact Or.inl (List.mem_cons_self ..)
      · rcases mem_mergeNat f xs (y :: ys) h with h | h
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · exact Or.inr h

/-- Pairwise merging keeps only elements of the runs. -/
theorem mem_mergePairs {n : ℕ} : ∀ ls : List (List ℕ), n ∈ (mergePairs ls).flatten → n ∈ ls.flatten
  | a :: b :: rest, h => by
    simp only [mergePairs, List.flatten_cons, List.mem_append] at h ⊢
    rcases h with h | h
    · rcases mem_mergeNat _ a b h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (mem_mergePairs rest h))
  | [], h => h
  | [_], h => h

/-- Merging all runs keeps only elements of the runs. -/
theorem mem_mergeAll {n : ℕ} : ∀ (f : ℕ) (ls : List (List ℕ)), n ∈ mergeAll f ls → n ∈ ls.flatten
  | _, [], h => by simp [mergeAll] at h
  | _, [a], h => by simpa [mergeAll] using h
  | 0, _ :: _ :: _, h => h
  | f + 1, a :: b :: rest, h => mem_mergePairs _ (mem_mergeAll f _ h)

/-- Sorting keeps only elements of the input. -/
theorem mem_of_mem_sortNat {n : ℕ} {l : List ℕ} (h : n ∈ sortNat l) : n ∈ l := by
  have := mem_mergeAll _ _ h
  simpa using this

/-- **Soundness of the certificate checker.** If `check` accepts, the constant `1` has index
`1` and the input `0` is one, then on every input on which the layered circuit is satisfied every
assertion of the DAG holds and every output node of the DAG is zero. -/
theorem check_sound {D : Dag} {C : Layered} {K : Cert} (h : check D C K = true)
    {κ x : ℕ → F} (hκ : κ 1 = 1) (hx : x 0 = 1)
    (hs : C.Satisfied K.width κ x) : D.Holds K.width κ x := by
  simp only [check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hone, hin⟩, hlay⟩, hasrt⟩, -⟩ := h
  have hone' := val_zero (w := K.width) (κ := κ) hone hx
  have hv : Carried K.width D κ x .ident C.inputs x := by
    intro g hg
    have hi : Nat.blt g D.inputs = true := by
      simp only [Nat.beq_eq] at hin
      simpa [Nat.blt_eq, ← hin] using hg
    rw [cell, Dag.val_eq, hi, Bool.cond_true]
  refine ⟨fun n hn => ?_,
    layersOk_outWires hκ hone' Table.ident C.inputs K.tables C.layers x hlay hv hs⟩
  rw [listEq_eq _ _ hasrt] at hn
  replace hn := mem_of_mem_sortNat hn
  refine layersOk_sound hκ hone' Table.ident C.inputs K.tables C.layers x _ hlay hv hs
    ?_ n hn
  intro m hm
  obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hm
  exact layersOk_outputs hκ hone' Table.ident C.inputs K.tables C.layers x hlay hv hs o ho

/-- Collecting a layer keeps the accumulated nodes. -/
theorem mem_collectGates_of_acc {w n : ℕ} :
    ∀ (cs acc : List ℕ), n ∈ acc → n ∈ collectGates w cs acc
  | [], _, h => h
  | c :: cs, acc, h => by
    simp only [collectGates]
    refine mem_collectGates_of_acc cs _ ?_
    cases (!flagged w c && hasAssert (gateTerms w c))
    · exact h
    · exact List.mem_cons_of_mem _ h

/-- Collecting the layers keeps the accumulated nodes. -/
theorem mem_collect_of_acc {w n : ℕ} :
    ∀ (ls : List (List ℕ)) (acc : List ℕ), n ∈ acc → n ∈ collect w ls acc
  | [], _, h => h
  | l :: ls, acc, h => mem_collect_of_acc ls _ (mem_collectGates_of_acc l acc h)

/-- Collecting a layer adds the node of each of its non-copy gates with an assertion term. -/
theorem gateNode_mem_collectGates {w : ℕ} :
    ∀ (cs acc : List ℕ) (j : ℕ), j < cs.length → flagged w (cs.getD j 0) = false →
      hasAssert (gateTerms w (cs.getD j 0)) = true →
        gateNode w (cs.getD j 0) ∈ collectGates w cs acc
  | [], _, _, hj, _, _ => by simp at hj
  | c :: cs, acc, 0, _, hf, ha => by
    simp only [List.getD_cons_zero] at hf ha ⊢
    simp only [collectGates, hf, ha, Bool.not_false, Bool.and_self, Bool.cond_true]
    exact mem_collectGates_of_acc cs _ (List.mem_cons_self ..)
  | c :: cs, acc, j + 1, hj, hf, ha => by
    simp only [List.getD_cons_succ] at hf ha ⊢
    exact gateNode_mem_collectGates cs _ j (by simpa using hj) hf ha

/-- Accepted term lists agree on whether they have an assertion term (their constant indices are
pairwise equal). -/
theorem termsOk_hasAssert {w : ℕ} {T : Table} {wp r : ℕ} :
    ∀ ts us, termsOk w T wp r ts us = true → hasAssert ts = hasAssert us
  | [], [], _ => rfl
  | t :: ts, u :: us, h => by
    simp only [termsOk, Bool.and_eq_true, Nat.beq_eq] at h
    simp only [hasAssert, h.1.1.1.1.1.1, termsOk_hasAssert ts us h.2]
  | [], _ :: _, h => by simp [termsOk] at h
  | _ :: _, [], h => by simp [termsOk] at h

/-- **A node carried by a wire of an accepted layer is collected**: if every wire of the previous
depth carrying the node `n` (a node with an assertion term) has it in `acc`, every
wire of the layer carrying `n` has it in the layer's collected nodes. A copy wire reads a wire of
the previous depth carrying `n`; a non-copy wire's gate has `n`'s terms, so an assertion term. -/
theorem mem_collectGates_of_cell {w : ℕ} {D : Dag} {Tp Tc : Table} {wp n : ℕ} {l acc : List ℕ}
    (ha : hasAssert (terms w (D.tree.get n)) = true)
    (h : layerOk w D Tp wp Tc l = true) (hinv : ∀ g < wp, cell w Tp g = n → n ∈ acc) :
    ∀ g < l.length, cell w Tc g = n → n ∈ collectGates w l acc := by
  intro g hg hc
  obtain ⟨hi, hok⟩ := gatesOk_get 0 l h g hg
  rw [Nat.zero_add] at hi
  have hnode : gateNode w (l.getD g 0) = n := by rw [← gateOk_cell hok, hi, hc]
  unfold gateOk at hok
  simp only [Bool.and_eq_true] at hok
  cases hf : flagged w (l.getD g 0)
  · rw [hf, Bool.cond_false] at hok
    simp only [Bool.and_eq_true] at hok
    have hk := termsOk_hasAssert _ _ hok.2.2
    rw [hnode] at hk
    rw [← hnode]
    exact gateNode_mem_collectGates l acc g hg hf (hk.trans ha)
  · rw [hf, Bool.cond_true] at hok
    have hcp := hok.2
    rw [hnode] at hcp
    apply mem_collectGates_of_acc
    generalize gateTerms w (l.getD g 0) = ts at hcp
    match ts, hcp with
    | [t], hcp =>
      simp only [copyOk, carries, Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq,
        Nat.blt_eq] at hcp
      obtain ⟨⟨⟨_, hta⟩, htb⟩, hc'⟩ := hcp
      rcases hc' with ⟨_, h2⟩ | ⟨h1, _⟩
      · exact hinv _ htb h2
      · exact hinv _ hta h1

/-- **A node carried by a wire below its layer's width is collected** (`mem_collectGates_of_cell`
layer by layer): the node `n`, a node with an assertion term, carried by wire
`g` of layer `d`, is among the collected nodes of accepted layers. -/
theorem mem_collect_of_cell {w : ℕ} {D : Dag} {outs : List (ℕ × ℕ)} {outw : List ℕ} {n : ℕ}
    (ha : hasAssert (terms w (D.tree.get n)) = true) :
    ∀ (Tp : Table) (wp : ℕ) (Ts : List Table) (ls : List (List ℕ)) (acc : List ℕ),
      layersOk w D outs outw Tp wp Ts ls = true → (∀ g < wp, cell w Tp g = n → n ∈ acc) →
        ∀ d g, g < (ls.getD d []).length → cell w (Ts.getD d .ident) g = n →
          n ∈ collect w ls acc
  | _, _, [], [], _, _, _, d, g, hg, _ => by simp at hg
  | Tp, wp, T :: Ts, l :: ls, acc, h, hinv, d, g, hg, hc => by
    simp only [layersOk, Bool.and_eq_true] at h
    have hinv' := mem_collectGates_of_cell ha h.1 hinv
    simp only [collect]
    cases d with
    | zero => exact mem_collect_of_acc ls _ (hinv' g (by simpa using hg) (by simpa using hc))
    | succ d =>
      exact mem_collect_of_cell ha T l.length Ts ls _ h.2 hinv' d g (by simpa using hg)
        (by simpa using hc)
  | _, _, [], _ :: _, _, h, _, _, _, _, _ => by simp [layersOk] at h
  | _, _, _ :: _, [], _, h, _, _, _, _, _ => by simp [layersOk] at h

end Soundness

/-! ## The sort

`sortNat` is a sorted permutation of its input. -/

section SortNat

/-- With enough fuel, `mergeNat` is `List.merge` by `Nat.ble`. -/
theorem mergeNat_eq_merge :
    ∀ (f : ℕ) (xs ys : List ℕ), xs.length + ys.length ≤ f →
      mergeNat f xs ys = xs.merge ys fun a b => Nat.ble a b
  | 0, [], [], _ => by simp [mergeNat]
  | 0, _ :: _, _, h => by simp at h
  | 0, [], _ :: _, h => by simp at h
  | _ + 1, [], ys, _ => by simp [mergeNat]
  | _ + 1, x :: xs, [], _ => by simp [mergeNat]
  | f + 1, x :: xs, y :: ys, h => by
    simp only [List.length_cons] at h
    rw [mergeNat, List.cons_merge_cons]
    cases hb : Nat.ble x y
    · simp only [Bool.cond_false, Bool.false_eq_true, ↓reduceIte]
      rw [mergeNat_eq_merge f (x :: xs) ys (by simp; omega)]
    · simp only [Bool.cond_true, ↓reduceIte]
      rw [mergeNat_eq_merge f xs (y :: ys) (by simp; omega)]

private theorem ble_trans (a b c : ℕ) (h₁ : Nat.ble a b = true) (h₂ : Nat.ble b c = true) :
    Nat.ble a c = true := by
  simp only [Nat.ble_eq] at *
  omega

private theorem ble_total (a b : ℕ) : (Nat.ble a b || Nat.ble b a) = true := by
  simp only [Bool.or_eq_true, Nat.ble_eq]
  omega

/-- Pairwise merging keeps the runs sorted, their elements, and halves their number. -/
theorem mergePairs_spec :
    ∀ ls : List (List ℕ), (∀ r ∈ ls, r.Pairwise fun a b => Nat.ble a b = true) →
      (∀ r ∈ mergePairs ls, r.Pairwise fun a b => Nat.ble a b = true) ∧ (mergePairs ls).flatten.Perm ls.flatten ∧
        (mergePairs ls).length = (ls.length + 1) / 2
  | [], _ => ⟨by simp [mergePairs], by simp [mergePairs], by simp [mergePairs]⟩
  | [a], h => ⟨by simpa [mergePairs] using h, by simp [mergePairs], by simp [mergePairs]⟩
  | a :: b :: rest, h => by
    have ha : a.Pairwise _ := h a (by simp)
    have hb : b.Pairwise _ := h b (by simp)
    obtain ⟨h₁, h₂, h₃⟩ := mergePairs_spec rest fun r hr => h r (by simp [hr])
    rw [mergePairs, mergeNat_eq_merge _ a b (Nat.le_refl _)]
    refine ⟨?_, ?_, ?_⟩
    · intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact List.pairwise_merge ble_trans ble_total a b ha hb
      · exact h₁ r hr
    · simp only [List.flatten_cons, ← List.append_assoc]
      exact List.Perm.append (List.merge_perm_append _) h₂
    · simp only [List.length_cons, h₃]
      omega

/-- With enough fuel, merging all runs gives one sorted run with their elements. -/
theorem mergeAll_spec :
    ∀ (f : ℕ) (ls : List (List ℕ)), (∀ r ∈ ls, r.Pairwise fun a b => Nat.ble a b = true) →
      ls.length ≤ f + 1 →
      (mergeAll f ls).Pairwise (fun a b => Nat.ble a b = true) ∧
        (mergeAll f ls).Perm ls.flatten
  | _, [], _, _ => ⟨by simp [mergeAll], by simp [mergeAll]⟩
  | _, [a], h, _ => ⟨by simpa [mergeAll] using h a (by simp), by simp [mergeAll]⟩
  | 0, _ :: _ :: _, _, hl => by simp at hl
  | f + 1, a :: b :: rest, h, hl => by
    obtain ⟨h₁, h₂, h₃⟩ := mergePairs_spec (a :: b :: rest) h
    obtain ⟨r₁, r₂⟩ := mergeAll_spec f (mergePairs (a :: b :: rest)) h₁
      (by rw [h₃]; simp only [List.length_cons] at hl ⊢; omega)
    exact ⟨r₁, r₂.trans h₂⟩

/-- The singleton runs of a list, joined, are the list. -/
theorem flatten_singletons : ∀ l : List ℕ, (l.map fun n => [n]).flatten = l
  | [] => rfl
  | a :: l => by simp [flatten_singletons l]

/-- **`sortNat` sorts**. -/
theorem pairwise_sortNat (l : List ℕ) : (sortNat l).Pairwise (· ≤ ·) :=
  ((mergeAll_spec _ _ (by simp) (by simp)).1).imp fun h => Nat.le_of_ble_eq_true h

/-- **`sortNat` permutes**. -/
theorem perm_sortNat (l : List ℕ) : (sortNat l).Perm l := by
  have := (mergeAll_spec l.length (l.map fun n => [n]) (by simp) (by simp)).2
  rwa [flatten_singletons] at this

/-- `listEq` is reflexive. -/
theorem listEq_refl : ∀ l : List ℕ, listEq l l = true
  | [] => rfl
  | a :: as => by simp [listEq, listEq_refl as]

end SortNat

/-! ## Checking in slices

A large circuit is checked by theorems that each read a bounded part of it, composed by the lemmas
below with no re-check: the layers' gates in slices (`layerSliceOk`, above), per layer its gate count
and asserting-gate count in slices (`layersCountB`), and the asserted nodes in slices of witnesses
(`assertSliceOk`). `assertsOk_of_cover` gives `assertsOk` from them without sorting: the asserted
nodes increase, each is collected (its witness), and there are no more collected nodes than
asserted ones, so the collected nodes, sorted, are the asserted ones. -/

section Slices

/-- **The `n` entries of `l` from position `s`** (every entry from `s` on when `n = 0`). -/
def sliceL (l : List ℕ) (s n : ℕ) : List ℕ := cond (Nat.beq n 0) (l.drop s) ((l.drop s).take n)

/-- A slice and the rest after it are the rest from the slice's start. -/
theorem sliceL_append {l : List ℕ} {s n : ℕ} (hn : 0 < n) :
    sliceL l s n ++ sliceL l (s + n) 0 = sliceL l s 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hb : Nat.beq (m + 1) 0 = false := rfl
  simp only [sliceL, hb, Nat.beq_refl, Bool.cond_true, Bool.cond_false]
  rw [← List.drop_drop]
  exact List.take_append_drop _ _

/-- The slice from position `0` on is the list. -/
@[simp] theorem sliceL_zero (l : List ℕ) : sliceL l 0 0 = l := by simp [sliceL]

/-- The number of a layer's non-copy gates with an assertion term, the nodes `collectGates`
adds. -/
def countGates (w : ℕ) : List ℕ → ℕ
  | [] => 0
  | c :: cs => cond (!flagged w c && hasAssert (gateTerms w c)) 1 0 + countGates w cs

/-- The count of a concatenation. -/
theorem countGates_append (w : ℕ) :
    ∀ l₁ l₂ : List ℕ, countGates w (l₁ ++ l₂) = countGates w l₁ + countGates w l₂
  | [], _ => by simp [countGates]
  | c :: cs, l₂ => by simp only [List.cons_append, countGates, countGates_append w cs l₂]; omega

/-- `collectGates` adds `countGates` nodes. -/
theorem length_collectGates (w : ℕ) :
    ∀ cs acc : List ℕ, (collectGates w cs acc).length = acc.length + countGates w cs
  | [], _ => by simp [collectGates, countGates]
  | c :: cs, acc => by
    simp only [collectGates, countGates, length_collectGates w cs]
    cases (!flagged w c && hasAssert (gateTerms w c)) <;> simp; omega

/-- **Per layer, its gate count and asserting-gate count.** -/
def layersCountB (w : ℕ) : List (List ℕ) → List ℕ → List ℕ → Bool
  | [], [], [] => true
  | l :: ls, m :: ms, c :: cs =>
    Nat.beq l.length m && Nat.beq (countGates w l) c && layersCountB w ls ms cs
  | _, _, _ => false

/-- The layers' gate counts. -/
theorem map_length_of_layersCountB {w : ℕ} :
    ∀ {ls : List (List ℕ)} {ms cs : List ℕ}, layersCountB w ls ms cs = true →
      ls.map List.length = ms
  | [], [], [], _ => rfl
  | l :: ls, m :: ms, c :: cs, h => by
    simp only [layersCountB, Bool.and_eq_true, Nat.beq_eq] at h
    simp [h.1.1, map_length_of_layersCountB h.2]
  | [], _ :: _, _, h | [], [], _ :: _, h | _ :: _, [], _, h | _ :: _, _ :: _, [], h => by
    simp [layersCountB] at h

/-- The collected nodes' count. -/
theorem length_collect_of_layersCountB {w : ℕ} :
    ∀ {ls : List (List ℕ)} {ms cs : List ℕ} (acc : List ℕ), layersCountB w ls ms cs = true →
      (collect w ls acc).length = acc.length + cs.sum
  | [], [], [], _, _ => by simp [collect]
  | l :: ls, m :: ms, c :: cs, acc, h => by
    simp only [layersCountB, Bool.and_eq_true, Nat.beq_eq] at h
    rw [collect, length_collect_of_layersCountB _ h.2, length_collectGates, h.1.2,
      List.sum_cons]
    omega
  | [], _ :: _, _, _, h | [], [], _ :: _, _, h | _ :: _, [], _, _, h
  | _ :: _, _ :: _, [], _, h => by simp [layersCountB] at h

/-- **`lo < l₀ < l₁ < ⋯`, the last of `lo :: l` being `hi`.** -/
def chainLast : ℕ → List ℕ → ℕ → Bool
  | lo, [], hi => Nat.beq lo hi
  | lo, x :: xs, hi => Nat.blt lo x && chainLast x xs hi

/-- Chains join at their common end. -/
theorem chainLast_append :
    ∀ {lo mid hi : ℕ} {l₁ l₂ : List ℕ}, chainLast lo l₁ mid = true →
      chainLast mid l₂ hi = true → chainLast lo (l₁ ++ l₂) hi = true
  | lo, mid, hi, [], l₂, h₁, h₂ => by
    simp only [chainLast, Nat.beq_eq] at h₁
    subst h₁
    exact h₂
  | lo, mid, hi, x :: xs, l₂, h₁, h₂ => by
    simp only [chainLast, Bool.and_eq_true] at h₁
    simp only [List.cons_append, chainLast, Bool.and_eq_true]
    exact ⟨h₁.1, chainLast_append h₁.2 h₂⟩

/-- A chain increases, above its start. -/
theorem pairwise_of_chainLast :
    ∀ {lo hi : ℕ} {l : List ℕ}, chainLast lo l hi = true →
      (∀ x ∈ l, lo < x) ∧ l.Pairwise (· < ·)
  | _, _, [], _ => by simp
  | lo, hi, x :: xs, h => by
    simp only [chainLast, Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨h₁, h₂⟩ := pairwise_of_chainLast h.2
    refine ⟨fun y hy => ?_, List.pairwise_cons.mpr ⟨h₁, h₂⟩⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · exact h.1
    · exact Nat.lt_trans h.1 (h₁ y hy)

/-- **A witness that the asserted node `n` is collected** by the layers `Ts`, of widths `ws`:
`(0, j)`, the node of the `j`-th last-layer assertion `outs`; `(d + 1, g)`, a wire `g` below
the width of layer `d` whose table entry is `n`, a node with an assertion term. Either way `n` is
at or above the inputs. -/
def assertWitOk (w : ℕ) (D : Dag) (outs : List (ℕ × ℕ)) (Ts : List Table) (ws : List ℕ) (n : ℕ)
    (p : ℕ × ℕ) : Bool :=
  Nat.ble D.inputs n &&
    cond (Nat.beq p.1 0) (Nat.beq (outs.getD p.2 (0, 0)).2 n)
      (hasAssert (terms w (D.tree.get n)) && Nat.blt p.2 (ws.getD (p.1 - 1) 0) &&
        Nat.beq (cell w (Ts.getD (p.1 - 1) .ident) p.2) n)

/-- Witnesses for a list of asserted nodes, one each. -/
def witsOk (w : ℕ) (D : Dag) (outs : List (ℕ × ℕ)) (Ts : List Table) (ws : List ℕ) :
    List ℕ → List (ℕ × ℕ) → Bool
  | [], [] => true
  | n :: ns, p :: ps => assertWitOk w D outs Ts ws n p && witsOk w D outs Ts ws ns ps
  | _, _ => false

/-- Every node with accepted witnesses has one. -/
theorem witsOk_mem {w : ℕ} {D : Dag} {outs : List (ℕ × ℕ)} {Ts : List Table} {ws : List ℕ} :
    ∀ {ns : List ℕ} {ps : List (ℕ × ℕ)}, witsOk w D outs Ts ws ns ps = true →
      ∀ x ∈ ns, ∃ p, assertWitOk w D outs Ts ws x p = true
  | [], _, _, x, hx => by simp at hx
  | n :: ns, p :: ps, h, x, hx => by
    simp only [witsOk, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨p, h.1⟩
    · exact witsOk_mem h.2 x hx
  | _ :: _, [], h, _, _ => by simp [witsOk] at h

/-- **A slice of the asserted nodes**: the `n` from position `s` (every one from `s` on when
`n = 0`) increase from above `lo` to `hi`, with the witnesses `wit`. -/
def assertSliceOk (w : ℕ) (D : Dag) (outs : List (ℕ × ℕ)) (Ts : List Table) (ws : List ℕ)
    (s n lo hi : ℕ) (wit : List (ℕ × ℕ)) : Bool :=
  chainLast lo (sliceL D.asserts s n) hi && witsOk w D outs Ts ws (sliceL D.asserts s n) wit

/-- **The asserted nodes from position `s` on** increase from above `lo` to `hi`, each with a
witness. -/
def AssertsFrom (w : ℕ) (D : Dag) (outs : List (ℕ × ℕ)) (Ts : List Table) (ws : List ℕ)
    (s lo hi : ℕ) : Prop :=
  chainLast lo (sliceL D.asserts s 0) hi = true ∧
    ∀ x ∈ sliceL D.asserts s 0, ∃ p, assertWitOk w D outs Ts ws x p = true

/-- The last slice. -/
theorem assertsFrom_of_slice {w : ℕ} {D : Dag} {outs : List (ℕ × ℕ)} {Ts : List Table}
    {ws : List ℕ} {s lo hi : ℕ} {wit : List (ℕ × ℕ)}
    (h : assertSliceOk w D outs Ts ws s 0 lo hi wit = true) : AssertsFrom w D outs Ts ws s lo hi := by
  simp only [assertSliceOk, Bool.and_eq_true] at h
  exact ⟨h.1, witsOk_mem h.2⟩

/-- A slice, then the rest after it. -/
theorem assertsFrom_cons {w : ℕ} {D : Dag} {outs : List (ℕ × ℕ)} {Ts : List Table}
    {ws : List ℕ} {s n lo mid hi : ℕ} {wit : List (ℕ × ℕ)} (hn : 0 < n)
    (h : assertSliceOk w D outs Ts ws s n lo mid wit = true)
    (h' : AssertsFrom w D outs Ts ws (s + n) mid hi) : AssertsFrom w D outs Ts ws s lo hi := by
  simp only [assertSliceOk, Bool.and_eq_true] at h
  rw [AssertsFrom, ← sliceL_append hn]
  refine ⟨chainLast_append h.1 h'.1, fun x hx => ?_⟩
  rcases List.mem_append.mp hx with hx | hx
  · exact witsOk_mem h.2 x hx
  · exact h'.2 x hx

/-- **The asserted nodes from slices**: if the asserted nodes increase and each has a witness,
the layers are accepted with the gate counts `ms` and asserting-gate counts `cs`, and there are no
more last-layer assertions and asserting gates than asserted nodes, then `assertsOk` accepts. -/
theorem assertsOk_of_cover {D : Dag} {C : Layered} {K : Cert} {ms cs : List ℕ} {hi : ℕ}
    (hone : oneOk D = true) (hin : Nat.beq C.inputs D.inputs = true)
    (hlay : layersOk K.width D K.outputs K.outWires .ident C.inputs K.tables C.layers = true)
    (hcnt : layersCountB K.width C.layers ms cs = true)
    (hcov : AssertsFrom K.width D K.outputs K.tables ms 0 0 hi)
    (hlen : Nat.ble (K.outputs.length + cs.sum) D.asserts.length = true) :
    assertsOk D C K = true := by
  obtain ⟨hch, hwit⟩ := hcov
  rw [sliceL_zero] at hch hwit
  have hsorted := (pairwise_of_chainLast hch).2
  have hD0 : 0 < D.inputs := by simpa [oneOk] using hone
  have hsub : D.asserts ⊆ collect K.width C.layers (K.outputs.map Prod.snd) := by
    intro n hn
    obtain ⟨p, hp⟩ := hwit n hn
    simp only [assertWitOk, Bool.and_eq_true] at hp
    obtain ⟨hle, hp⟩ := hp
    cases h0 : Nat.beq p.1 0
    · rw [h0, Bool.cond_false] at hp
      simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hp
      obtain ⟨⟨ha, hg⟩, hc⟩ := hp
      have hws : (C.layers.getD (p.1 - 1) []).length = ms.getD (p.1 - 1) 0 := by
        rw [← map_length_of_layersCountB hcnt]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
        cases C.layers[p.1 - 1]? <;> rfl
      refine mem_collect_of_cell ha _ _ _ _ _ hlay (fun g hg' hc' => ?_) (p.1 - 1) p.2
        (hws ▸ hg) hc
      simp only [Nat.ble_eq, Nat.beq_eq] at hle hin
      simp only [cell] at hc'
      omega
    · rw [h0, Bool.cond_true, Nat.beq_eq] at hp
      refine mem_collect_of_acc _ _ (List.mem_map.mpr ?_)
      by_cases hj : p.2 < K.outputs.length
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at hp
        exact ⟨_, List.getElem_mem hj, hp⟩
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hp
        simp only [Nat.ble_eq] at hle
        simp at hp
        omega
  have hnd : D.asserts.Nodup := hsorted.imp Nat.ne_of_lt
  have hperm := (List.subperm_of_subset hnd hsub).perm_of_length_le (by
    rw [length_collect_of_layersCountB _ hcnt, List.length_map]
    simpa only [Nat.ble_eq] using hlen)
  have hsort : sortNat (collect K.width C.layers (K.outputs.map Prod.snd)) = D.asserts :=
    List.Perm.eq_of_pairwise (le := (· ≤ ·)) (fun a b _ _ h₁ h₂ => Nat.le_antisymm h₁ h₂)
      (pairwise_sortNat _) (hsorted.imp Nat.le_of_lt) ((perm_sortNat _).trans hperm.symm)
  rw [assertsOk, hsort]
  exact listEq_refl _

end Slices

end GordieHowe.GKR.Certificate
