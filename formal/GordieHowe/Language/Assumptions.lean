-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Realized
public import GordieHowe.ProofSystem.GKR.SourceCircuit

@[expose] public section

/-!
# GordieHowe: what a program's GKR circuits enforce

The trust bundle of the plan's GKR circuits at the level of the realized program (the paper's `sec:formal-assumptions`),
in two directions:

* **soundness** (`GordieHowe.RealizedProgram.CircuitsEnforce`): for every circuit `c` of the program, a GKR source
  circuit (`GordieHowe.RealizedProgram.CircuitSource`: input dimension `d`, the source `S`, its nodes and `hfit`, the
  circuit's inputs fit) whose satisfaction, on every input vector whose public positions hold the
  verifier's public input (`GordieHowe.RealizedProgram.publicInput`), gives the meaning of every entry of the circuit
  (`GordieHowe.RealizedProgram.CircuitHolds`) at the valuation decoded from the vector (`GordieHowe.RealizedProgram.inputValuation`); and
  the source has the circuit's shape (`ShapeAtMost` at the width `GordieHowe.RealizedProgram.circuitWidth` and the
  circuit's layers);
* **completeness** (`GordieHowe.RealizedProgram.CircuitsAccept`): the honest prover only. Wherever the circuit's entries
  hold at the reader of an environment of the layout, the source accepts the honest input vector
  (`GordieHowe.RealizedProgram.circuitInput`).

**The meaning of a circuit** (`GordieHowe.RealizedProgram.CircuitHolds`, entry by entry, `GordieHowe.RealizedProgram.EntryHolds`): a
Boolean check or a placed predicate holds (`GordieHowe.RealizedProgram.PlacedHolds`: a field `equal`, or a `mod_q`'s
field equation); a realization circuit holds (`GordieHowe.RealizedProgram.RealHolds`: the LogUp identity of a table
group at the weights `1/(α − j)`, or the H half of a cross-field `equal`). The alignment entries
constrain filler inputs, which no value reads; they carry no meaning here.

**Decoding an input vector** (`GordieHowe.RealizedProgram.inputValuation` at the statement `x` and the run `r`): a
committed value's coordinates are read from its committed block, a bit view's from its view block,
a public value's (a statement value, a constant, a public expression, a challenge value, a message)
from its public block; a late value is the run's message minus its pad, read from its pad block.
Every other coordinate (a value no block holds, a coordinate past a block, a value bound to its
digits) is the semantics' own reading (`GordieHowe.RealizedProgram.reader`) at the realized assignment
(`GordieHowe.RealizedProgram.bindAsg`) of the committed assignment decoded from the vector
(`GordieHowe.RealizedProgram.inputAssignment`). There is no Boolean or subfield restriction on the private inputs.
-/

namespace GordieHowe.RealizedProgram

open Export

/-! ## Casts between field identifiers -/


theorem castElt_of_ne {I : Interp} {a b : ℕ} (h : a ≠ b) (x : (I a).K) :
    (castElt x : (I b).K) = 0 :=
  dif_neg h


/-! ## Input blocks -/

namespace InputBlock

/-- **The input of coordinate `i` of value `v`** in a committed block of `v` holding it. -/
def committedPos (v i : ℕ) : InputBlock → Option ℕ
  | .committed u a n => if u = v ∧ i < n then some (a + i) else none
  | _ => none

/-- **The input of coordinate `i` of late value `v`'s pad** in a pad block of `v` holding it. -/
def padPos (v i : ℕ) : InputBlock → Option ℕ
  | .pad u a n => if u = v ∧ i < n then some (a + i) else none
  | _ => none

/-- **The input of coordinate `i` of value `v`** in a public block of `v` holding it. -/
def pubPos (v i : ℕ) : InputBlock → Option ℕ
  | .pub u a n => if u = v ∧ i < n then some (a + i) else none
  | _ => none

/-- **The input of coordinate `i` of bit view `v`** in a view block of `v` holding it. -/
def viewPos (v i : ℕ) : InputBlock → Option ℕ
  | .view u a n => if u = v ∧ i < n then some (a + i) else none
  | _ => none

/-- **The value of public input `j`** in a public block holding it: coordinate `j − at` of the
block's value read by `pv`, or of the realization input read by `rp`. -/
def pubValue? {K : Type} (pv : ℕ → ℕ → K) (rp : RealPub → ℕ → K) (j : ℕ) : InputBlock → Option K
  | .pub u a n => if a ≤ j ∧ j < a + n then some (pv u (j - a)) else none
  | .realizationPub w a n => if a ≤ j ∧ j < a + n then some (rp w (j - a)) else none
  | _ => none

/-- **The value of private input `j`** in a block holding it: a committed coordinate read by `cv`, a
pad by `pv`, a bit view by `vv`; zero for filler and batch pads. -/
def privValue? {K : Type} [Zero K] (cv pv vv : ℕ → ℕ → K) (j : ℕ) : InputBlock → Option K
  | .committed u a n => if a ≤ j ∧ j < a + n then some (cv u (j - a)) else none
  | .pad u a n => if a ≤ j ∧ j < a + n then some (pv u (j - a)) else none
  | .view u a n => if a ≤ j ∧ j < a + n then some (vv u (j - a)) else none
  | .batchPads _ a n => if a ≤ j ∧ j < a + n then some 0 else none
  | .filler a n => if a ≤ j ∧ j < a + n then some 0 else none
  | _ => none

end InputBlock

namespace Circuit

/-- The input of coordinate `i` of committed value `v` (its first committed block holding it). -/
def committedPos (c : Circuit) (v i : ℕ) : Option ℕ := c.inputs.findSome? (·.committedPos v i)

/-- The input of coordinate `i` of late value `v`'s pad. -/
def padPos (c : Circuit) (v i : ℕ) : Option ℕ := c.inputs.findSome? (·.padPos v i)

/-- The public input of coordinate `i` of value `v`. -/
def pubPos (c : Circuit) (v i : ℕ) : Option ℕ := c.inputs.findSome? (·.pubPos v i)

/-- The input of coordinate `i` of bit view `v`. -/
def viewPos (c : Circuit) (v i : ℕ) : Option ℕ := c.inputs.findSome? (·.viewPos v i)

/-- **Input `i` is public**: the constant one or a public block (`i < publicInputs`). -/
def IsPublicPos (c : Circuit) (i : ℕ) : Prop := i < c.publicInputs

instance (c : Circuit) (i : ℕ) : Decidable (c.IsPublicPos i) := inferInstanceAs (Decidable (_ < _))

end Circuit

/-- **Input `p` of a vector of `2^d` inputs**, `0` past its end. -/
def vecRead {K : Type} [Zero K] {d : ℕ} (v : Fin (2 ^ d) → K) (p : ℕ) : K :=
  if h : p < 2 ^ d then v ⟨p, h⟩ else 0

section

variable (ir : RealizedProgram) (I : Interp)

/-- **The field of circuit `c`**: its domain's. -/
abbrev circField (c : ℕ) : ℕ := ir.domainField (ir.circuit c).domain

/-! ## Realization circuits -/

/-- **The value holding challenge `j`**: the first value of kind `challenge j`. -/
def chalNode (j : ℕ) : Option ℕ :=
  (List.range ir.values.length).find? fun v =>
    match (ir.value v).kind with
    | .challenge c => c == j
    | _ => false

variable {I}

/-- **The LogUp identity of group `g` of table `t`** read by `rd` (`range.lookup:<D>.<T>[.g<k>]`):
`RealizedProgram.logupAt` at `α` coordinate `0` of the value holding the table's challenge (`chalNode`):
for a range, `Range.rangeArgument` on the group's needles and histograms (`RealizedProgram.groupNeedles`,
`RealizedProgram.staticHist`, `RealizedProgram.lateHist`) at the weights `(α − j)⁻¹`; for a committed table, the
identity with its denominators cleared (`Range.committedArgument`, the C++
`assert_log_derivative_committed`, `lib/gordiehowe/compiler/log_derivative.h`), every value read in
`α`'s field; the same identity as `RealizedProgram.LogupHolds` at an environment's reader
(`logupHoldsAt_reader_iff`). True when no value holds the challenge. -/
def LogupHoldsAt (rd : ir.Valuation I) (t g : ℕ) : Prop :=
  match ir.chalNode (ir.alphaOf t) with
  | some v => ir.logupAt rd t g (castElt (rd v 0)) = true
  | none => True

/-- **The value holding a challenge reads the challenge.** -/
theorem reader_chalNode (e : ir.Env I) {j v : ℕ} (hv : ir.chalNode j = some v)
    (hf : ir.valueField v = ir.chalField j) : (castElt (ir.reader e v 0) : (I (ir.chalField j)).K) =
      e.chal j 0 := by
  have hp := List.find?_some hv
  have hk : (ir.value v).kind = .challenge j := by
    revert hp
    cases (ir.value v).kind <;> simp
  simp only [reader, fuel, read, hk]
  exact castElt_castElt_of_eq hf.symm _

/-- **The LogUp identity at an environment's reader is `RealizedProgram.LogupHolds`**, when a value of the
challenge's field holds the table's challenge. -/
theorem logupHoldsAt_reader_iff (e : ir.Env I) {t g v : ℕ} (hv : ir.chalNode (ir.alphaOf t) = some v)
    (hf : ir.valueField v = ir.chalField (ir.alphaOf t)) :
    ir.LogupHoldsAt (ir.reader e) t g ↔ ir.LogupHolds e t g := by
  simp only [LogupHoldsAt, hv, LogupHolds, reader_chalNode (ir := ir) e hv hf]

/-- **The H half of cross-field `equal` `p` stated by the compiler's own circuit** at `rd`
(`RealCircuit.macH`, no `<mac>.H` predicate): `MacHHoldsAt` with the key read from the value
holding it (`chalNode`); false when no value holds the key; true when the H half is a predicate
(an ordinary `equal`) or `p` is no cross-field `equal`. -/
def MacHHolds (rd : ir.Valuation I) (p : ℕ) : Prop :=
  match (ir.predicate p).body with
  | .cross dx x _ _ _ real =>
    match real.hPredicate, ir.chalNode real.key with
    | none, some v => ir.MacHHoldsAt rd dx x real (castElt (rd v 0))
    | none, none => False
    | some _, _ => True
  | _ => True

/-- **A realization circuit holds** at `rd`: a LogUp identity (`LogupHoldsAt`), the H half of a
cross-field `equal` (`MacHHolds`). A circuit named only by its C++ name (`RealCircuit.named`) or not
modeled (`RealCircuit.unmodeled`) is given no meaning;
this is the one function that reads them. -/
def RealHolds (rd : ir.Valuation I) : RealCircuit → Prop
  | .logup t g => ir.LogupHoldsAt rd t g
  | .macH p => ir.MacHHolds rd p
  | .named _ => True
  | .unmodeled _ => True

/-! ## The meaning of a circuit -/

/-- **A predicate placed in a circuit holds** at `rd`: a `mod_q`'s field equation (`e = e'` in the
field, for `q = 0` or the field form; the other forms' equations are given no meaning yet), any
other predicate itself (`RealizedProgram.HoldsWith`). -/
def PlacedHolds (rd : ir.Valuation I) : PredBody → Prop
  | .mod d q e e' real =>
    if q = 0 ∨ real.form = .field then
      ∀ i < ir.exprLen e, ir.evalWith rd d e i = ir.evalWith rd d e' i
    else True
  | b => ir.HoldsWith rd b

/-- **A `mod_0` placed in a circuit holds** exactly when its field equation does. -/
theorem placedHolds_mod_zero_iff (rd : ir.Valuation I) (d : ℕ) (e e' : Expr)
    (real : ModRealization) : ir.PlacedHolds rd (.mod d 0 e e' real) ↔
      ∀ i < ir.exprLen e, ir.evalWith rd d e i = ir.evalWith rd d e' i := by
  simp [PlacedHolds]

/-- **An entry of a circuit's emission order holds** at `rd`: a Boolean check or a placed predicate
(`PlacedHolds`), a realization circuit (`RealHolds`); an alignment entry constrains filler inputs,
which no value reads. -/
def EntryHolds (rd : ir.Valuation I) : CircuitEntry → Prop
  | .typeCheck p => ir.PlacedHolds rd (ir.predicate p).body
  | .alignment _ => True
  | .pred p => ir.PlacedHolds rd (ir.predicate p).body
  | .realization rc => ir.RealHolds rd rc

variable (I)

/-- **The meaning of circuit `c`** at the valuation `rd`: every entry of its emission order holds
(`EntryHolds`). -/
def CircuitHolds (c : ℕ) (rd : ir.Valuation I) : Prop :=
  ∀ e ∈ (ir.circuit c).entries, ir.EntryHolds rd e

/-! ## The public input -/

/-- **A realization input's coordinate `j`** at the run `r`, in circuit `c`'s field: the weight
`1/(α − j)` of table `t`, `α` the run's challenge of `t` (`0` for an input named only by its C++
name or read only by an unmodeled circuit). -/
def realPubValue (c : ℕ) (r : (ir.layout I).Run) : RealPub → ℕ → (I (ir.circField c)).K
  | .weights t, j =>
    (castElt (ir.chalRead I r.chal (ir.table t).alpha 0) - (j : (I (ir.circField c)).K))⁻¹
  | .named _, _ => 0
  | .unmodeled _, _ => 0

/-- **The verifier's public input `j` of circuit `c`** at the statement `x` and the run `r`: `1` at
input `0`; in a public block, the block's value read by the semantics at the zero committed
assignment (a message is the run's message), or a realization input (`realPubValue`); `0`
elsewhere. -/
def publicInput (c : ℕ) (x : ir.Valuation I) (r : (ir.layout I).Run) (j : ℕ) :
    (I (ir.circField c)).K :=
  if j = 0 then 1
  else ((ir.circuit c).inputs.findSome?
    (·.pubValue? (fun u i => castElt (ir.reader (ir.layoutEnv I x ⟨0, 0⟩ r) u i))
      (ir.realPubValue I c r) j)).getD 0

/-! ## Decoding an input vector -/

/-- **The committed assignment decoded from the inputs `w` of circuit `c`**: committed coordinates
from their committed blocks, pads from their pad blocks, `0` elsewhere. -/
def inputAssignment (c : ℕ) (w : ℕ → (I (ir.circField c)).K) : ir.Assignment I where
  val u i := (((ir.circuit c).committedPos u i).map fun p => castElt (w p)).getD 0
  pad u i := (((ir.circuit c).padPos u i).map fun p => castElt (w p)).getD 0

/-- **The valuation decoded from an input vector `v` of circuit `c`** at the statement `x` and the
run `r` (see the module docstring): committed values, bit views and public values from their
blocks; every other coordinate, a late value included (the run's message minus its pad from the
pad block), from the semantics' reader at the realized assignment of the decoded committed
assignment. -/
def inputValuation (c : ℕ) (x : ir.Valuation I) (r : (ir.layout I).Run) {d : ℕ}
    (v : Fin (2 ^ d) → (I (ir.circField c)).K) : ir.Valuation I := fun u i =>
  let base := ir.reader (ir.layoutEnv I x (ir.bindAsg (ir.inputAssignment I c (vecRead v))) r)
  let fromBlock (o : Option ℕ) := ((o.map fun p => castElt (vecRead v p)).getD (base u i))
  match (ir.value u).kind with
  | .priv => fromBlock ((ir.circuit c).committedPos u i)
  | .padCopy _ _ => fromBlock ((ir.circuit c).committedPos u i)
  | .late => base u i
  | .bits _ _ => fromBlock ((ir.circuit c).viewPos u i)
  | _ => fromBlock ((ir.circuit c).pubPos u i)

/-- **The honest input vector of circuit `c`** at the statement `x`, the committed assignment `a`
and the run `r`: the public input (`publicInput`) at the public inputs; committed coordinates and
pads from `a`, bit views as the semantics reads them at the realized assignment; zero at filler,
batch pads and past the layout. -/
def circuitInput (c : ℕ) (x : ir.Valuation I) (r : (ir.layout I).Run) (a : ir.Assignment I)
    {d : ℕ} : Fin (2 ^ d) → (I (ir.circField c)).K := fun j =>
  if (ir.circuit c).IsPublicPos j then ir.publicInput I c x r j
  else ((ir.circuit c).inputs.findSome?
    (·.privValue? (fun u i => castElt (a.val u i)) (fun u i => castElt (a.pad u i))
      (fun u i => castElt (ir.reader (ir.layoutEnv I x (ir.bindAsg a) r) u i)) j)).getD 0

/-! ## The trust bundle -/

/-- **The width bound of circuit `c`**: `⌈log₂⌉` of the larger of its wires and its inputs, so
the compiled circuit's output layer and every layer's inputs have at most `2^width` wires. -/
def circuitWidth (c : ℕ) : ℕ := Nat.clog 2 (max (ir.circuit c).wires (ir.circuit c).inputCount)

/-- **The GKR source of circuit `c`**: the input dimension `d`, the source circuit `S` over the
circuit's field, its sumcheck nodes, and `hfit`: the circuit's inputs fit in `2^d`. -/
structure CircuitSource (c : ℕ) where
  /-- The input dimension. -/
  d : ℕ
  /-- The source circuit. -/
  S : GordieHowe.GKR.LayeredCircuit (I (ir.domainField (ir.circuit c).domain)).K d
  /-- The sumcheck nodes. -/
  nodes : Sumcheck.Nodes (I (ir.domainField (ir.circuit c).domain)).K
  /-- The circuit's inputs fit. -/
  hfit : (ir.circuit c).inputCount ≤ 2 ^ d

/-- **Trust base: the program's GKR circuits enforce their entries** (soundness direction of the
compiler correspondence, the paper's `sec:formal-assumptions`): for every circuit `c`, every
statement `x` and run `r`, every input vector `v` whose public inputs are the verifier's
(`publicInput`) and that satisfies the source circuit gives the meaning of every entry of `c`
(`CircuitHolds`) at the valuation decoded from `v` (`inputValuation`); and every source has the
circuit's shape (`circuitWidth`, the circuit's layers): its output and every layer's inputs have at
most `2^circuitWidth` wires. The vector is otherwise arbitrary: no Boolean or subfield restriction
on the private inputs, and no condition on the source circuit beyond its shape (any number of
assertions per gate, any output dimension within the width). -/
structure CircuitsEnforce (src : ∀ c : Fin ir.circuits.length, ir.CircuitSource I c) : Prop where
  /-- The circuits enforce their entries. -/
  enforce : ∀ (c : Fin ir.circuits.length) (x : ir.Valuation I) (r : (ir.layout I).Run)
    (v : Fin (2 ^ (src c).d) → (I (ir.circField c)).K),
    (∀ i : Fin (2 ^ (src c).d), (ir.circuit c).IsPublicPos i → v i = ir.publicInput I c x r i) →
    (src c).S.Satisfied v → ir.CircuitHolds I c (ir.inputValuation I c x r v)
  /-- The sources have the circuits' shapes. -/
  shape : ∀ c, (src c).S.ShapeAtMost (ir.circuitWidth c) (ir.circuit c).layers

/-- **Trust base, honest prover: the program's GKR circuits accept honest inputs** (completeness
direction of the compiler correspondence): wherever every entry of circuit `c` holds at the reader
of the layout's environment at the realized assignment (`bindAsg`), the source accepts the honest
input vector (`circuitInput`). -/
structure CircuitsAccept (src : ∀ c : Fin ir.circuits.length, ir.CircuitSource I c) : Prop where
  /-- The circuits accept honest inputs. -/
  accept : ∀ (c : Fin ir.circuits.length) (x : ir.Valuation I) (r : (ir.layout I).Run)
    (a : ir.Assignment I), ir.CircuitHolds I c (ir.reader (ir.layoutEnv I x (ir.bindAsg a) r)) →
    (src c).S.Satisfied (ir.circuitInput I c x r a)

/-! ## Public values do not read the committed assignment -/

/-- **Value `v` reads nothing of the committed assignment**, with `n` levels (as `RealizedProgram.read`): a
statement value, a constant, a challenge value, a message of a late value, an opaque value or a
public expression reading only such values. -/
def pubB : ℕ → ℕ → Bool
  | 0, _ => true
  | n + 1, v =>
    match (ir.value v).kind with
    | .pub .input => true
    | .pub (.opaque _ args) => args.all (pubB n)
    | .pub (.expr x) => (ir.exprNodes x).all (pubB n)
    | .constant _ => true
    | .challenge _ => true
    | .message u => decide (u < ir.values.length ∧ ir.IsLate u)
    | _ => false

/-- **Two committed assignments agree off the late values' coordinates**: their pads agree at every
coordinate that is not a coordinate of a late value. -/
def PadsAgreeOff (a a' : ir.Assignment I) : Prop :=
  ∀ u i, ¬ (u < ir.values.length ∧ ir.IsLate u ∧ i < (ir.value u).size) → a.pad u i = a'.pad u i

variable {ir I}

/-- **A value reading nothing of the committed assignment reads the same at two assignments**
whose pads agree off the late values' coordinates (a message is its run's message). -/
theorem read_eq_of_pubB {x : ir.Valuation I} {r : (ir.layout I).Run} {a a' : ir.Assignment I}
    (ha : ir.PadsAgreeOff I a a') :
    ∀ n v, ir.pubB n v = true →
      ir.read (ir.layoutEnv I x a r) n v = ir.read (ir.layoutEnv I x a' r) n v
  | 0, _, _ => rfl
  | n + 1, v, h => by
    funext i
    rcases hk : (ir.value v).kind with _ | ⟨_ | ⟨name, args⟩ | e⟩ | es | c | _ | ⟨w, sel⟩ | ⟨u, m⟩ |
      u <;> simp only [pubB, hk, Bool.false_eq_true] at h <;>
      simp only [read, hk, layoutEnv]
    case pub.opaque =>
      have hargs : args.map (fun u j => (I (ir.valueField u)).toNat
            (ir.read (ir.layoutEnv I x a r) n u j)) =
          args.map (fun u j => (I (ir.valueField u)).toNat (ir.read (ir.layoutEnv I x a' r) n u j)) :=
        List.map_congr_left fun u hu => by
          rw [read_eq_of_pubB ha n u (List.all_eq_true.1 h u hu)]
      simp only [layoutEnv] at hargs
      rw [hargs]
    case pub.expr =>
      exact congrFun (evalE_congr fun u hu => read_eq_of_pubB ha n u (List.all_eq_true.1 h u hu)) i
    case message =>
      rw [decide_eq_true_iff] at h
      by_cases hi : i < (ir.value u).size
      · rw [if_pos ⟨h.1, h.2, hi⟩, if_pos ⟨h.1, h.2, hi⟩, sub_add_cancel, sub_add_cancel]
      · rw [if_neg fun h' => hi h'.2.2, if_neg fun h' => hi h'.2.2,
          ha u i fun h' => hi h'.2.2]

/-- **The reader at a value reading nothing of the committed assignment** is the same at two
assignments whose pads agree off the late values' coordinates. -/
theorem reader_eq_of_pubB {x : ir.Valuation I} {r : (ir.layout I).Run} {a a' : ir.Assignment I}
    (ha : ir.PadsAgreeOff I a a') {v : ℕ} (h : ir.pubB ir.fuel v = true) :
    ir.reader (ir.layoutEnv I x a r) v = ir.reader (ir.layoutEnv I x a' r) v :=
  read_eq_of_pubB ha _ v h

end

end GordieHowe.RealizedProgram
