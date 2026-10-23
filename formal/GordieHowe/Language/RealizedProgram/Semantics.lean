-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram
public import GordieHowe.Language.RealizedProgram.Ops
public import GordieHowe.Language.Realizations.Lowering
public import GordieHowe.Language.Realizations.Range

@[expose] public section

/-!
# GordieHowe: the semantics of the plan's program

The meaning of a program (`GordieHowe.RealizedProgram`, `GordieHowe/Language/RealizedProgram.lean`):

* **Fields** (`FieldInterp`, `Interp`): every field identifier of the program is read as a Lean
  finite field with its specification (matched to the registry `GordieHowe.RealizedProgram.Export.fieldRegistry` by
  `Interp.Registered`, `GordieHowe/Language/RealizedProgram/WithPlan.lean`), the decoding of the C++ encoding of
  an element, the integer reading of an element, its packing-tree nodes as additive subgroups and
  the coordinates of an element in a node's basis (the bit views). An interpretation also reads
  the opaque functions (`Interp.opaqueFn`).
* **An environment** (`GordieHowe.RealizedProgram.Env`): what the values are read from: the statement, the
  committed assignment of phase `0` (the committed values and the pads of the late values), the
  challenges and the late values. The source protocol `Π_P` (`GordieHowe/Language/RealizedProgram/Protocol.lean`)
  reads the late values from the prover's messages; the realized program on the phase layout
  (`GordieHowe.RealizedProgram.layoutEnv`) reads late value `v` as its message minus its pad (`msg(v) − pad(v)`).
* **Reading values** (`GordieHowe.RealizedProgram.read`): a committed value, a pad copy or a value bound to its
  digits (committed in phase `0` in the source program; the realized program reads it through its
  digits, `GordieHowe.RealizedProgram.bindAsg`) from the committed assignment, a statement member from the statement, an opaque value by its function, a constant
  by decoding, a challenge from the environment, a late value from the environment, a message as
  `v + pad(v)`, a bit view as the coordinates of its words in their subfield's basis, and a public
  expression by evaluating it. Public expressions and bit views read other values; `read` takes a
  fuel bound (`GordieHowe.RealizedProgram.fuel`, enough when every value reads only values of smaller identifier,
  `GordieHowe.RealizedProgram.ValueOk`).
* **Expressions** (`Expr.eval`, `Expr.evalInt`): coordinatewise arithmetic, views, sparse rows,
  products, multiplexers, the named operators (`NamedOp.block`, the meanings of
  `GordieHowe/Language/RealizedProgram/Ops.lean`, applied along the last axis by `NamedOp.apply`), the Logic
  builders (`LogicOp.eval`), and the shared expressions `ref k`, read from a table
  (`GordieHowe.RealizedProgram.refVal`, by fuel: entry `k` reads only entries of smaller index).
* **The predicates** (`GordieHowe.RealizedProgram.HoldsWith` at a reader of the values): a field `equal` coordinatewise
  in its domain's field; an `in` at every record; a `mod_q` on the integers (`Expr.evalInt`: values
  read as integers in `[0, p)`, constants and constant coefficients in `(−p/2, p/2)`, a named
  operator by its matrix entries read in `(−p/2, p/2)`, as the C++ `signed_rep` reads them,
  compiler/range.h); a cross-field `equal` in the compiler's contract (the `y` operand's readings
  below `2^width`, and the operands' readings equal where every reading of `x` is below `2^width`;
  `GordieHowe.RealizedProgram.HoldsWith`).
* **`GordieHowe.RealizedProgram.SatAt`**: every predicate holds and every value whose type its packing-tree node
  enforces lies in its type. **`GordieHowe.RealizedProgram.Pred`** is `SatAt` at the layout's environment, as a
  constraint of the phase layout (`GordieHowe.RealizedProgram.layout`): phase `k + 1` of the program is index `k`; its
  challenge is the product of the program's challenges of that phase, each a vector of its size
  drawn by its sampler; the late values are the late value nodes in identifier order, each masked
  over its pad space.
-/

namespace GordieHowe.RealizedProgram

open Export ProofSystem.PhaseLayout

/-! ## Fields -/

/-- **A field of the program, read in Lean**: its registry specification, a finite field `K`, the
decoding of the C++ encoding of an element (`decode`), the integer reading of an element
(`toNat`: the natural below the characteristic of a prime-subfield element; the polynomial-basis
coefficients of a binary-field element as a natural, bit `j` the coefficient of `x^j`), the
additive subgroup of each packing-tree node by name (`node`), with decidable membership, and the
coordinates of an element in a node's basis (`coord E x j`: the coefficient of the basis element
`β_j` of node `E`, `Domain::bits`; for the designated subfield `β_j = g^j`). -/
structure FieldInterp where
  /-- The registry specification. -/
  spec : FieldSpec
  /-- The field. -/
  K : Type
  [field : Field K]
  [fintype : Fintype K]
  [decEq : DecidableEq K]
  /-- The decoding of the C++ encoding. -/
  decode : ℕ → K
  /-- The integer reading. -/
  toNat : K → ℕ
  /-- The packing-tree node by name. -/
  node : String → AddSubgroup K
  /-- Membership in a node is decidable. -/
  memDec : ∀ s, DecidablePred (· ∈ node s)
  /-- The coordinates of an element in a node's basis. -/
  coord : String → K → ℕ → Bool

attribute [instance] FieldInterp.field FieldInterp.fintype FieldInterp.decEq FieldInterp.memDec

namespace FieldInterp

variable (F : FieldInterp)

/-- **The additive subgroup of a space**: `⊤` for the whole field, the node's subgroup otherwise. -/
def space : Space → AddSubgroup F.K
  | .full => ⊤
  | .node s => F.node s

instance (s : Space) : DecidablePred (· ∈ F.space s) := fun x =>
  match s with
  | .full => isTrue (AddSubgroup.mem_top x)
  | .node s => F.memDec s x

/-- **Membership in a value type**: `0` or `1` for `Bit`, the node's subgroup for `Sub(E)`, any
element for `Field`. -/
def InType : VType → F.K → Prop
  | .bit, x => x = 0 ∨ x = 1
  | .sub E, x => x ∈ F.node E
  | .field, _ => True

instance (t : VType) (x : F.K) : Decidable (F.InType t x) := by
  cases t <;> unfold InType <;> infer_instance

/-- **The values a sampler draws from**: the field, a node, or the field minus the integers
`[0, tmax)` (`Range.LookupChallenge`, LogUp's `α`). The packed rows of public tables
(`Excluded.packedRows`) and unions (`Excluded.union`) are given no meaning here: their `U` depends on an earlier challenge `γ`
under the `gamma` packing, which a layout's fixed challenge types cannot express, and
`RealizedProgram.ValidAtNodes` rejects them (`RealizedProgram.SamplerOk`). -/
def SamplerTy : Sampler → Type
  | .full => F.K
  | .node E => F.node E
  | .fieldMinusTables (.range T) => Range.LookupChallenge F.K T
  | .fieldMinusTables (.packedRows _) => F.K
  | .fieldMinusTables (.union _ _) => F.K

/-- **A drawn value as a field element.** -/
def samplerVal : (s : Sampler) → F.SamplerTy s → F.K
  | .full, x => x
  | .node _, x => x.val
  | .fieldMinusTables (.range _), x => x.val
  | .fieldMinusTables (.packedRows _), x => x
  | .fieldMinusTables (.union _ _), x => x

/-- The sampler's values are finite. -/
instance samplerFintype : (s : Sampler) → Fintype (F.SamplerTy s)
  | .full => inferInstanceAs (Fintype F.K)
  | .node E => inferInstanceAs (Fintype (F.node E))
  | .fieldMinusTables (.range T) => inferInstanceAs (Fintype (Range.LookupChallenge F.K T))
  | .fieldMinusTables (.packedRows _) => inferInstanceAs (Fintype F.K)
  | .fieldMinusTables (.union _ _) => inferInstanceAs (Fintype F.K)

/-- The sampler's values have decidable equality. -/
instance samplerDecEq : (s : Sampler) → DecidableEq (F.SamplerTy s)
  | .full => inferInstanceAs (DecidableEq F.K)
  | .node E => inferInstanceAs (DecidableEq (F.node E))
  | .fieldMinusTables (.range T) => inferInstanceAs (DecidableEq (Range.LookupChallenge F.K T))
  | .fieldMinusTables (.packedRows _) => inferInstanceAs (DecidableEq F.K)
  | .fieldMinusTables (.union _ _) => inferInstanceAs (DecidableEq F.K)

/-- The sampler draws from a nonempty set. -/
instance samplerInhabited : (s : Sampler) → Inhabited (F.SamplerTy s)
  | .full => ⟨(0 : F.K)⟩
  | .node E => ⟨(0 : F.node E)⟩
  | .fieldMinusTables (.range T) => inferInstanceAs (Inhabited (Range.LookupChallenge F.K T))
  | .fieldMinusTables (.packedRows _) => ⟨(0 : F.K)⟩
  | .fieldMinusTables (.union _ _) => ⟨(0 : F.K)⟩

/-- **A constant as an integer**: the natural `c` of the C++ encoding read in `(−p/2, p/2)` for the
characteristic `p`. -/
def centered (c : ℕ) : ℤ :=
  if 2 * c < F.spec.characteristic then c else (c : ℤ) - F.spec.characteristic

/-- **An element as a coefficient of an integer expression**: its integer reading, centred
(`centered`). -/
def coefInt (x : F.K) : ℤ := F.centered (F.toNat x)

/-- A bit as a field element: `1` or `0`. -/
def ofBool (b : Bool) : F.K := if b then 1 else 0

end FieldInterp

/-- **An interpretation of the program**: field identifier `f` is the Lean field `field f` (total;
identifiers outside the program are never read), and the opaque function `name` maps the integer
readings of its arguments' coordinates (`FieldInterp.toNat`) to the naturals of the C++ encoding
of its value's coordinates (`opaqueFn name args i`). -/
structure Interp : Type 1 where
  /-- The fields. -/
  field : ℕ → FieldInterp
  /-- The opaque functions. -/
  opaqueFn : String → List (ℕ → ℕ) → ℕ → ℕ

instance : CoeFun Interp fun _ => ℕ → FieldInterp := ⟨Interp.field⟩

/-- **An element read in another field identifier**: itself when the identifiers agree, `0`
otherwise (a program whose expressions stay in one field, `RealizedProgram.ExprOk`, casts only where
identifiers agree). -/
def castElt {I : Interp} {a b : ℕ} (x : (I a).K) : (I b).K :=
  if h : a = b then h ▸ x else 0

@[simp] theorem castElt_self {I : Interp} {a : ℕ} (x : (I a).K) : castElt (b := a) x = x :=
  by simp [castElt]

@[simp] theorem castElt_zero {I : Interp} {a b : ℕ} : (castElt (0 : (I a).K) : (I b).K) = 0 := by
  unfold castElt
  split
  · rename_i h
    subst h
    rfl
  · rfl

theorem castElt_castElt_of_eq {I : Interp} {a b : ℕ} (h : a = b) (x : (I a).K) :
    (castElt (castElt x : (I b).K) : (I a).K) = x := by
  subst h
  simp

/-! ## Named operators and Logic builders -/

namespace NamedOp

variable (ir : RealizedProgram)

/-- **The block width of a named operator**: the coordinates of one block of its operand
(`n` for the transforms and convolutions, `L·n` for `polyMatVec`, `nch·w` for `macConv`, `w` for
`sum`, `k` for `fromDigits`, `1` for `scale`). -/
def cols : NamedOp → ℕ
  | .negacyclicConv h _ => (ir.value h).size
  | .polyMatVec a K L _ => L * ((ir.value a).size / (K * L))
  | .polyBroadcast t K _ => (ir.value t).size / K
  | .ntt n _ _ => n
  | .inverseNtt n _ => n
  | .nttTranspose n _ => n
  | .rowDot _ _ W => W
  | .macConv _ w nch _ => nch * w
  | .acyclicConv _ lx => lx
  | .diagonal d => (ir.value d).size
  | .scale _ => 1
  | .constDiagonal d => (ir.value d).size
  | .sum w => w
  | .fromDigits k _ => k
  | .batched b op => b * cols op

/-- **The output width of a named operator** on one block. -/
def rows : NamedOp → ℕ
  | .negacyclicConv h _ => (ir.value h).size
  | .polyMatVec a K L _ => K * ((ir.value a).size / (K * L))
  | .polyBroadcast t _ _ => (ir.value t).size
  | .ntt n _ _ => n
  | .inverseNtt n _ => n
  | .nttTranspose n _ => n
  | .rowDot _ R _ => R
  | .macConv _ w _ _ => w
  | .acyclicConv h lx => lx + (ir.value h).size - 1
  | .diagonal d => (ir.value d).size
  | .scale _ => 1
  | .constDiagonal d => (ir.value d).size
  | .sum _ => 1
  | .fromDigits _ _ => 1
  | .batched b op => b * rows op

variable {I : Interp}

/-- **A polynomial operand in its form**: its coefficients, or the inverse transform of its
scheme-order spectrum at `ψ`. -/
def formPoly (f n : ℕ) (h : ℕ → (I f).K) : ConvForm → ℕ → (I f).K
  | .coefficients => h
  | .ntt psi => Ops.inverseNtt n ((I f).decode psi) h

/-- **A named operator on one block**, in field `f`, its public operands read by `leaf` (read in
field `f`; `macConv` reads the bits of its powers `r_c` in their own field, the MAC field's
polynomial basis): the meanings of `GordieHowe/Language/RealizedProgram/Ops.lean`. -/
def block (f : ℕ) (leaf : ∀ v : ℕ, ℕ → (I (ir.valueField v)).K) :
    NamedOp → (ℕ → (I f).K) → ℕ → (I f).K
  | .negacyclicConv h form, x =>
    Ops.negacyclic (ir.value h).size
      (formPoly f (ir.value h).size (fun s => castElt (leaf h s)) form) x
  | .polyMatVec a K L form, x => fun j =>
    let n := (ir.value a).size / (K * L)
    if j < K * n then
      ∑ l : Fin L, Ops.negacyclic n
        (formPoly f n (fun s => castElt (leaf a ((j / n * L + l) * n + s))) form)
        (fun s => x (l * n + s)) (j % n)
    else 0
  | .polyBroadcast t K form, x => fun j =>
    let n := (ir.value t).size / K
    if j < K * n then
      Ops.negacyclic n (formPoly f n (fun s => castElt (leaf t (j / n * n + s))) form) x (j % n)
    else 0
  | .ntt n psi .scheme, x => Ops.nttScheme n ((I f).decode psi) x
  | .ntt n psi .natural, x => Ops.nttNatural n ((I f).decode psi) x
  | .inverseNtt n psi, x => Ops.inverseNtt n ((I f).decode psi) x
  | .nttTranspose n psi, x => Ops.nttTranspose n ((I f).decode psi) x
  | .rowDot M R W, x => Ops.rowDot R W (fun s => castElt (leaf M s)) x
  | .macConv r w nch taps, x =>
    Ops.macConv w nch taps
      (fun c j => if ((I (ir.valueField r)).toNat (leaf r c)).testBit j then 1 else 0) x
  | .acyclicConv h lx, x => Ops.acyclic (ir.value h).size lx (fun s => castElt (leaf h s)) x
  | .diagonal d, x => Ops.diagonal (ir.value d).size (fun s => castElt (leaf d s)) x
  | .scale c, x => fun j => if j = 0 then castElt (leaf c 0) * x 0 else 0
  | .constDiagonal d, x => Ops.diagonal (ir.value d).size (fun s => castElt (leaf d s)) x
  | .sum w, x => Ops.sum w x
  | .fromDigits k base, x => Ops.fromDigits k ((I f).decode base) x
  | .batched b op, x => fun j =>
    if j < b * rows ir op then
      block f leaf op (fun t => x (j / rows ir op * cols ir op + t)) (j % rows ir op)
    else 0

/-- **A named operator along the last axis**: output coordinate `j` is coordinate `j mod rows` of
the operator on block `j / rows` of the operand (`cols` coordinates). -/
def apply (f : ℕ) (leaf : ∀ v : ℕ, ℕ → (I (ir.valueField v)).K) (op : NamedOp)
    (x : ℕ → (I f).K) (j : ℕ) : (I f).K :=
  block ir f leaf op (fun t => x (j / rows ir op * cols ir op + t)) (j % rows ir op)

/-- **A named operator along the last axis, on the integers** (`mod_q`): output coordinate `j` is
`Σ_t ⌊M_{j t}⌉ x_t` over block `j / rows` of the operand, `M_{j t}` the operator's matrix entry in
field `f` (its value on the unit vector `t`) read in `(−p/2, p/2)` (`FieldInterp.coefInt`). -/
def applyInt (f : ℕ) (leaf : ∀ v : ℕ, ℕ → (I (ir.valueField v)).K) (op : NamedOp)
    (x : ℕ → ℤ) (j : ℕ) : ℤ :=
  ∑ t : Fin (cols ir op),
    (I f).coefInt (block ir f leaf op (fun s => if s = t then 1 else 0) (j % rows ir op)) *
      x (j / rows ir op * cols ir op + t)

end NamedOp

/-- **A Logic builder** on words of `w` bits along the last axis, over a commutative ring, its
arguments `args` (`Ops.ltWord`, `Ops.leqWord`, `Ops.eqWord`, the balanced AND and OR trees):
output coordinate `j` reads bits `j w, …, j w + w − 1` of each argument. -/
def LogicOp.eval {R : Type*} [CommRing R] (w : ℕ) (args : List (ℕ → R)) (j : ℕ) : LogicOp → R
  | .lt => Ops.ltWord w (fun t => args.headD 0 (j * w + t)) (fun t => args.getD 1 0 (j * w + t))
  | .leq => Ops.leqWord w (fun t => args.headD 0 (j * w + t)) (fun t => args.getD 1 0 (j * w + t))
  | .eq => Ops.eqWord w (fun t => args.headD 0 (j * w + t)) (fun t => args.getD 1 0 (j * w + t))
  | .any => Ops.orTree (fun t => args.headD 0 (j * w + t)) w 0
  | .all => Ops.andTree (fun t => args.headD 0 (j * w + t)) w 0

/-! ## Expressions -/

variable (ir : RealizedProgram)

mutual

/-- **The length of an expression** (its number of coordinates), the shared expressions having
lengths `rl`. -/
def Expr.len (rl : ℕ → ℕ) : Expr → ℕ
  | .leaf v => (ir.value v).size
  | .add e _ => Expr.len rl e
  | .sub e _ => Expr.len rl e
  | .scale _ e => Expr.len rl e
  | .mul e _ => Expr.len rl e
  | .reindex idx _ => idx.size
  | .concat e e' => Expr.len rl e + Expr.len rl e'
  | .linear rows _ => rows.length
  | .prod n e => Expr.len rl e / n
  | .mux _ t _ => Expr.len rl t
  | .apply op e => Expr.len rl e / NamedOp.cols ir op * NamedOp.rows ir op
  | .ref k => rl k
  | .logic _ w args => (Expr.lenList rl args).headD 0 / w

/-- The lengths of a list of expressions. -/
def Expr.lenList (rl : ℕ → ℕ) : List Expr → List ℕ
  | [] => []
  | e :: es => Expr.len rl e :: Expr.lenList rl es

end

variable {I : Interp}

/-- **A coefficient's value** in field `f`, reading values by `leaf`. -/
def Coef.eval (f : ℕ) (leaf : ∀ v : ℕ, ℕ → (I (ir.valueField v)).K) : Coef → (I f).K
  | .const c => (I f).decode c
  | .node v i => castElt (leaf v i)

mutual

/-- **An expression's coordinate `i`** in field `f`, reading values by `leaf`, the shared
expressions by `ref` and their lengths by `rl`. -/
def Expr.eval (f : ℕ) (leaf : ∀ v : ℕ, ℕ → (I (ir.valueField v)).K) (ref : ℕ → ℕ → (I f).K)
    (rl : ℕ → ℕ) : Expr → ℕ → (I f).K
  | .leaf v, i => castElt (leaf v i)
  | .add e e', i => Expr.eval f leaf ref rl e i + Expr.eval f leaf ref rl e' i
  | .sub e e', i => Expr.eval f leaf ref rl e i - Expr.eval f leaf ref rl e' i
  | .scale c e, i => Coef.eval ir f leaf c * Expr.eval f leaf ref rl e i
  | .mul e e', i => Expr.eval f leaf ref rl e i * Expr.eval f leaf ref rl e' i
  | .reindex idx e, i => Expr.eval f leaf ref rl e (idx.entry i)
  | .concat e e', i =>
      if i < Expr.len ir rl e then Expr.eval f leaf ref rl e i
      else Expr.eval f leaf ref rl e' (i - Expr.len ir rl e)
  | .linear rows e, i =>
      ((rows.getD i []).map fun t => Coef.eval ir f leaf t.2 * Expr.eval f leaf ref rl e t.1).sum
  | .prod n e, i => ((List.range n).map fun t => Expr.eval f leaf ref rl e (i * n + t)).prod
  | .mux b t e, i =>
      Expr.eval f leaf ref rl b i * Expr.eval f leaf ref rl t i +
        (1 - Expr.eval f leaf ref rl b i) * Expr.eval f leaf ref rl e i
  | .apply op e, i => NamedOp.apply ir f leaf op (Expr.eval f leaf ref rl e) i
  | .ref k, i => ref k i
  | .logic op w args, i => op.eval w (Expr.evalList f leaf ref rl args) i

/-- The values of a list of expressions. -/
def Expr.evalList (f : ℕ) (leaf : ∀ v : ℕ, ℕ → (I (ir.valueField v)).K) (ref : ℕ → ℕ → (I f).K)
    (rl : ℕ → ℕ) : List Expr → List (ℕ → (I f).K)
  | [] => []
  | e :: es => Expr.eval f leaf ref rl e :: Expr.evalList f leaf ref rl es

end

/-- **A coefficient's integer value** in field `f`: a constant in `(−p/2, p/2)`, a value by
`ileaf`. -/
def Coef.evalInt (f : ℕ) (ileaf : ℕ → ℕ → ℤ) : Coef → ℤ
  | .const c => (I f).centered c
  | .node v i => ileaf v i

mutual

/-- **An expression's coordinate `i` on the integers** (`mod_q`), in field `f`: the operations
over `ℤ`, the values read by `ileaf`, the constants by `FieldInterp.centered`, a named operator by
its matrix entries (`NamedOp.applyInt`, public operands read by `leaf`), the shared expressions
by `iref`. -/
def Expr.evalInt (f : ℕ) (leaf : ∀ v : ℕ, ℕ → (I (ir.valueField v)).K) (ileaf : ℕ → ℕ → ℤ)
    (iref : ℕ → ℕ → ℤ) (rl : ℕ → ℕ) : Expr → ℕ → ℤ
  | .leaf v, i => ileaf v i
  | .add e e', i => Expr.evalInt f leaf ileaf iref rl e i + Expr.evalInt f leaf ileaf iref rl e' i
  | .sub e e', i => Expr.evalInt f leaf ileaf iref rl e i - Expr.evalInt f leaf ileaf iref rl e' i
  | .scale c e, i => Coef.evalInt (I := I) f ileaf c * Expr.evalInt f leaf ileaf iref rl e i
  | .mul e e', i => Expr.evalInt f leaf ileaf iref rl e i * Expr.evalInt f leaf ileaf iref rl e' i
  | .reindex idx e, i => Expr.evalInt f leaf ileaf iref rl e (idx.entry i)
  | .concat e e', i =>
      if i < Expr.len ir rl e then Expr.evalInt f leaf ileaf iref rl e i
      else Expr.evalInt f leaf ileaf iref rl e' (i - Expr.len ir rl e)
  | .linear rows e, i =>
      ((rows.getD i []).map fun t =>
        Coef.evalInt (I := I) f ileaf t.2 * Expr.evalInt f leaf ileaf iref rl e t.1).sum
  | .prod n e, i => ((List.range n).map fun t => Expr.evalInt f leaf ileaf iref rl e (i * n + t)).prod
  | .mux b t e, i =>
      Expr.evalInt f leaf ileaf iref rl b i * Expr.evalInt f leaf ileaf iref rl t i +
        (1 - Expr.evalInt f leaf ileaf iref rl b i) * Expr.evalInt f leaf ileaf iref rl e i
  | .apply op e, i => NamedOp.applyInt ir f leaf op (Expr.evalInt f leaf ileaf iref rl e) i
  | .ref k, i => iref k i
  | .logic op w args, i => op.eval w (Expr.evalIntList f leaf ileaf iref rl args) i

/-- The integer values of a list of expressions. -/
def Expr.evalIntList (f : ℕ) (leaf : ∀ v : ℕ, ℕ → (I (ir.valueField v)).K) (ileaf : ℕ → ℕ → ℤ)
    (iref : ℕ → ℕ → ℤ) (rl : ℕ → ℕ) : List Expr → List (ℕ → ℤ)
  | [] => []
  | e :: es => Expr.evalInt f leaf ileaf iref rl e :: Expr.evalIntList f leaf ileaf iref rl es

end

section

variable (I : Interp)

/-! ## The layout -/

/-- **The challenges of index `k`** (phase `k + 1`). -/
def ChalAt (k : Fin ir.phases) : Type :=
  {j : Fin ir.challenges.length // (ir.challenge j).phase = k + 1}

instance (k : Fin ir.phases) : Fintype (ir.ChalAt k) := Subtype.fintype _

instance (k : Fin ir.phases) : DecidableEq (ir.ChalAt k) := Subtype.instDecidableEq

/-- **The value of challenge `j`**: a vector of its size, each coordinate drawn by its sampler. -/
abbrev ChalVal (j : ℕ) : Type :=
  Fin (ir.challenge j).size → (I (ir.chalField j)).SamplerTy (ir.challenge j).sampler

/-- **A late value node** of a phase the program has. -/
def IsLate (v : ℕ) : Prop :=
  (ir.value v).kind.isLate = true ∧ 1 ≤ (ir.value v).phase ∧ (ir.value v).phase ≤ ir.phases

instance (v : ℕ) : Decidable (ir.IsLate v) := inferInstanceAs (Decidable (_ ∧ _))

/-- **The late values**: the late value nodes, in identifier order. -/
def Late : Type := {v : Fin ir.values.length // ir.IsLate v}

instance : Fintype ir.Late := Subtype.fintype _

instance : LinearOrder ir.Late := Subtype.instLinearOrder _

instance : DecidableEq ir.Late := Subtype.instDecidableEq

/-- **The masking space of late value `v`**: its pad space, coordinatewise. -/
abbrev Mask (v : ℕ) : Type :=
  Fin (ir.value v).size → (I (ir.valueField v)).space (ir.value v).padSpace

/-- **The layout of the program**: index `k` is phase `k + 1`; its challenge is the product of
the phase's challenges; the late values are the late value nodes with their pad spaces. -/
abbrev layout : ProofSystem.PhaseLayout ir.phases where
  Ch k := ∀ j : ir.ChalAt k, ir.ChalVal I j.1
  chNonempty _ := ⟨fun _ _ => default⟩
  Late := ir.Late
  phase l := ⟨(ir.value l.1).phase - 1, by have := l.2; unfold IsLate at this; omega⟩
  Mask l := ir.Mask I l.1

/-- **Coordinate `i` of challenge `j`** at the challenges `c`; `0` for a challenge of a phase the
program does not have or a coordinate past its size. -/
def chalRead (c : ∀ k, (ir.layout I).Ch k) (j i : ℕ) : (I (ir.chalField j)).K :=
  if h : j < ir.challenges.length ∧ 1 ≤ (ir.challenge j).phase ∧
      (ir.challenge j).phase ≤ ir.phases ∧ i < (ir.challenge j).size then
    (show ir.ChalVal I j from
      c ⟨(ir.challenge j).phase - 1, by omega⟩ ⟨⟨j, h.1⟩, by simp only; omega⟩) ⟨i, h.2.2.2⟩
      |> (I (ir.chalField j)).samplerVal _
  else 0

/-- **The message of late value `v`** at coordinate `i` in the run `r`; `0` when `v` is not a late
value of the layout or `i` is out of range. -/
def msgRead (r : (ir.layout I).Run) (v i : ℕ) : (I (ir.valueField v)).K :=
  if h : v < ir.values.length ∧ ir.IsLate v ∧ i < (ir.value v).size then
    (show ir.Mask I v from r.msg ⟨⟨v, h.1⟩, h.2.1⟩) ⟨i, h.2.2⟩
  else 0

/-! ## Assignments and environments -/

/-- **A valuation**: every coordinate of every value, in the value's field. The statement is a
valuation read at the statement members and the opaque values without arguments. -/
abbrev Valuation : Type := ∀ v : ℕ, ℕ → (I (ir.valueField v)).K

/-- **A committed assignment**: the committed values of phase `0` (`val`, read at the committed
values and the pad copies) and the pads (`pad`, read at the late values). -/
structure Assignment where
  /-- The committed values. -/
  val : ir.Valuation I
  /-- The pads. -/
  pad : ir.Valuation I

/-- **An environment**: the statement, the committed assignment, coordinate `i` of challenge `j`
(`chal j i`), and the late values. -/
structure Env where
  /-- The statement. -/
  stmt : ir.Valuation I
  /-- The committed assignment. -/
  asg : ir.Assignment I
  /-- The challenges. -/
  chal : ∀ j : ℕ, ℕ → (I (ir.chalField j)).K
  /-- The late values. -/
  late : ir.Valuation I

/-- **The environment of the realized program on the layout** at the statement `x`, the committed
assignment `a` and the run `r`: the challenges of the run, and late value `v` read as its message
minus its pad (`0` past the late values' coordinates). -/
def layoutEnv (x : ir.Valuation I) (a : ir.Assignment I) (r : (ir.layout I).Run) : ir.Env I where
  stmt := x
  asg := a
  chal := ir.chalRead I r.chal
  late v i :=
    if v < ir.values.length ∧ ir.IsLate v ∧ i < (ir.value v).size then
      ir.msgRead I r v i - a.pad v i
    else 0

/-! ## Shared expressions -/

/-- **The lengths of the shared expressions**, with `n` levels (`0`: every length `0`). -/
def refLen : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, k => Expr.len ir (refLen n) (ir.expr k)

/-- **The length of an expression**, its shared expressions' lengths at the program's depth (the
number of shared expressions, enough when each reads only entries of smaller index). -/
def exprLen (e : Expr) : ℕ := Expr.len ir (ir.refLen ir.exprs.length) e

variable {I}

/-- **Coordinate `i` of shared expression `k`** in field `f`, reading values by `leaf`, with `n`
levels. -/
def refVal (leaf : ir.Valuation I) : ℕ → (f : ℕ) → ℕ → ℕ → (I f).K
  | 0, _, _, _ => 0
  | n + 1, f, k, i => Expr.eval ir f leaf (refVal leaf n f) (ir.refLen ir.exprs.length) (ir.expr k) i

/-- **An expression's coordinate `i`** in field `f`, reading values by `leaf`, the shared
expressions at the program's depth. -/
def evalE (leaf : ir.Valuation I) (f : ℕ) (e : Expr) (i : ℕ) : (I f).K :=
  Expr.eval ir f leaf (ir.refVal leaf ir.exprs.length f) (ir.refLen ir.exprs.length) e i

/-! ## Reading values -/

/-- **The fuel of the program**: one more than its number of values. -/
def fuel : ℕ := ir.values.length + 1

/-- **Coordinate `i` of a bit view** of the words `sel` of value `w`, `e` bits per word, the words
read by `rd`: bit `i mod e` of word `sel[i / e]` in the basis of `w`'s subfield. -/
def bitView (rd : ir.Valuation I) (v w : ℕ) (sel : IndexMap) (i : ℕ) : (I (ir.valueField v)).K :=
  let e := (ir.value v).size / sel.size
  (I (ir.valueField v)).ofBool
    ((I (ir.valueField w)).coord ((ir.value w).type.nodeName.getD "")
      (rd w (sel.entry (i / e))) (i % e))

/-- **Coordinate `i` of value `v`** in the environment `e`, with `n` levels of values read by
values (`0`: nothing is read). -/
def read (e : ir.Env I) : ℕ → ∀ v : ℕ, ℕ → (I (ir.valueField v)).K
  | 0, _, _ => 0
  | n + 1, v, i =>
    match (ir.value v).kind with
    | .priv => e.asg.val v i
    | .pub .input => e.stmt v i
    | .pub (.opaque name args) =>
      if args = [] then e.stmt v i
      else (I (ir.valueField v)).decode (I.opaqueFn name
        (args.map fun u j => (I (ir.valueField u)).toNat (read e n u j)) i)
    | .pub (.expr x) => ir.evalE (read e n) (ir.valueField v) x i
    | .constant es => (I (ir.valueField v)).decode (es.getD i 0)
    | .challenge c => castElt (e.chal c i)
    | .late => e.late v i
    | .bits w sel => ir.bitView (read e n) v w sel i
    | .padCopy _ _ => e.asg.val v i
    | .message u => castElt (e.late u i + e.asg.pad u i)
    | .bound _ => e.asg.val v i

/-- **The reader of the environment** `e`: every value read at the program's fuel. -/
def reader (e : ir.Env I) : ir.Valuation I := ir.read e ir.fuel

section ReaderAt

variable {ir}

/-- **A committed value reads the committed assignment.** -/
theorem reader_of_priv (e : ir.Env I) {v : ℕ} (hk : (ir.value v).kind = .priv) :
    ir.reader e v = e.asg.val v := by
  funext i
  simp [reader, fuel, read, hk]

/-- **A pad copy reads the committed assignment.** -/
theorem reader_of_padCopy (e : ir.Env I) {v u : ℕ} {m : String}
    (hk : (ir.value v).kind = .padCopy u m) : ir.reader e v = e.asg.val v := by
  funext i
  simp [reader, fuel, read, hk]

/-- **A late value reads the environment's late values.** -/
theorem reader_of_late (e : ir.Env I) {v : ℕ} (hk : (ir.value v).kind = .late) :
    ir.reader e v = e.late v := by
  funext i
  simp [reader, fuel, read, hk]

/-- **A constant reads its entries.** -/
theorem reader_of_constant (e : ir.Env I) {v : ℕ} {es : List ℕ}
    (hk : (ir.value v).kind = .constant es) (i : ℕ) :
    ir.reader e v i = (I (ir.valueField v)).decode (es.getD i 0) := by
  simp only [reader, fuel, read, hk]

end ReaderAt

/-! ## Values bound to their digits -/

/-- **The committed reader of the committed assignment `a`**: a constant by decoding, every other
value from the committed values. The expression of a value bound to its digits reads committed
values and constants only (`RealizedProgram.BoundOk`). -/
def committedRead (a : ir.Assignment I) : ir.Valuation I := fun u j =>
  match (ir.value u).kind with
  | .constant es => (I (ir.valueField u)).decode (es.getD j 0)
  | _ => a.val u j

/-- **The realized assignment of the committed assignment `a`**: every value bound to its digits
read as its expression `e` at the committed reader (`committedRead`), every other coordinate as in
`a`. The realized program is read at it (`RealizedProgram.Realized`); a bound value has no cell, and the
source program reads its coordinates from it. -/
def bindAsg (a : ir.Assignment I) : ir.Assignment I where
  val v i :=
    match (ir.value v).kind with
    | .bound e => ir.evalE (ir.committedRead a) (ir.valueField v) e i
    | _ => a.val v i
  pad := a.pad

/-- **The realized assignment keeps every value not bound to its digits.** -/
theorem bindAsg_val_of_isBound (a : ir.Assignment I) {v : ℕ}
    (h : (ir.value v).kind.isBound = false) : (ir.bindAsg a).val v = a.val v := by
  funext i
  simp only [bindAsg]
  split
  · rename_i e he
    rw [he] at h
    cases h
  · rfl

/-- **An expression's coordinate `i`** in domain `d`'s field, reading values by `rd`. -/
def evalWith (rd : ir.Valuation I) (d : ℕ) (e : Expr) (i : ℕ) : (I (ir.domainField d)).K :=
  ir.evalE rd (ir.domainField d) e i

/-- **The integer reading of value `v`** for `mod_q`, reading values by `rd`: a constant's entry in
`(−p/2, p/2)`; a value bound to an expression (`Kind.bound`, a value the C++ and the paper inline,
such as `z = d_0 + 645 d_1 − offset`) its integer reading in `(−p/2, p/2)`, so it reads signed:
where it reads its expression, it is the expression's integer value whenever that lies in
`(−p/2, p/2)`; any other value's
integer reading (`FieldInterp.toNat`). -/
def intOf (rd : ir.Valuation I) (v i : ℕ) : ℤ :=
  match (ir.value v).kind with
  | .constant es => (I (ir.valueField v)).centered (es.getD i 0)
  | .bound _ => (I (ir.valueField v)).centered ((I (ir.valueField v)).toNat (rd v i))
  | _ => ((I (ir.valueField v)).toNat (rd v i) : ℤ)

/-- **Coordinate `i` of shared expression `k` on the integers** in field `f`, reading values by
`rd`, with `n` levels. -/
def refInt (rd : ir.Valuation I) (f : ℕ) : ℕ → ℕ → ℕ → ℤ
  | 0, _, _ => 0
  | n + 1, k, i =>
    Expr.evalInt ir f rd (ir.intOf rd) (refInt rd f n) (ir.refLen ir.exprs.length) (ir.expr k) i

/-- **An expression's coordinate `i` on the integers** in domain `d`, reading values by `rd`. -/
def evalIntWith (rd : ir.Valuation I) (d : ℕ) (e : Expr) (i : ℕ) : ℤ :=
  Expr.evalInt ir (ir.domainField d) rd (ir.intOf rd)
    (ir.refInt rd (ir.domainField d) ir.exprs.length) (ir.refLen ir.exprs.length) e i

/-! ## Predicates -/

/-- **A record is a row of a table**, reading values by `rd`: below `n` for the range `[0, n)`
(every field); the columns' coordinates at one row for a table of columns; a coordinate of `e'`
for the coordinates of an expression `e'` (every record field). -/
def InRows (rd : ir.Valuation I) (d : ℕ) (records : List Expr) (i : ℕ) : TableRows → Prop
  | .range n => ∀ e ∈ records, ∃ k < n, ir.evalWith rd d e i = k
  | .columns cols =>
    ∃ j < (ir.value (cols.headD 0)).size, ∀ ec ∈ records.zip cols,
      ir.evalWith rd d ec.1 i = castElt (rd ec.2 j)
  | .expr e' => ∀ e ∈ records, ∃ j < ir.exprLen e', ir.evalWith rd d e i = ir.evalWith rd d e' j

instance (rd : ir.Valuation I) (d : ℕ) (records : List Expr) (i : ℕ) (rows : TableRows) :
    Decidable (ir.InRows rd d records i rows) := by
  cases rows <;> unfold InRows <;> infer_instance

/-- **A record is in a set**, reading values by `rd`: the range `[0, n)`, the rows of table `t`,
or the entries of the expression `e'` (`def:o-preds`: every entry of the record is an entry of
`e'`). -/
def InSetWith (rd : ir.Valuation I) (d : ℕ) (records : List Expr) (i : ℕ) : InSet → Prop
  | .range n => ir.InRows rd d records i (.range n)
  | .table t => ir.InRows rd d records i (ir.table t).rows
  | .expr e' => ir.InRows rd d records i (.expr e')

instance (rd : ir.Valuation I) (d : ℕ) (records : List Expr) (i : ℕ) (set : InSet) :
    Decidable (ir.InSetWith rd d records i set) := by
  cases set <;> unfold InSetWith <;> infer_instance

/-- **A predicate body holds**, reading values by `rd`. A cross-field `equal(x, y)` (`x` in domain
`dx`, `y` in domain `dy`) holds in the compiler's contract (compiler/mac.h): every reading of `y` is
below `2^width`, and where every reading of `x` is, the readings of `x` and `y` are equal. The MAC
binds the packed chunks of `x` to those of `y` and so states nothing about `x` when `x` holds field
elements other than bits: the Booleanity of `x` is the caller's. ML-DSA's H operand `c_enc² + c_enc`
is made with `bit_from_unchecked`, Boolean where the source program's shuffle holds; that is
established by the source program and proved in the round-by-round soundness of `Π_P₀`, not by the
realization. -/
def HoldsWith (rd : ir.Valuation I) : PredBody → Prop
  | .equal d e e' _ => ∀ i < ir.exprLen e, ir.evalWith rd d e i = ir.evalWith rd d e' i
  | .mem d records set _ =>
      ∀ i < ir.exprLen (records.headD default), ir.InSetWith rd d records i set
  | .mod d q e e' _ =>
      ∀ i < ir.exprLen e, (q : ℤ) ∣ ir.evalIntWith rd d e i - ir.evalIntWith rd d e' i
  | .cross dx ex dy ey k _ =>
      (∀ i < ir.exprLen ex, (I (ir.domainField dy)).toNat (ir.evalWith rd dy ey i) < 2 ^ k.width) ∧
        ((∀ i < ir.exprLen ex, (I (ir.domainField dx)).toNat (ir.evalWith rd dx ex i) < 2 ^ k.width) →
          ∀ i < ir.exprLen ex, (I (ir.domainField dx)).toNat (ir.evalWith rd dx ex i) =
            (I (ir.domainField dy)).toNat (ir.evalWith rd dy ey i))

instance (rd : ir.Valuation I) (b : PredBody) : Decidable (ir.HoldsWith rd b) := by
  cases b <;> unfold HoldsWith <;> infer_instance

/-- **A predicate body holds in the environment `e`**: `RealizedProgram.HoldsWith` at the environment's
reader. -/
def HoldsAt (e : ir.Env I) (b : PredBody) : Prop := ir.HoldsWith (ir.reader e) b

instance (e : ir.Env I) (b : PredBody) : Decidable (ir.HoldsAt e b) :=
  inferInstanceAs (Decidable (ir.HoldsWith _ b))

/-- **Every node-typed value lies in its type** in the environment `e`: a value whose type its
packing-tree node enforces (these hold by the packing; the proof system establishes them). -/
def TypesHold (e : ir.Env I) : Prop :=
  ∀ v < ir.values.length, (ir.value v).typeSource = .node →
    ∀ i < (ir.value v).size, (I (ir.valueField v)).InType (ir.value v).type (ir.reader e v i)

/-- **The program is satisfied in the environment `e`**: every predicate holds, and every value
whose type its node enforces lies in its type. -/
structure SatAt (e : ir.Env I) : Prop where
  /-- Every predicate holds. -/
  preds : ∀ p ∈ ir.predicates, ir.HoldsAt e p.body
  /-- Every node-typed value lies in its type. -/
  types : ir.TypesHold e

variable (I) in
/-- **`Pred P`, the program as a phased constraint** on its layout: `RealizedProgram.SatAt` at the
layout's environment. -/
def Pred : (ir.layout I).Constraint (ir.Valuation I) (ir.Assignment I) :=
  fun x a r => ir.SatAt (ir.layoutEnv I x a r)

/-! ## The statement's member checks -/

variable (I) in
/-- **The integer of a value's limbs** of `w` bits in the statement `x`: `Σ_i n_i 2^(w i)`, `n_i`
coordinate `i` of value `v` read as a natural (`FieldInterp.toNat`). -/
def limbsValue (x : ir.Valuation I) (v w : ℕ) : ℕ :=
  ((List.range (ir.value v).size).map fun i =>
    (I (ir.valueField v)).toNat (x v i) * 2 ^ (w * i)).sum

variable (I) in
/-- **A member check accepts the statement `x`**, by its kind (`MemberCheck.kind?`):

* a check with an entry bound `q` (`MemberCheck.entryBound?`): every coordinate of the member's
  value (`RealizedProgram.memberValue?`), read as a natural (`FieldInterp.toNat`), is below `q`;
* `p256_affine_point`: the member's value `(x, y)` satisfies `y² = x³ + a x + b` at P-256's
  coefficients (`p256A`, `p256B`) in its field;
* `limbBits b w L` (`rsa_modulus_2048`): every coordinate `n_i` of the member's value is below
  `2^w` and `2^(b−1) ≤ Σ_i n_i 2^(w i) < 2^b` (`limbsValue`).

A check whose member is no value or whose id is unknown accepts nothing (validity rejects both,
`RealizedProgram.CheckOk`).

The C++ check reads the member's canonical bytes; the statement here is the valuation those bytes
decode to, an entry `b` to the field element of the natural `b`. A valuation passes exactly when it
is the decoding of bytes the check accepts: for the entry bounds, an accepted entry `b < q` decodes
to an element whose natural is `b`, and a coordinate whose natural is at least `q` is the decoding
of no accepted entry; for P-256, the C++ check is the same curve equation in `F_p256`; for
`limbBits`, the C++ checks the top bit of the member's `b / 8` bytes, and a valuation passes exactly
when it is the limbs (`rsa_digits`) of a `b`-bit integer (CheckOk asks `2^w` at most the
characteristic, so each limb is the natural it decodes from). -/
def MemberHolds (x : ir.Valuation I) (m : MemberCheck) : Prop :=
  match ir.memberValue? m.member, m.entryBound? with
  | some v, some q => ∀ i < (ir.value v).size, (I (ir.valueField v)).toNat (x v i) < q
  | some v, none =>
    match m.kind? with
    | some .p256Point =>
      x v 1 ^ 2 = x v 0 ^ 3 + (p256A : (I (ir.valueField v)).K) * x v 0 +
        (p256B : (I (ir.valueField v)).K)
    | some (.limbBits b w _) =>
      (∀ i < (ir.value v).size, (I (ir.valueField v)).toNat (x v i) < 2 ^ w) ∧
        2 ^ (b - 1) ≤ ir.limbsValue I x v w ∧ ir.limbsValue I x v w < 2 ^ b
    | _ => False
  | none, _ => False

instance (x : ir.Valuation I) (m : MemberCheck) : Decidable (ir.MemberHolds I x m) := by
  unfold MemberHolds
  split
  · infer_instance
  · split <;> infer_instance
  · infer_instance

variable (I) in
/-- **The statement passes the program's member checks** (`StatementHeader.checks`): every check
accepts it (`MemberHolds`). A statement that fails is rejected before the transcript starts: the
source protocol's verifier and the proof system's both check it first (`RealizedProgram.sourceVerifier`,
`ProofSystem.enforcement`), and the honest prover is run only on statements that pass it
(`HonestStrategy.checks`). A program without checks passes every statement. -/
def StatementOk (x : ir.Valuation I) : Prop := ∀ m ∈ ir.statement.checks, ir.MemberHolds I x m

instance (x : ir.Valuation I) : Decidable (ir.StatementOk I x) := by
  unfold StatementOk
  infer_instance

/-- Whether a value's kind is read from the statement as given: a statement input or an opaque
statement value with no arguments. -/
def isStmtLeaf : Kind → Bool
  | .pub .input => true
  | .pub (.opaque _ []) => true
  | _ => false

/-- **The declared statement bounds** (`Value.bound`): `(v, N)` for every value read from the
statement as given (`isStmtLeaf`) that declares the bound `N`. -/
def declaredRanges : List (ℕ × ℕ) :=
  (List.range ir.values.length).filterMap fun v =>
    if isStmtLeaf (ir.value v).kind then (ir.value v).bound.map (v, ·) else none

variable (I) in
/-- **The statement lies within the declared bounds** (`declaredRanges`): every coordinate of a
bounded statement value is the cast of a natural below its bound. -/
def StmtBounded (x : ir.Valuation I) : Prop :=
  ∀ vN ∈ ir.declaredRanges, ∀ i < (ir.value vN.1).size,
    ∃ n < vN.2, x vN.1 i = ((n : ℕ) : (I (ir.valueField vN.1)).K)

variable {ir} in
/-- **A program declaring no bound bounds every statement.** -/
theorem stmtBounded_of_nil (h : ir.declaredRanges = []) (x : ir.Valuation I) :
    ir.StmtBounded I x := by
  intro vN hvN
  rw [h] at hvN
  cases hvN

variable (I) in
/-- **The statement is admissible**: it passes the member checks (`StatementOk`) and lies within
the declared bounds (`StmtBounded`). The verifier rejects any other statement before the
transcript starts (`stmtOk`). -/
def StatementIn (x : ir.Valuation I) : Prop := ir.StatementOk I x ∧ ir.StmtBounded I x

instance (x : ir.Valuation I) : Decidable (ir.StmtBounded I x) := by
  unfold StmtBounded
  infer_instance

instance (x : ir.Valuation I) : Decidable (ir.StatementIn I x) := by
  unfold StatementIn
  infer_instance

variable (I) in
/-- **The verifier's statement check**: `StatementIn` as a Boolean. -/
def stmtOk (x : ir.Valuation I) : Bool := decide (ir.StatementIn I x)

variable {ir} in
/-- The verifier's statement check is `StatementIn`. -/
theorem stmtOk_iff {x : ir.Valuation I} : ir.stmtOk I x = true ↔ ir.StatementIn I x :=
  decide_eq_true_iff

variable {ir} in
/-- **The member a check reads is below its bound**: where the statement passes the checks, a check
of the program whose member is value `v` and whose bound is `q` bounds every coordinate of `v`. -/
theorem StatementOk.toNat_lt {x : ir.Valuation I} (hx : ir.StatementOk I x) {m : MemberCheck}
    (hm : m ∈ ir.statement.checks) {v q : ℕ} (hv : ir.memberValue? m.member = some v)
    (hq : m.entryBound? = some q) {i : ℕ} (hi : i < (ir.value v).size) :
    (I (ir.valueField v)).toNat (x v i) < q := by
  have h := hx m hm
  unfold MemberHolds at h
  rw [hv, hq] at h
  exact h i hi

end

end GordieHowe.RealizedProgram
