-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.Affine
public import GordieHowe.ProofSystem.Zerocheck.AffineBatch

@[expose] public section

/-!
# GordieHowe: a program's batched relations

A batch of a program (`GordieHowe.RealizedProgram.batches`) proves its parts, the predicates whose target is
`batch(b)`, by one masked skip zerocheck. The compiler writes each part's field equation
`e − e' = 0` as a polynomial `Q` in affine operands (`compiler/batch_form.h`, `batch_form`) and
places predicates of one shape in one batch, their instances side by side
(`compiler/compiled_domain.h`, `group_kernel`: the relation of the group's first predicate, every
predicate's operands added to one operand map). This file compiles the same relation from the parts'
expressions:

* **The batch form** (`GordieHowe.RealizedProgram.bpoly`, `GordieHowe.RealizedProgram.partForm`): a side is a sum of signed monomials in
  atoms, an atom being a maximal subexpression of degree at most one in the cells reading only
  values the batch's operand map may read (`GordieHowe.RealizedProgram.atomB` on columns, `GordieHowe.RealizedProgram.bitsAtomB` on
  bits); sums, differences, constant multiples and products are distributed
  (`GordieHowe.RealizedProgram.eval_bpoly`). The monomials of degree other than one are placed on the distinct atoms
  (`placeMonos`; an atom read twice is one shared node, `ref k`, or one value, `leaf v`:
  `Expr.sameAtom`); the part of degree one is one operand, the last (`batch_form`: "the part of
  degree at most 1 ... is one operand, the last"), unless it is one term with coefficient `±1` on
  an atom of the other monomials, whose operand it then reuses; a monomial of degree one on a leaf
  of a zero constant is dropped (`zeroMonoB`; `batch_form` reads a constant as the constant monomial
  and drops a zero coefficient, `zero_coef`), which keeps the relation where the program's
  fields decode `0` to `0` (`GordieHowe.RealizedProgram.ZeroDecodes`) (`PartForm.reused`: `batch_form`'s
  `op(*lin)` for coefficient one, and the Boolean checks' relation `x·x − x` on one operand,
  `compiler/compiled_domain.h`). A form is padded to the degree-two shape `a b + c` as
  `batch_form` does with `pad_affine` (`Pad`, `padOf`): a form with no monomial of degree
  above one gets two constant-zero operands and the monomial `0 · 0`, a lone product of two
  distinct atoms a constant-zero linear operand. A shared expression that is not an atom, or a
  coefficient that is not a constant, has no form here.
* **The shape** (`PartForm.shape`, `Shape`): the operand count and the monomials, each a coefficient
  and its factors' operand positions; it is a relation of degree at most `D` when every monomial
  has between one and `D` factors on operands (`Shape.Ok`, so `Q` has no constant term), and then
  its relation is a `MonoRelation` (`Shape.rel`, `Shape.eval_rel`) with one product cell per
  multiset of at least two operands dividing a monomial (`Shape.cells`, `pad_monomials`).
* **The batch's relation** (`GordieHowe.RealizedProgram.relShape`): the parts' common shape, or, when the batch merges
  its parts by a challenge (`GordieHowe.RealizedProgram.merged`), the parts' monomials on their operands side by side
  (`GordieHowe.RealizedProgram.partOffset`, `GordieHowe.RealizedProgram.sliceShape`; `Σ_p γ^p Q_p` at `γ = 1`); an instance of part `j`
  reads the part's operands in its slice and constant zeros elsewhere (`GordieHowe.RealizedProgram.instOperand`), so
  the batch's relation there is the part's (`relShape_evalAt_instOperand`).
* **The parts' check** (`GordieHowe.RealizedProgram.PartsOk`, decided by `partsOkB`): the batch has parts, predicates
  with forms each of the batch's degree, of one shape or, merged, of one number of coordinates.
  The full batch check (`GordieHowe.RealizedProgram.BatchOk`) is in `GordieHowe/Language/RealizedProgram/Views.lean`.
* **The batched relation on columns** (`RealizedProgram.batchRelation d b`): on the cells of domain `d`, the
  instances every coordinate of every part, operand `j` of an instance the gradient of the operand's
  value at the cells (an affine function of the cells, `isAff_opValAt`) and its offset the value at
  zero. It holds exactly when every part placed holds (`batchRelation_holds_iff`: a field `equal`
  itself, a `mod_0` its field equation; the integer equation follows by `RealizeInteger`).
-/

namespace GordieHowe.RealizedProgram

open Export

/-! ## Batch forms -/

/-- **A coefficient of a batch form**: a sign and a product of constants (naturals of the C++
encoding). -/
structure BCoef where
  /-- The sign is negative. -/
  neg : Bool := false
  /-- The constant factors. -/
  consts : List ℕ := []
  deriving DecidableEq, Repr, Inhabited

namespace BCoef

/-- The product of two coefficients. -/
def mul (a b : BCoef) : BCoef := ⟨xor a.neg b.neg, a.consts ++ b.consts⟩

/-- The negated coefficient. -/
def negate (a : BCoef) : BCoef := ⟨!a.neg, a.consts⟩

/-- The coefficient times the constant `c`. -/
def scale (c : ℕ) (a : BCoef) : BCoef := ⟨a.neg, c :: a.consts⟩

/-- **The value of a coefficient** in a field: the sign times the product of the decoded
constants. -/
def val {I : Interp} {f : ℕ} (a : BCoef) : (I f).K :=
  (if a.neg then -1 else 1) * (a.consts.map (I f).decode).prod

variable {I : Interp} {f : ℕ}

theorem val_mul (a b : BCoef) : (a.mul b).val (I := I) (f := f) = a.val * b.val := by
  unfold val mul
  cases a.neg <;> cases b.neg <;> simp [List.prod_append]

theorem val_negate (a : BCoef) : a.negate.val (I := I) (f := f) = -a.val := by
  unfold val negate
  cases a.neg <;> simp

theorem val_scale (c : ℕ) (a : BCoef) :
    (a.scale c).val (I := I) (f := f) = (I f).decode c * a.val := by
  unfold val scale
  simp only [List.map_cons, List.prod_cons]
  ring

/-- The coefficient `1`. -/
def one : BCoef := ⟨false, []⟩

@[simp] theorem val_one : one.val (I := I) (f := f) = 1 := by
  simp [val, one]

end BCoef

/-- **A monomial of a batch form**: a coefficient and its factors, atoms. -/
structure BMono where
  /-- The coefficient. -/
  coef : BCoef := BCoef.one
  /-- The factors. -/
  factors : List Expr := []
  deriving Inhabited

namespace BMono

/-- The negated monomial. -/
def negate (m : BMono) : BMono := ⟨m.coef.negate, m.factors⟩

/-- The monomial times the constant `c`. -/
def scale (c : ℕ) (m : BMono) : BMono := ⟨m.coef.scale c, m.factors⟩

/-- The product of two monomials. -/
def mul (m m' : BMono) : BMono := ⟨m.coef.mul m'.coef, m.factors ++ m'.factors⟩

end BMono

/-- **Two atoms are one node**: the same shared expression or the same value (the export writes a
node read more than once as a shared expression, so the C++'s shared atoms are these). -/
def Expr.sameAtom : Expr → Expr → Bool
  | .ref a, .ref b => a == b
  | .leaf a, .leaf b => a == b
  | _, _ => false

theorem Expr.eq_of_sameAtom : ∀ {e e' : Expr}, Expr.sameAtom e e' = true → e = e'
  | .ref a, .ref b, h => by simp only [sameAtom, beq_iff_eq] at h; rw [h]
  | .leaf a, .leaf b, h => by simp only [sameAtom, beq_iff_eq] at h; rw [h]
  | .ref _, .leaf _, h | .leaf _, .ref _, h => by simp [sameAtom] at h
  | .add _ _, _, h | .sub _ _, _, h | .scale _ _, _, h | .mul _ _, _, h | .reindex _ _, _, h
  | .concat _ _, _, h | .linear _ _, _, h | .prod _ _, _, h | .mux _ _ _, _, h | .apply _ _, _, h
  | .logic _ _ _, _, h => by simp [sameAtom] at h
  | .ref _, .add _ _, h | .ref _, .sub _ _, h | .ref _, .scale _ _, h | .ref _, .mul _ _, h
  | .ref _, .reindex _ _, h | .ref _, .concat _ _, h | .ref _, .linear _ _, h | .ref _, .prod _ _, h
  | .ref _, .mux _ _ _, h | .ref _, .apply _ _, h | .ref _, .logic _ _ _, h => by simp [sameAtom] at h
  | .leaf _, .add _ _, h | .leaf _, .sub _ _, h | .leaf _, .scale _ _, h | .leaf _, .mul _ _, h
  | .leaf _, .reindex _ _, h | .leaf _, .concat _ _, h | .leaf _, .linear _ _, h
  | .leaf _, .prod _ _, h | .leaf _, .mux _ _ _, h | .leaf _, .apply _ _, h
  | .leaf _, .logic _ _ _, h => by simp [sameAtom] at h

section

variable (ir : RealizedProgram)

/-- **A value a batch operand may read**: a committed value of phase `0`, a pad copy, or a
constant (`compiler/compiled_domain.h`, the batch's leaf kinds; statement values, whose readings
would make an operand's linear part depend on the statement, are not admitted here). -/
def batchLeafOk (v : ℕ) : Bool :=
  match (ir.value v).kind with
  | .priv => (ir.value v).phase == 0
  | .padCopy _ _ => true
  | .constant _ => true
  | _ => false

/-- **An atom of a batch form**: an expression reading only values a batch operand may read
(`batchLeafOk`), with constant coefficients, of degree at most one in the cells. -/
def atomB (e : Expr) : Bool :=
  (ir.exprNodes e).all ir.batchLeafOk && (ir.closure Expr.coefNodes e).all (ir.cellNd · == 0) &&
    decide (ir.cellDeg e ≤ 1)

/-- A node of a batch form at the atom test `atom`: one monomial of degree one when the node is an
atom, `rest` otherwise. -/
def bnode (atom : Expr → Bool) (e : Expr) (rest : Option (List BMono)) : Option (List BMono) :=
  if atom e then some [⟨BCoef.one, [e]⟩] else rest

/-- **The batch form of an expression** (`batch_form`) at the atom test `atom` (`atomB` for a batch
on columns, `bitsAtomB` for one on bits): an atom is one monomial of degree one; sums,
differences, constant multiples and products are distributed; anything else has no form. -/
def bpoly (atom : Expr → Bool) : Expr → Option (List BMono)
  | .add a b => bnode atom (.add a b) do
      let p ← bpoly atom a
      let q ← bpoly atom b
      pure (p ++ q)
  | .sub a b => bnode atom (.sub a b) do
      let p ← bpoly atom a
      let q ← bpoly atom b
      pure (p ++ q.map BMono.negate)
  | .scale (.const c) a => bnode atom (.scale (.const c) a) do
      let p ← bpoly atom a
      pure (p.map (BMono.scale c))
  | .mul a b => bnode atom (.mul a b) do
      let p ← bpoly atom a
      let q ← bpoly atom b
      pure (p.flatMap fun m => q.map m.mul)
  | e => bnode atom e none

theorem bnode_eq_some {atom : Expr → Bool} {e : Expr} {rest : Option (List BMono)}
    {ms : List BMono} (h : bnode atom e rest = some ms) :
    (atom e = true ∧ ms = [⟨BCoef.one, [e]⟩]) ∨ (atom e = false ∧ rest = some ms) := by
  unfold bnode at h
  split_ifs at h with ha
  · exact .inl ⟨ha, (Option.some.inj h).symm⟩
  · exact .inr ⟨by simpa using ha, h⟩

variable {ir} {I : Interp}

/-- **The value of a monomial** at coordinate `i`, its factors evaluated by `ev`. -/
def BMono.val {f : ℕ} (ev : Expr → ℕ → (I f).K) (m : BMono) (i : ℕ) : (I f).K :=
  m.coef.val * (m.factors.map fun a => ev a i).prod

/-- **The value of a list of monomials**: their sum. -/
def bpolyVal {f : ℕ} (ev : Expr → ℕ → (I f).K) (ms : List BMono) (i : ℕ) : (I f).K :=
  (ms.map fun m => BMono.val ev m i).sum

theorem bpolyVal_append {f : ℕ} (ev : Expr → ℕ → (I f).K) (p q : List BMono) (i : ℕ) :
    bpolyVal ev (p ++ q) i = bpolyVal ev p i + bpolyVal ev q i := by
  simp [bpolyVal, List.sum_append]

theorem bpolyVal_negate {f : ℕ} (ev : Expr → ℕ → (I f).K) (q : List BMono) (i : ℕ) :
    bpolyVal ev (q.map BMono.negate) i = -bpolyVal ev q i := by
  induction q with
  | nil => simp [bpolyVal]
  | cons m q ih =>
    simp only [bpolyVal, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, neg_add]
    congr 1
    simp only [BMono.val, BMono.negate, BCoef.val_negate, neg_mul]

theorem bpolyVal_scale {f : ℕ} (ev : Expr → ℕ → (I f).K) (c : ℕ) (q : List BMono) (i : ℕ) :
    bpolyVal ev (q.map (BMono.scale c)) i = (I f).decode c * bpolyVal ev q i := by
  simp only [bpolyVal, List.map_map, ← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun m _ => ?_
  simp only [Function.comp_apply, BMono.val, BMono.scale, BCoef.val_scale]
  ring

theorem bpolyVal_mul {f : ℕ} (ev : Expr → ℕ → (I f).K) (p q : List BMono) (i : ℕ) :
    bpolyVal ev (p.flatMap fun m => q.map m.mul) i = bpolyVal ev p i * bpolyVal ev q i := by
  induction p with
  | nil => simp [bpolyVal]
  | cons m p ih =>
    rw [List.flatMap_cons, bpolyVal_append, ih]
    simp only [bpolyVal, List.map_cons, List.sum_cons, add_mul, List.map_map]
    congr 1
    rw [← List.sum_map_mul_left]
    congr 1
    refine List.map_congr_left fun m' _ => ?_
    simp only [Function.comp_apply, BMono.val, BMono.mul, BCoef.val_mul, List.map_append,
      List.prod_append]
    ring

/-- The value of the monomial of one atom. -/
theorem bpolyVal_atom {f : ℕ} (ev : Expr → ℕ → (I f).K) (e : Expr) (i : ℕ) :
    bpolyVal ev [⟨BCoef.one, [e]⟩] i = ev e i := by
  simp [bpolyVal, BMono.val]

/-- **The batch form's value is the expression's**: at every coordinate, the expression is the sum
of its form's monomials, each factor evaluated as the expression is (`Expr.eval` with the same
readings). -/
theorem eval_bpoly {atom : Expr → Bool} {f : ℕ} {leaf : ir.Valuation I} {ref : ℕ → ℕ → (I f).K}
    {rl : ℕ → ℕ} : ∀ (e : Expr) {ms : List BMono}, bpoly atom e = some ms → ∀ i,
      Expr.eval ir f leaf ref rl e i = bpolyVal (Expr.eval ir f leaf ref rl) ms i
  | .add a b, ms, h, i => by
    rw [bpoly] at h
    rcases bnode_eq_some h with ⟨-, rfl⟩ | ⟨-, h⟩
    · rw [bpolyVal_atom]
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨p, hp, q, hq, rfl⟩ := h
      simp only [Expr.eval, bpolyVal_append, eval_bpoly a hp, eval_bpoly b hq]
  | .sub a b, ms, h, i => by
    rw [bpoly] at h
    rcases bnode_eq_some h with ⟨-, rfl⟩ | ⟨-, h⟩
    · rw [bpolyVal_atom]
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨p, hp, q, hq, rfl⟩ := h
      simp only [Expr.eval, bpolyVal_append, bpolyVal_negate, eval_bpoly a hp, eval_bpoly b hq,
        sub_eq_add_neg]
  | .scale (.const c) a, ms, h, i => by
    rw [bpoly] at h
    rcases bnode_eq_some h with ⟨-, rfl⟩ | ⟨-, h⟩
    · rw [bpolyVal_atom]
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨p, hp, rfl⟩ := h
      simp only [Expr.eval, Coef.eval, bpolyVal_scale, eval_bpoly a hp]
  | .mul a b, ms, h, i => by
    rw [bpoly] at h
    rcases bnode_eq_some h with ⟨-, rfl⟩ | ⟨-, h⟩
    · rw [bpolyVal_atom]
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨p, hp, q, hq, rfl⟩ := h
      simp only [Expr.eval, bpolyVal_mul, eval_bpoly a hp, eval_bpoly b hq]
  | .leaf _, ms, h, i | .scale (.node _ _) _, ms, h, i | .reindex _ _, ms, h, i
  | .concat _ _, ms, h, i | .linear _ _, ms, h, i | .prod _ _, ms, h, i | .mux _ _ _, ms, h, i
  | .apply _ _, ms, h, i | .ref _, ms, h, i | .logic _ _ _, ms, h, i => by
    change bnode atom _ none = some ms at h
    rcases bnode_eq_some h with ⟨-, rfl⟩ | ⟨-, h⟩
    · rw [bpolyVal_atom]
    · cases h

/-- **Every factor of a batch form is an atom.** -/
theorem atom_of_mem_bpoly {atom : Expr → Bool} : ∀ (e : Expr) {ms : List BMono},
    bpoly atom e = some ms → ∀ m ∈ ms, ∀ a ∈ m.factors, atom a = true
  | .add x y, ms, h, m, hm, a, ha => by
    rw [bpoly] at h
    rcases bnode_eq_some h with ⟨hat, rfl⟩ | ⟨-, h⟩
    · simp only [List.mem_singleton] at hm
      subst hm
      simp only [List.mem_singleton] at ha
      subst ha
      exact hat
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨p, hp, q, hq, rfl⟩ := h
      rcases List.mem_append.1 hm with hm | hm
      · exact atom_of_mem_bpoly x hp m hm a ha
      · exact atom_of_mem_bpoly y hq m hm a ha
  | .sub x y, ms, h, m, hm, a, ha => by
    rw [bpoly] at h
    rcases bnode_eq_some h with ⟨hat, rfl⟩ | ⟨-, h⟩
    · simp only [List.mem_singleton] at hm
      subst hm
      simp only [List.mem_singleton] at ha
      subst ha
      exact hat
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨p, hp, q, hq, rfl⟩ := h
      rcases List.mem_append.1 hm with hm | hm
      · exact atom_of_mem_bpoly x hp m hm a ha
      · obtain ⟨m', hm', rfl⟩ := List.mem_map.1 hm
        exact atom_of_mem_bpoly y hq m' hm' a ha
  | .scale (.const c) x, ms, h, m, hm, a, ha => by
    rw [bpoly] at h
    rcases bnode_eq_some h with ⟨hat, rfl⟩ | ⟨-, h⟩
    · simp only [List.mem_singleton] at hm
      subst hm
      simp only [List.mem_singleton] at ha
      subst ha
      exact hat
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨p, hp, rfl⟩ := h
      obtain ⟨m', hm', rfl⟩ := List.mem_map.1 hm
      exact atom_of_mem_bpoly x hp m' hm' a ha
  | .mul x y, ms, h, m, hm, a, ha => by
    rw [bpoly] at h
    rcases bnode_eq_some h with ⟨hat, rfl⟩ | ⟨-, h⟩
    · simp only [List.mem_singleton] at hm
      subst hm
      simp only [List.mem_singleton] at ha
      subst ha
      exact hat
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨p, hp, q, hq, rfl⟩ := h
      obtain ⟨m₁, hm₁, hm⟩ := List.mem_flatMap.1 hm
      obtain ⟨m₂, hm₂, rfl⟩ := List.mem_map.1 hm
      rcases List.mem_append.1 ha with ha | ha
      · exact atom_of_mem_bpoly x hp m₁ hm₁ a ha
      · exact atom_of_mem_bpoly y hq m₂ hm₂ a ha
  | .leaf _, ms, h, m, hm, a, ha | .scale (.node _ _) _, ms, h, m, hm, a, ha
  | .reindex _ _, ms, h, m, hm, a, ha | .concat _ _, ms, h, m, hm, a, ha
  | .linear _ _, ms, h, m, hm, a, ha | .prod _ _, ms, h, m, hm, a, ha
  | .mux _ _ _, ms, h, m, hm, a, ha | .apply _ _, ms, h, m, hm, a, ha | .ref _, ms, h, m, hm, a, ha
  | .logic _ _ _, ms, h, m, hm, a, ha => by
    change bnode atom _ none = some ms at h
    rcases bnode_eq_some h with ⟨hat, rfl⟩ | ⟨-, h⟩
    · simp only [List.mem_singleton] at hm
      subst hm
      simp only [List.mem_singleton] at ha
      subst ha
      exact hat
    · cases h

end

/-! ## The form of a part -/

/-- **Place a factor among the atoms**: its position, appending it when no atom is the same node
(`Expr.sameAtom`). -/
def placeAtom (atoms : List Expr) (f : Expr) : List Expr × ℕ :=
  match atoms.findIdx? (Expr.sameAtom · f) with
  | some j => (atoms, j)
  | none => (atoms ++ [f], atoms.length)

/-- **Place a monomial's factors among the atoms**: each factor's position, in order. -/
def placeFactors : List Expr → List Expr → List Expr × List ℕ
  | atoms, [] => (atoms, [])
  | atoms, f :: fs => ((placeFactors (placeAtom atoms f).1 fs).1,
      (placeAtom atoms f).2 :: (placeFactors (placeAtom atoms f).1 fs).2)

/-- **Place the monomials**: each monomial's factors among the atoms, the monomial recorded as its
coefficient and the factors' positions. -/
def placeMonos : List Expr → List BMono → List Expr × List (BCoef × List ℕ)
  | atoms, [] => (atoms, [])
  | atoms, m :: ms => ((placeMonos (placeFactors atoms m.factors).1 ms).1,
      (m.coef, (placeFactors atoms m.factors).2) ::
        (placeMonos (placeFactors atoms m.factors).1 ms).2)

theorem placeAtom_spec (atoms : List Expr) (f : Expr) :
    (∃ t, (placeAtom atoms f).1 = atoms ++ t) ∧ (placeAtom atoms f).2 < (placeAtom atoms f).1.length ∧
      (placeAtom atoms f).1.getD (placeAtom atoms f).2 default = f := by
  unfold placeAtom
  split
  · rename_i j hj
    obtain ⟨hlt, hs, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hj
    refine ⟨⟨[], by simp⟩, hlt, ?_⟩
    rw [List.getD_eq_getElem _ _ hlt]
    exact Expr.eq_of_sameAtom hs
  · refine ⟨⟨[f], rfl⟩, by simp, ?_⟩
    rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
    rfl

/-- An extension keeps the entries at the old positions. -/
theorem getD_of_ext {l l' : List Expr} (h : ∃ t, l' = l ++ t) {i : ℕ} (hi : i < l.length) :
    l'.getD i default = l.getD i default := by
  obtain ⟨t, rfl⟩ := h
  exact List.getD_append _ _ _ _ hi

theorem ext_trans {l l' l'' : List Expr} (h : ∃ t, l' = l ++ t) (h' : ∃ t, l'' = l' ++ t) :
    ∃ t, l'' = l ++ t := by
  obtain ⟨t, rfl⟩ := h
  obtain ⟨t', rfl⟩ := h'
  exact ⟨t ++ t', by simp⟩

theorem length_le_of_ext {l l' : List Expr} (h : ∃ t, l' = l ++ t) : l.length ≤ l'.length := by
  obtain ⟨t, rfl⟩ := h
  simp

/-- **A placement relates a monomial to its record**: the coefficient, and positions of the atoms
`atoms` holding its factors. -/
def Placed (atoms : List Expr) (m : BMono) (c : BCoef × List ℕ) : Prop :=
  c.1 = m.coef ∧ (∀ j ∈ c.2, j < atoms.length) ∧ c.2.map (atoms.getD · default) = m.factors

/-- A placement stays a placement on an extension of the atoms. -/
theorem Placed.of_ext {atoms atoms' : List Expr} (h : ∃ t, atoms' = atoms ++ t) {m : BMono}
    {c : BCoef × List ℕ} (hp : Placed atoms m c) : Placed atoms' m c := by
  obtain ⟨hc, hlt, hmap⟩ := hp
  refine ⟨hc, fun j hj => (hlt j hj).trans_le (length_le_of_ext h), ?_⟩
  rw [← hmap]
  exact List.map_congr_left fun j hj => getD_of_ext h (hlt j hj)

/-- **The placed factors read the factors**: positions of the final atoms holding them. -/
theorem placeFactors_spec : ∀ (atoms fs : List Expr),
    (∃ t, (placeFactors atoms fs).1 = atoms ++ t) ∧
      (∀ j ∈ (placeFactors atoms fs).2, j < (placeFactors atoms fs).1.length) ∧
      (placeFactors atoms fs).2.map ((placeFactors atoms fs).1.getD · default) = fs
  | atoms, [] => ⟨⟨[], by simp [placeFactors]⟩, by simp [placeFactors], by simp [placeFactors]⟩
  | atoms, f :: fs => by
    obtain ⟨h1e, h1l, h1g⟩ := placeAtom_spec atoms f
    obtain ⟨h2e, h2l, h2g⟩ := placeFactors_spec (placeAtom atoms f).1 fs
    have hl := length_le_of_ext h2e
    refine ⟨ext_trans h1e h2e, ?_, ?_⟩
    · simp only [placeFactors, List.mem_cons, forall_eq_or_imp]
      exact ⟨by omega, h2l⟩
    · simp only [placeFactors, List.map_cons, h2g, List.cons.injEq, and_true]
      rw [getD_of_ext h2e h1l, h1g]

/-- **The placed monomials read their factors**: every recorded monomial is a monomial's
coefficient with positions of the final atoms holding its factors. -/
theorem placeMonos_spec : ∀ (atoms : List Expr) (ms : List BMono),
    (∃ t, (placeMonos atoms ms).1 = atoms ++ t) ∧
      List.Forall₂ (Placed (placeMonos atoms ms).1) ms (placeMonos atoms ms).2
  | atoms, [] => ⟨⟨[], by simp [placeMonos]⟩, by simp [placeMonos]⟩
  | atoms, m :: ms => by
    obtain ⟨h1e, h1l, h1g⟩ := placeFactors_spec atoms m.factors
    obtain ⟨h2e, h2f⟩ := placeMonos_spec (placeFactors atoms m.factors).1 ms
    exact ⟨ext_trans h1e h2e,
      List.Forall₂.cons (Placed.of_ext h2e ⟨rfl, h1l, h1g⟩) h2f⟩

/-- **An operand of a batch** (`batch_form`): one atom (a factor of a quadratic monomial), or the
linear part, signed constant multiples of atoms. -/
inductive BOperand where
  /-- An atom. -/
  | atom (e : Expr)
  /-- The linear part. -/
  | lin (terms : List (BCoef × Expr))
  /-- A constant-zero operand, added by the padding (`Pad`). -/
  | zero
  deriving Inhabited

/-- **The padding of a batch form** (`batch_form` with `pad_affine`, which `place_predicates`
passes): an affine form is written `a b + c` with `a`, `b` two constant-zero operands and `c` its
linear part, and a lone product `a b` of two distinct operands without a linear part is written
`a b + c` with `c` a constant-zero operand, so that either joins a batch of the degree-two shape
`a b + c`. -/
inductive Pad where
  /-- No padding. -/
  | none
  /-- The quadratic monomial `0 · 0` on two constant-zero operands, placed after the atoms. -/
  | zeroQuad
  /-- The linear monomial on a constant-zero operand, the last. -/
  | zeroLin
  deriving DecidableEq, Inhabited

/-- **The linear monomial of a shape** (`FieldRelation`'s monomial of degree one): the position of
its operand and its sign. The operand is the linear part itself (its own operand, the last, sign
positive), or an atom of the quadratic monomials that the linear part, one term with coefficient
`±1`, reuses. -/
structure LinOperand where
  /-- The operand's position. -/
  pos : ℕ
  /-- The sign is negative. -/
  neg : Bool
  deriving DecidableEq, Inhabited

/-- **The shape of a batch form** (`BatchForm::shape_key`): the operand count and the monomials,
each a coefficient and its factors' operand positions (with repetition): the monomials of degree at
least two on the atoms, the padding's, and the linear monomial (its operand's position, the
coefficient `±1`). -/
structure Shape where
  /-- The operand count. -/
  k : ℕ
  /-- The monomials. -/
  monos : List (BCoef × List ℕ)
  deriving DecidableEq, Inhabited

/-- **The form of a part** of a batch: the distinct atoms of its monomials of degree at least two,
those monomials on them, and its linear part. -/
structure PartForm where
  /-- The atoms of the monomials of degree at least two. -/
  atoms : List Expr
  /-- The monomials of degree at least two: coefficient and the factors' atom positions. -/
  monos : List (BCoef × List ℕ)
  /-- The linear part. -/
  lin : List (BCoef × Expr)
  /-- The padding. -/
  pad : Pad := .none
  deriving Inhabited

namespace PartForm

variable (pf : PartForm)

/-- The part has a linear part. -/
def hasLin : Bool := !pf.lin.isEmpty

/-- **The atom the linear part reuses**: when the linear part is one term with coefficient `±1` (no
constant factor) on an atom of the quadratic monomials (`Expr.sameAtom`), that atom's position and
the sign. The C++ writes the Boolean checks `v · v = v` as the relation `x·x − x` on one operand
(`compiler/compiled_domain.h`, the field batch of the Boolean checks), and `batch_form` reuses
the operand of an atom when the linear part is that atom with coefficient one (`op(*lin)`). -/
def reused : Option LinOperand :=
  match pf.lin with
  | [t] => if t.1.consts = [] then
      (pf.atoms.findIdx? (Expr.sameAtom · t.2)).map fun j => ⟨j, t.1.neg⟩
    else none
  | _ => none

/-- **The linear part is its own operand**: it has one and reuses no atom. -/
def linOwn : Bool := pf.hasLin && pf.reused.isNone

/-- **The constant-zero operands of the quadratic padding**: two with `Pad.zeroQuad`, none
otherwise. -/
def zeroOps : List BOperand := if pf.pad = .zeroQuad then [.zero, .zero] else []

/-- **The last operand**: the linear part when it is its own operand, a constant zero with
`Pad.zeroLin`, none otherwise. -/
def tailOps : List BOperand :=
  if pf.linOwn then [.lin pf.lin] else if pf.pad = .zeroLin then [.zero] else []

/-- **The operands of a part**: its atoms, the padding's constant zeros (`zeroOps`), then its
linear part when it is its own operand or the padding's constant zero (`tailOps`). -/
def operands : List BOperand := pf.atoms.map .atom ++ pf.zeroOps ++ pf.tailOps

/-- **The padding's quadratic monomial**: with `Pad.zeroQuad`, coefficient one on the two
constant-zero operands after the atoms. -/
def padMonos : List (BCoef × List ℕ) :=
  if pf.pad = .zeroQuad then [(BCoef.one, [pf.atoms.length, pf.atoms.length + 1])] else []

/-- **The linear monomial of a part**: the reused atom's position and sign (`reused`), or else the
last operand with sign positive, when the part has a linear part; the last operand, a constant zero,
with `Pad.zeroLin`; none otherwise. -/
def linOperand : Option LinOperand :=
  if pf.hasLin then some (pf.reused.getD ⟨pf.atoms.length + pf.zeroOps.length, false⟩)
  else if pf.pad = .zeroLin then some ⟨pf.atoms.length + pf.zeroOps.length, false⟩ else none

/-- **The linear monomial of a part as a monomial**: its operand's position, the coefficient `±1`. -/
def linMono : List (BCoef × List ℕ) :=
  match pf.linOperand with
  | some l => [(⟨l.neg, []⟩, [l.pos])]
  | none => []

/-- **The shape of a part**: the operands; the monomials of degree at least two, the padding's and
the linear monomial. -/
def shape : Shape := ⟨pf.operands.length, pf.monos ++ pf.padMonos ++ pf.linMono⟩

end PartForm

section

variable (ir : RealizedProgram)

/-- **The padding of a form** (`batch_form`'s `pad_affine`): `Pad.zeroQuad` when there are no
monomials of degree at least two and a linear part; `Pad.zeroLin` when there is no linear part and
one monomial, a product of two distinct atoms; `Pad.none` otherwise. -/
def padOf (monos : List (BCoef × List ℕ)) (low : List BMono) : Pad :=
  if monos.isEmpty && !low.isEmpty then .zeroQuad
  else if low.isEmpty && (match monos with | [(_, [a, b])] => a != b | _ => false) then .zeroLin
  else .none

/-- **A leaf of a zero constant**: a leaf of a constant value of a field of the program whose
entries are all `0` (the export writes `assert_zero(e)` as `e = c` with such a constant `c`;
`batch_form` reads a constant node as the constant monomial and drops a monomial whose coefficient
is zero, `zero_coef`). -/
def zeroLeafB : Expr → Bool
  | .leaf v => decide (ir.valueField v < ir.fields.length) &&
      match (ir.value v).kind with
      | .constant es => es.all (· == 0)
      | _ => false
  | _ => false

/-- **A monomial the batch form drops**: one whose factors are leaves of zero constants
(`zeroLeafB`; on a monomial of degree one, `batch_form`'s `zero_coef`). -/
def zeroMonoB (m : BMono) : Bool := m.factors.all ir.zeroLeafB

/-- **The program's fields decode the constant `0` to `0`** (a property of the model; from
`Interp.Lawful.decode_natCast` at `0`, `Interp.zeroDecodes_of_lawful`). -/
def ZeroDecodes (I : Interp) : Prop := ∀ f < ir.fields.length, (I f).decode 0 = 0

/-- **The form of a part** with sides `e`, `e'`: the batch forms of `e` and of `−e'`; the monomials
of degree other than one placed on their atoms (`placeMonos`), the monomials of degree one as the
linear part, without those on a zero constant (`zeroMonoB`, `batch_form`'s `zero_coef`), padded by
`padOf`. -/
def partForm (atom : Expr → Bool) (e e' : Expr) : Option PartForm := do
  let p ← bpoly atom e
  let q ← bpoly atom e'
  let ms := p ++ q.map BMono.negate
  let high := ms.filter (·.factors.length != 1)
  let low := (ms.filter (·.factors.length == 1)).filter fun m => !ir.zeroMonoB m
  pure ⟨(placeMonos [] high).1, (placeMonos [] high).2,
    low.map fun m => (m.coef, m.factors.getD 0 default), padOf (placeMonos [] high).2 low⟩

end

/-! ## The relation of a shape -/

open Sumcheck.FieldSkip (MonoRelation)

/-- **The value of a list of monomials** at operand values `y` (`FieldRelation::eval`): the sum of
the monomials, each its coefficient times its factors' values. -/
def monosEval {I : Interp} {f : ℕ} (ms : List (BCoef × List ℕ)) (y : ℕ → (I f).K) : (I f).K :=
  (ms.map fun c => c.1.val * (c.2.map y).prod).sum

section MonosEval

variable {I : Interp} {f : ℕ}

theorem monosEval_append (ms ms' : List (BCoef × List ℕ)) (y : ℕ → (I f).K) :
    monosEval (ms ++ ms') y = monosEval ms y + monosEval ms' y := by
  simp [monosEval, List.sum_append]

theorem monosEval_flatMap {α : Type} (l : List α) (g : α → List (BCoef × List ℕ))
    (y : ℕ → (I f).K) : monosEval (l.flatMap g) y = (l.map fun a => monosEval (g a) y).sum := by
  induction l with
  | nil => simp [monosEval]
  | cons a l ih => rw [List.flatMap_cons, monosEval_append, ih, List.map_cons, List.sum_cons]

theorem monosEval_congr {ms : List (BCoef × List ℕ)} {y y' : ℕ → (I f).K}
    (h : ∀ c ∈ ms, ∀ j ∈ c.2, y j = y' j) : monosEval ms y = monosEval ms y' := by
  unfold monosEval
  refine congrArg _ (List.map_congr_left fun c hc => ?_)
  rw [List.map_congr_left (h c hc)]

/-- Monomials each reading a zero factor vanish. -/
theorem monosEval_eq_zero {ms : List (BCoef × List ℕ)} {y : ℕ → (I f).K}
    (h : ∀ c ∈ ms, ∃ j ∈ c.2, y j = 0) : monosEval ms y = 0 := by
  unfold monosEval
  refine List.sum_eq_zero fun x hx => ?_
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx
  obtain ⟨j, hj, h0⟩ := h c hc
  rw [List.prod_eq_zero (List.mem_map.2 ⟨j, hj, h0⟩), mul_zero]

end MonosEval

/-- A sum over `range n` with one nonzero term is that term. -/
theorem sum_map_range_single {M : Type} [AddCommMonoid M] {g : ℕ → M} :
    ∀ {n j : ℕ}, j < n → (∀ p < n, p ≠ j → g p = 0) → ((List.range n).map g).sum = g j
  | 0, _, hj, _ => absurd hj (Nat.not_lt_zero _)
  | n + 1, j, hj, h => by
    rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · rw [sum_map_range_single hj fun p hp hpj => h p (by omega) hpj, h n (by omega) (by omega),
        add_zero]
    · rw [List.sum_eq_zero fun x hx => ?_, zero_add]
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
      exact h p (by simp at hp; omega) (by simp at hp; omega)

namespace Shape

variable {I : Interp} {f : ℕ}

/-- **The value of a shape** at operand values `y` (`monosEval` of its monomials). -/
abbrev evalAt (sh : Shape) (y : ℕ → (I f).K) : (I f).K := monosEval sh.monos y

/-- **The value of a shape on `k` operands**: `evalAt` with the operands beyond `k` zero. -/
def evalFin (sh : Shape) (x : Fin sh.k → (I f).K) : (I f).K :=
  sh.evalAt fun j => if hj : j < sh.k then x ⟨j, hj⟩ else 0

/-- **The monomials of a shape on operands shifted by `o`.** -/
def shift (sh : Shape) (o : ℕ) : List (BCoef × List ℕ) :=
  sh.monos.map fun c => (c.1, c.2.map (· + o))

theorem monosEval_shift (sh : Shape) (o : ℕ) (y : ℕ → (I f).K) :
    monosEval (sh.shift o) y = sh.evalAt fun j => y (j + o) := by
  simp [monosEval, shift, List.map_map, Function.comp_def]

/-- **The shape is a relation of degree at most `D`**: every monomial has between one and `D`
factors, each on an operand below `k`. -/
structure Ok (sh : Shape) (D : ℕ) : Prop where
  /-- No monomial is constant. -/
  ne_nil : ∀ c ∈ sh.monos, c.2 ≠ []
  /-- Every monomial has at most `D` factors. -/
  length_le : ∀ c ∈ sh.monos, c.2.length ≤ D
  /-- Every factor is an operand. -/
  lt : ∀ c ∈ sh.monos, ∀ j ∈ c.2, j < sh.k

/-- **`Ok`, decided.** -/
def okB (sh : Shape) (D : ℕ) : Bool :=
  sh.monos.all fun c => decide (c.2 ≠ []) && decide (c.2.length ≤ D) && c.2.all (· < sh.k)

theorem okB_iff (sh : Shape) (D : ℕ) : sh.okB D = true ↔ sh.Ok D := by
  simp only [okB, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨fun h => ⟨fun c hc => (h c hc).1.1, fun c hc => (h c hc).1.2, fun c hc => (h c hc).2⟩,
    fun h c hc => ⟨⟨h.ne_nil c hc, h.length_le c hc⟩, h.lt c hc⟩⟩

variable (I f) in
/-- **The relation of a shape** of degree at most `D` in field `f` (`FieldRelation`): monomial `i`
the coefficient's value times the operands at its positions. -/
def rel (sh : Shape) (D : ℕ) (h : sh.Ok D) : MonoRelation (I f).K sh.k D where
  nm := sh.monos.length
  deg i := sh.monos[i].2.length
  ops i t := ⟨sh.monos[i].2[t], h.lt _ (List.getElem_mem _) _ (List.getElem_mem _)⟩
  coeff i := sh.monos[i].1.val
  deg_pos i := List.length_pos_iff.2 (h.ne_nil _ (List.getElem_mem _))
  deg_le i := h.length_le _ (List.getElem_mem _)

/-- **The relation's value is the shape's.** -/
theorem eval_rel (sh : Shape) {D : ℕ} (h : sh.Ok D) (x : Fin sh.k → (I f).K) :
    (sh.rel I f D h).eval x = sh.evalFin x := by
  simp only [MonoRelation.eval, rel, evalFin, evalAt, monosEval]
  rw [← Fin.sum_univ_fun_getElem]
  refine Finset.sum_congr rfl fun i _ => congrArg _ ?_
  rw [← Fin.prod_univ_fun_getElem]
  refine Finset.prod_congr rfl fun t _ => ?_
  rw [dif_pos (h.lt _ (List.getElem_mem _) _ (List.getElem_mem _))]
  simp [Fin.getElem_fin]

/-- **The product cells of a shape** (`pad_monomials`): the multisets of at least two operands
dividing a monomial. -/
def cellSet (sh : Shape) : Finset (Multiset ℕ) :=
  sh.monos.toFinset.biUnion fun c =>
    ((c.2 : Multiset ℕ).powerset.toFinset).filter fun M => 2 ≤ Multiset.card M

/-- **The number of product cells of a shape.** -/
def cells (sh : Shape) : ℕ := sh.cellSet.card

end Shape

/-- **The value of an operand** at coordinate `i`, atoms evaluated by `ev`. -/
def BOperand.val {I : Interp} {f : ℕ} (ev : Expr → ℕ → (I f).K) : BOperand → ℕ → (I f).K
  | .atom e, i => ev e i
  | .lin ts, i => (ts.map fun t => t.1.val * ev t.2 i).sum
  | .zero, _ => 0

/-- A sum of a list splits by a predicate. -/
theorem sum_map_filter_add {α M : Type} [AddCommMonoid M] (g : α → M) (P : α → Bool) :
    ∀ l : List α, (l.map g).sum = ((l.filter P).map g).sum + ((l.filter fun a => !P a).map g).sum
  | [] => by simp
  | a :: l => by
    rw [List.map_cons, List.sum_cons, sum_map_filter_add g P l]
    cases h : P a <;> simp [h] <;> abel

theorem sum_map_congr {α M : Type} [AddCommMonoid M] {g g' : α → M} {l : List α}
    (h : ∀ a ∈ l, g a = g' a) : (l.map g).sum = (l.map g').sum := by
  rw [List.map_congr_left h]

section

variable {ir : RealizedProgram} {I : Interp}

/-- **The placed monomials keep their value.** -/
theorem bpolyVal_placed {f : ℕ} (ev : Expr → ℕ → (I f).K) (atoms : List Expr) (i : ℕ) :
    ∀ {ms : List BMono} {cs : List (BCoef × List ℕ)}, List.Forall₂ (Placed atoms) ms cs →
      bpolyVal ev ms i = monosEval cs fun j => ev (atoms.getD j default) i
  | _, _, .nil => rfl
  | m :: ms, c :: cs, .cons hq hF => by
    have ih := bpolyVal_placed ev atoms i hF
    unfold bpolyVal monosEval at ih ⊢
    rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, ih]
    congr 1
    obtain ⟨hc, -, hmap⟩ := hq
    rw [BMono.val, hc, ← hmap, List.map_map]
    rfl

/-- **The monomials of degree one keep their value** as the linear part. -/
theorem bpolyVal_linear {f : ℕ} (ev : Expr → ℕ → (I f).K) (i : ℕ) {low : List BMono}
    (hl : ∀ m ∈ low, m.factors.length = 1) :
    bpolyVal ev low i = ((low.map fun m => (m.coef, m.factors.getD 0 default)).map
      fun t => t.1.val * ev t.2 i).sum := by
  unfold bpolyVal
  rw [List.map_map]
  refine sum_map_congr fun m hm => ?_
  obtain ⟨f₀, hf⟩ : ∃ f₀, m.factors = [f₀] := by
    have h1 := hl m hm
    match m.factors, h1 with
    | [a], _ => exact ⟨a, rfl⟩
  simp [BMono.val, hf]

/-- An entry of the right list of a `Forall₂` is related to an entry of the left. -/
theorem exists_of_forall₂ {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → ∀ c ∈ l', ∃ m ∈ l, R m c
  | _, _, .nil, _, hc => absurd hc List.not_mem_nil
  | m :: _, _ :: _, .cons h hF, c, hc => by
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ⟨m, List.mem_cons_self, h⟩
    · obtain ⟨m', hm', h'⟩ := exists_of_forall₂ hF c hc
      exact ⟨m', List.mem_cons_of_mem _ hm', h'⟩

theorem operands_getD_atom (pf : PartForm) {a : ℕ} (ha : a < pf.atoms.length) :
    pf.operands.getD a default = .atom (pf.atoms.getD a default) := by
  rw [PartForm.operands, List.append_assoc, List.getD_append _ _ _ _ (by simpa using ha)]
  simp [ha]

/-- **The padding's operands after the atoms are constant zeros.** -/
theorem operands_getD_zeroOps (pf : PartForm) {j : ℕ} (hj : j < pf.zeroOps.length) :
    pf.operands.getD (pf.atoms.length + j) default = .zero := by
  have hz : ∀ o ∈ pf.zeroOps, o = .zero := by
    unfold PartForm.zeroOps
    split_ifs <;> simp
  rw [PartForm.operands, List.getD_append _ _ _ _ (by simp; omega),
    List.getD_append_right _ _ _ _ (by simp), List.length_map, Nat.add_sub_cancel_left,
    List.getD_eq_getElem _ _ hj]
  exact hz _ (List.getElem_mem _)

/-- **The operand after the atoms and the padding's zeros is the last operand** (`tailOps`). -/
theorem operands_getD_tailOps (pf : PartForm) :
    pf.operands.getD (pf.atoms.length + pf.zeroOps.length) default =
      pf.tailOps.getD 0 default := by
  rw [PartForm.operands, List.getD_append_right _ _ _ _ (by simp)]
  simp

/-- **The atom a linear part reuses**: the linear part is one term with coefficient `±1`, the sign
the reused position's, on the atom at that position. -/
theorem exists_of_reused {pf : PartForm} {l : LinOperand} (hr : pf.reused = some l) :
    ∃ t, pf.lin = [t] ∧ t.1.consts = [] ∧ l.neg = t.1.neg ∧ l.pos < pf.atoms.length ∧
      pf.atoms.getD l.pos default = t.2 := by
  unfold PartForm.reused at hr
  split at hr
  · rename_i t ht
    by_cases hc : t.1.consts = []
    · rw [if_pos hc] at hr
      obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.1 hr
      obtain ⟨hlt, hs, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hj
      refine ⟨t, ht, hc, rfl, hlt, ?_⟩
      rw [List.getD_eq_getElem _ _ hlt]
      exact Expr.eq_of_sameAtom hs
    · rw [if_neg hc] at hr
      cases hr
  · cases hr

/-- **The linear monomial of a part's shape on its operands is its linear part**: the linear part as
its own operand with coefficient one, or the reused atom with the term's coefficient `±1`, or the
padding's constant zero. -/
theorem linMono_eval {f : ℕ} (ev : Expr → ℕ → (I f).K) (i : ℕ) (pf : PartForm) :
    monosEval pf.linMono (fun j => (pf.operands.getD j default).val ev i) =
      if pf.hasLin then (pf.lin.map fun t => t.1.val * ev t.2 i).sum else 0 := by
  unfold PartForm.linMono PartForm.linOperand
  by_cases hl : pf.hasLin
  · rw [if_pos hl, if_pos hl]
    cases hr : pf.reused with
    | none =>
      have hown : pf.linOwn = true := by simp [PartForm.linOwn, hl, hr]
      have ht : pf.tailOps = [.lin pf.lin] := by simp [PartForm.tailOps, hown]
      simp only [Option.getD_none, monosEval, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, add_zero, List.prod_cons, List.prod_nil, mul_one]
      rw [operands_getD_tailOps, ht]
      simp [BOperand.val, BCoef.val]
    | some l =>
      obtain ⟨t, hlin, hc, hneg, hlt, hat⟩ := exists_of_reused hr
      simp only [Option.getD_some, monosEval, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, add_zero, List.prod_cons, List.prod_nil, mul_one]
      rw [operands_getD_atom pf hlt, hat, hlin]
      simp only [BOperand.val, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
        BCoef.val, hc, List.prod_nil, mul_one, hneg]
  · rw [if_neg hl, if_neg hl]
    split_ifs with hz
    · have hown : pf.linOwn = false := by simp [PartForm.linOwn, hl]
      have ht : pf.tailOps = [.zero] := by simp [PartForm.tailOps, hown, hz]
      simp only [monosEval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
        List.prod_cons, List.prod_nil, mul_one]
      rw [operands_getD_tailOps, ht]
      simp [BOperand.val]
    · simp [monosEval]

/-- **The padding's monomial vanishes**: `0 · 0` on the two constant-zero operands. -/
theorem padMonos_eval {f : ℕ} (ev : Expr → ℕ → (I f).K) (i : ℕ) (pf : PartForm) :
    monosEval pf.padMonos (fun j => (pf.operands.getD j default).val ev i) = 0 := by
  unfold PartForm.padMonos
  split_ifs with hz
  · have hz2 : pf.zeroOps.length = 2 := by simp [PartForm.zeroOps, hz]
    have h0 : pf.operands.getD pf.atoms.length default = .zero := by
      simpa using operands_getD_zeroOps pf (j := 0) (by omega)
    simp only [monosEval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.prod_cons,
      List.prod_nil, h0, BOperand.val, zero_mul, mul_zero, add_zero]
  · simp [monosEval]

/-- **The relation of a part's shape on its operands**: its monomials on the atoms and its linear
part. -/
theorem shape_evalAt {f : ℕ} (ev : Expr → ℕ → (I f).K) (i : ℕ) (pf : PartForm)
    (hq : ∀ c ∈ pf.monos, ∀ j ∈ c.2, j < pf.atoms.length) :
    pf.shape.evalAt (fun j => (pf.operands.getD j default).val ev i) =
      monosEval pf.monos (fun j => ev (pf.atoms.getD j default) i) +
        if pf.hasLin then (pf.lin.map fun t => t.1.val * ev t.2 i).sum else 0 := by
  show monosEval (pf.monos ++ pf.padMonos ++ pf.linMono) _ = _
  rw [monosEval_append, monosEval_append, padMonos_eval, add_zero, linMono_eval]
  congr 1
  refine monosEval_congr fun c hc j hj => ?_
  rw [operands_getD_atom pf (hq c hc j hj)]
  rfl

/-- **A monomial on a zero constant vanishes** at a reading of the zero constants as `0`. -/
theorem BMono.val_eq_zero_of_zeroMonoB {f : ℕ} {ev : Expr → ℕ → (I f).K} {m : BMono}
    (hz : ∀ a, ir.zeroLeafB a = true → ∀ i, ev a i = 0) (hm : ir.zeroMonoB m = true)
    (hne : m.factors ≠ []) (i : ℕ) : BMono.val ev m i = 0 := by
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ hne
  rw [BMono.val, List.prod_eq_zero (List.mem_map.2 ⟨a, ha, hz a (List.all_eq_true.1 hm a ha) i⟩),
    mul_zero]

/-- **Dropping the monomials on zero constants keeps the value** (`zeroMonoB`), of nonconstant
monomials at a reading of the zero constants as `0`. -/
theorem bpolyVal_filter_zeroMonoB {f : ℕ} {ev : Expr → ℕ → (I f).K} {ms : List BMono}
    (hz : ∀ a, ir.zeroLeafB a = true → ∀ i, ev a i = 0) (hne : ∀ m ∈ ms, m.factors ≠ [])
    (i : ℕ) : bpolyVal ev (ms.filter fun m => !ir.zeroMonoB m) i = bpolyVal ev ms i := by
  unfold bpolyVal
  symm
  rw [sum_map_filter_add _ (fun m => !ir.zeroMonoB m) ms, add_eq_left]
  refine List.sum_eq_zero fun x hx => ?_
  obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hx
  obtain ⟨hm, hzm⟩ := List.mem_filter.1 hm
  exact BMono.val_eq_zero_of_zeroMonoB hz (by simpa using hzm) (hne m hm) i

/-- **The relation of a part's shape on its operands is its field equation**: at every
coordinate, `e − e'` is the shape's relation on the part's operands, every atom evaluated as the
sides are, when the leaves of zero constants read `0` (`hz`; `zeroLeafB`). -/
theorem partForm_eval {atom : Expr → Bool} {f : ℕ} {leaf : ir.Valuation I}
    {ref : ℕ → ℕ → (I f).K} {rl : ℕ → ℕ} {e e' : Expr} {pf : PartForm}
    (hz : ∀ a, ir.zeroLeafB a = true → ∀ i, Expr.eval ir f leaf ref rl a i = 0)
    (h : ir.partForm atom e e' = some pf) (i : ℕ) :
    Expr.eval ir f leaf ref rl e i - Expr.eval ir f leaf ref rl e' i =
      pf.shape.evalAt fun j => (pf.operands.getD j default).val (Expr.eval ir f leaf ref rl) i := by
  simp only [partForm, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨p, hp, q, hq, h⟩ := h
  simp only [Option.pure_def, Option.some.injEq] at h
  subst h
  generalize hms : p ++ q.map BMono.negate = ms
  have hlhs : Expr.eval ir f leaf ref rl e i - Expr.eval ir f leaf ref rl e' i =
      bpolyVal (Expr.eval ir f leaf ref rl) (ms.filter (·.factors.length != 1)) i +
        bpolyVal (Expr.eval ir f leaf ref rl)
          ((ms.filter (·.factors.length == 1)).filter fun m => !ir.zeroMonoB m) i := by
    rw [bpolyVal_filter_zeroMonoB hz (fun m hm h0 => by
        simpa [h0] using (List.mem_filter.1 hm).2),
      eval_bpoly e hp, eval_bpoly e' hq, sub_eq_add_neg, ← bpolyVal_negate, ← bpolyVal_append,
      hms]
    unfold bpolyVal
    rw [sum_map_filter_add _ (·.factors.length != 1) ms]
    congr 3
    exact List.filter_congr fun m _ => by simp [bne]
  obtain ⟨-, hF⟩ := placeMonos_spec [] (ms.filter (·.factors.length != 1))
  have hl1 : ∀ m ∈ (ms.filter (·.factors.length == 1)).filter (fun m => !ir.zeroMonoB m),
      m.factors.length = 1 :=
    fun m hm => by simpa using (List.mem_filter.1 (List.mem_filter.1 hm).1).2
  rw [hlhs, shape_evalAt _ _ _ fun c hc j hj => by
      obtain ⟨m, -, hR⟩ := exists_of_forall₂ hF c hc
      exact hR.2.1 j hj,
    bpolyVal_placed _ _ _ hF, bpolyVal_linear _ _ hl1]
  congr 1
  simp only [PartForm.hasLin]
  generalize List.map (fun m => (m.coef, m.factors.getD 0 default))
    ((ms.filter (·.factors.length == 1)).filter (fun m => !ir.zeroMonoB m)) = L
  cases L <;> simp

/-- Every atom of a placement is a placed factor or an earlier atom. -/
theorem mem_placeAtom {atoms : List Expr} {f a : Expr} (h : a ∈ (placeAtom atoms f).1) :
    a ∈ atoms ∨ a = f := by
  unfold placeAtom at h
  split at h
  · exact .inl h
  · rcases List.mem_append.1 h with h | h
    · exact .inl h
    · exact .inr (List.mem_singleton.1 h)

theorem mem_placeFactors : ∀ {atoms fs : List Expr} {a : Expr},
    a ∈ (placeFactors atoms fs).1 → a ∈ atoms ∨ a ∈ fs
  | _, [], _, h => .inl h
  | atoms, f :: fs, a, h => by
    rcases mem_placeFactors (atoms := (placeAtom atoms f).1) h with h | h
    · rcases mem_placeAtom h with h | rfl
      · exact .inl h
      · exact .inr List.mem_cons_self
    · exact .inr (List.mem_cons_of_mem _ h)

theorem mem_placeMonos : ∀ {atoms : List Expr} {ms : List BMono} {a : Expr},
    a ∈ (placeMonos atoms ms).1 → a ∈ atoms ∨ ∃ m ∈ ms, a ∈ m.factors
  | _, [], _, h => .inl h
  | atoms, m :: ms, a, h => by
    rcases mem_placeMonos (atoms := (placeFactors atoms m.factors).1) h with h | ⟨m', hm', ha⟩
    · rcases mem_placeFactors h with h | h
      · exact .inl h
      · exact .inr ⟨m, List.mem_cons_self, h⟩
    · exact .inr ⟨m', List.mem_cons_of_mem _ hm', ha⟩

/-- **Every operand of a part's form reads atoms only**: an atom, a linear part of atoms, or the
padding's constant zero. -/
theorem operand_atoms {atom : Expr → Bool} {e e' : Expr} {pf : PartForm}
    (h : ir.partForm atom e e' = some pf) {o : BOperand} (ho : o ∈ pf.operands) :
    (∃ a, o = .atom a ∧ atom a = true) ∨
      (∃ ts, o = .lin ts ∧ ∀ t ∈ ts, atom t.2 = true) ∨ o = .zero := by
  simp only [partForm, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨p, hp, q, hq, h⟩ := h
  simp only [Option.pure_def, Option.some.injEq] at h
  subst h
  have hatom : ∀ m ∈ p ++ q.map BMono.negate, ∀ a ∈ m.factors, atom a = true := by
    intro m hm a ha
    rcases List.mem_append.1 hm with hm | hm
    · exact atom_of_mem_bpoly e hp m hm a ha
    · obtain ⟨m', hm', rfl⟩ := List.mem_map.1 hm
      exact atom_of_mem_bpoly e' hq m' hm' a ha
  unfold PartForm.operands at ho
  rcases List.mem_append.1 ho with ho | ho
  · rcases List.mem_append.1 ho with ho | ho
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 ho
      refine .inl ⟨a, rfl, ?_⟩
      rcases mem_placeMonos ha with ha | ⟨m, hm, ha⟩
      · simp at ha
      · exact hatom m (List.mem_filter.1 hm).1 a ha
    · refine .inr (.inr ?_)
      unfold PartForm.zeroOps at ho
      split_ifs at ho <;> simp_all
  · unfold PartForm.tailOps at ho
    split_ifs at ho
    · rcases List.mem_singleton.1 ho with rfl
      refine .inr (.inl ⟨_, rfl, fun t ht => ?_⟩)
      obtain ⟨m, hm, rfl⟩ := List.mem_map.1 ht
      have hm := (List.mem_filter.1 hm).1
      have h1 : m.factors.length = 1 := by simpa using (List.mem_filter.1 hm).2
      exact hatom m (List.mem_filter.1 hm).1 _ (by
        rw [List.getD_eq_getElem _ _ (by omega)]
        exact List.getElem_mem _)
    · exact .inr (.inr (List.mem_singleton.1 ho))
    · simp at ho

end

/-! ## The batched relation -/

/-- **The sides of a predicate of domain `d` placed in batch `b`**: a field `equal`'s with target
`batch(b)`, or a `mod_0`'s field equation's with that target. -/
def PredBody.batchSides (body : PredBody) (d b : ℕ) : Option (Expr × Expr) :=
  match body with
  | .equal d' e e' (.batch b') => if d' = d ∧ b' = b then some (e, e') else none
  | .mod d' 0 e e' real => if d' = d ∧ real.target = some (.batch b) then some (e, e') else none
  | _ => none

section

/-- **A batched predicate placed holds exactly when its sides agree** (`PlacedHolds`: a field
`equal` itself, a `mod_0` its field equation). -/
theorem placedHolds_iff_of_batchSides {ir : RealizedProgram} {I : Interp} {body : PredBody} {d b : ℕ}
    {e e' : Expr} (h : body.batchSides d b = some (e, e')) (rd : ir.Valuation I) :
    ir.PlacedHolds rd body ↔ ∀ i < ir.exprLen e, ir.evalWith rd d e i = ir.evalWith rd d e' i := by
  unfold PredBody.batchSides at h
  split at h
  · split_ifs at h with hd
    cases h
    obtain ⟨rfl, -⟩ := hd
    rfl
  · split_ifs at h with hd
    cases h
    rw [hd.1]
    simp [PlacedHolds]
  · cases h

variable (ir : RealizedProgram)

/-- The predicate of part `j` of batch `b`. -/
def partPred (b j : ℕ) : ℕ := (ir.batch b).parts.getD j 0

/-- **The sides of part `j` of batch `b`** in domain `d`. -/
def partSides (d b j : ℕ) : Option (Expr × Expr) :=
  (ir.predicate (ir.partPred b j)).body.batchSides d b

/-- **The form of part `j` of batch `b`** in domain `d` at the atom test `atom`. -/
def partFormAt (atom : Expr → Bool) (d b j : ℕ) : Option PartForm :=
  (ir.partSides d b j).bind fun s => ir.partForm atom s.1 s.2

/-- **The instances of part `j`**: the coordinates of its left side. -/
def partLen (d b j : ℕ) : ℕ := ((ir.partSides d b j).map fun s => ir.exprLen s.1).getD 0

/-- **The shape of part `j`.** -/
def partShape (atom : Expr → Bool) (d b j : ℕ) : Shape :=
  ((ir.partFormAt atom d b j).map PartForm.shape).getD default

/-- **The operands of part `j`.** -/
def partOperands (atom : Expr → Bool) (d b j : ℕ) : List BOperand :=
  ((ir.partFormAt atom d b j).map PartForm.operands).getD []

/-- **Batch `b` merges its parts** (`batch.h`, `FieldOperands::relation(gamma)`): it has a merging
challenge. -/
def merged (b : ℕ) : Bool := (ir.batch b).gamma.isSome

/-- **The first operand of part `j` in the batch's operands**: the parts' operands side by side when
the batch merges its parts (`field_batch`'s concatenated operands), `0` otherwise (every part reads
the batch's one operand vector). -/
def partOffset (atom : Expr → Bool) (d b j : ℕ) : ℕ :=
  if ir.merged b then ((List.range j).map fun j' => (ir.partShape atom d b j').k).sum else 0

/-- **The shape of the batch's relation**: its first part's, or, when the batch merges its parts,
the parts' monomials on their operands side by side (`Σ_p γ^p Q_p` at `γ = 1`). -/
def relShape (atom : Expr → Bool) (d b : ℕ) : Shape :=
  if ir.merged b then
    ⟨((List.range (ir.batch b).parts.length).map fun j => (ir.partShape atom d b j).k).sum,
      (List.range (ir.batch b).parts.length).flatMap fun j =>
        (ir.partShape atom d b j).shift (ir.partOffset atom d b j)⟩
  else ir.partShape atom d b 0

/-- **Operand `o` of an instance of part `j`** in the batch's operands: the part's operand
`o − offset` in the part's operands, a constant zero elsewhere. -/
def instOperand (atom : Expr → Bool) (d b j o : ℕ) : BOperand :=
  if ir.partOffset atom d b j ≤ o ∧ o < ir.partOffset atom d b j + (ir.partShape atom d b j).k then
    (ir.partOperands atom d b j).getD (o - ir.partOffset atom d b j) default
  else .zero

/-- **The parts of batch `b` have forms** at the atom test `atom`: its parts are predicates with forms, each a relation of degree at most the batch's
(`Shape.Ok`); without a merging challenge the parts have one shape, with one they have one number of
coordinates. -/
structure PartsOk (atom : Expr → Bool) (d b : ℕ) : Prop where
  /-- It has a part. -/
  pos : 0 < (ir.batch b).parts.length
  /-- Its parts are predicates. -/
  parts : ∀ p ∈ (ir.batch b).parts, p < ir.predicates.length
  /-- Every part has a form. -/
  forms : ∀ j < (ir.batch b).parts.length, (ir.partFormAt atom d b j).isSome
  /-- Every part's shape is a relation of the batch's degree. -/
  ok : ∀ j < (ir.batch b).parts.length, (ir.partShape atom d b j).Ok (ir.batch b).degree
  /-- Without a merging challenge, the parts have one shape. -/
  shapes : ir.merged b = false → ∀ j < (ir.batch b).parts.length,
    ir.partShape atom d b j = ir.partShape atom d b 0
  /-- With a merging challenge, the parts have one number of coordinates. -/
  lens : ir.merged b = true → ∀ j < (ir.batch b).parts.length, ir.partLen d b j = ir.partLen d b 0

/-- **`PartsOk`, decided.** -/
def partsOkB (atom : Expr → Bool) (d b : ℕ) : Bool :=
  decide (0 < (ir.batch b).parts.length) && (ir.batch b).parts.all (· < ir.predicates.length) &&
    (List.range (ir.batch b).parts.length).all (fun j =>
      (ir.partFormAt atom d b j).isSome && (ir.partShape atom d b j).okB (ir.batch b).degree &&
        (ir.merged b || ir.partShape atom d b j == ir.partShape atom d b 0) &&
        (!ir.merged b || ir.partLen d b j == ir.partLen d b 0))

theorem partsOkB_iff (atom : Expr → Bool) (d b : ℕ) :
    ir.partsOkB atom d b = true ↔ ir.PartsOk atom d b := by
  simp only [partsOkB, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    beq_iff_eq, Shape.okB_iff, Bool.not_eq_true', decide_eq_true_eq]
  constructor
  · rintro ⟨⟨h0, hp⟩, h⟩
    exact ⟨h0, fun p hp' => by simpa using hp p hp', fun j hj => (h j hj).1.1.1,
      fun j hj => (h j hj).1.1.2, fun hm j hj => ((h j hj).1.2.resolve_left (by simp [hm])),
      fun hm j hj => ((h j hj).2.resolve_left (by simp [hm]))⟩
  · intro h
    refine ⟨⟨h.pos, fun p hp => by simpa using h.parts p hp⟩,
      fun j hj => ⟨⟨⟨h.forms j hj, h.ok j hj⟩, ?_⟩, ?_⟩⟩
    · cases hm : ir.merged b
      · exact .inr (h.shapes hm j hj)
      · exact .inl rfl
    · cases hm : ir.merged b
      · exact .inl rfl
      · exact .inr (h.lens hm j hj)

variable {ir}

/-- **A part with a form**: its sides and its form. -/
theorem PartsOk.exists_part {atom : Expr → Bool} {d b : ℕ} (hb : ir.PartsOk atom d b)
    (j : Fin (ir.batch b).parts.length) :
    ∃ e e' pf, ir.partSides d b j = some (e, e') ∧ ir.partForm atom e e' = some pf ∧
      ir.partShape atom d b j = pf.shape ∧ ir.partOperands atom d b j = pf.operands := by
  obtain ⟨pf, hpf⟩ := Option.isSome_iff_exists.1 (hb.forms j j.2)
  have hpf' := hpf
  simp only [partFormAt, Option.bind_eq_some_iff] at hpf'
  obtain ⟨⟨e, e'⟩, hs, hf⟩ := hpf'
  exact ⟨e, e', pf, hs, hf, by simp [partShape, hpf], by simp [partOperands, hpf]⟩

/-- The offsets of the parts are the prefix sums of their operand counts, when merged. -/
theorem partOffset_succ {atom : Expr → Bool} {d b : ℕ} (hm : ir.merged b = true) (j : ℕ) :
    ir.partOffset atom d b (j + 1) = ir.partOffset atom d b j + (ir.partShape atom d b j).k := by
  simp [partOffset, hm, List.range_succ, List.sum_append]

/-- The offsets of the parts increase, when merged. -/
theorem partOffset_mono {atom : Expr → Bool} {d b : ℕ} (hm : ir.merged b = true) {a c : ℕ}
    (hac : a ≤ c) : ir.partOffset atom d b a ≤ ir.partOffset atom d b c := by
  induction hac with
  | refl => exact le_rfl
  | step _ ih => rw [partOffset_succ hm]; omega

/-- The slices of two parts are disjoint, when merged. -/
theorem partOffset_disjoint {atom : Expr → Bool} {d b : ℕ} (hm : ir.merged b = true) {p j : ℕ}
    (hpj : p ≠ j) {o : ℕ} (hp : ir.partOffset atom d b p ≤ o)
    (hp' : o < ir.partOffset atom d b p + (ir.partShape atom d b p).k)
    (hj : ir.partOffset atom d b j ≤ o) :
    ir.partOffset atom d b j + (ir.partShape atom d b j).k ≤ o := by
  rcases Nat.lt_or_gt_of_ne hpj with h | h
  · have := partOffset_mono (atom := atom) (d := d) hm (Nat.succ_le_of_lt h)
    rw [partOffset_succ hm] at this
    omega
  · have := partOffset_mono (atom := atom) (d := d) hm (Nat.succ_le_of_lt h)
    rw [partOffset_succ hm] at this
    omega

/-- **The operand count of a merged batch's relation** is the last part's offset. -/
theorem relShape_k_of_merged {atom : Expr → Bool} {d b : ℕ} (hm : ir.merged b = true) :
    (ir.relShape atom d b).k = ir.partOffset atom d b (ir.batch b).parts.length := by
  simp [relShape, partOffset, hm]

/-- **The batch's relation is a relation of the batch's degree** when its parts' shapes are: the
first part's, or the parts' monomials side by side, each in its part's slice. -/
theorem PartsOk.relShape_ok {atom : Expr → Bool} {d b : ℕ} (hb : ir.PartsOk atom d b) :
    (ir.relShape atom d b).Ok (ir.batch b).degree := by
  cases hm : ir.merged b
  · simp only [relShape, hm, Bool.false_eq_true, ↓reduceIte]
    exact hb.ok 0 hb.pos
  · have hmem : ∀ c ∈ (ir.relShape atom d b).monos, ∃ j < (ir.batch b).parts.length,
        ∃ c' ∈ (ir.partShape atom d b j).monos, c = (c'.1, c'.2.map (· + ir.partOffset atom d b j)) := by
      intro c hc
      simp only [relShape, hm, ↓reduceIte, List.mem_flatMap, List.mem_range, Shape.shift,
        List.mem_map] at hc
      obtain ⟨j, hj, c', hc', rfl⟩ := hc
      exact ⟨j, hj, c', hc', rfl⟩
    refine ⟨fun c hc => ?_, fun c hc => ?_, fun c hc o ho => ?_⟩
    · obtain ⟨j, hj, c', hc', rfl⟩ := hmem c hc
      simpa using (hb.ok j hj).ne_nil c' hc'
    · obtain ⟨j, hj, c', hc', rfl⟩ := hmem c hc
      simpa using (hb.ok j hj).length_le c' hc'
    · obtain ⟨j, hj, c', hc', rfl⟩ := hmem c hc
      obtain ⟨o', ho', rfl⟩ := List.mem_map.1 ho
      have h1 := (hb.ok j hj).lt c' hc' o' ho'
      have h2 := partOffset_mono (atom := atom) (d := d) hm (Nat.succ_le_of_lt hj)
      rw [partOffset_succ hm] at h2
      rw [relShape_k_of_merged hm]
      omega

/-- **The batch's relation at an instance of part `j` is the part's shape on its operands**, for
any reading of the operands that reads the constant zero as `0`: the batch's operands at the
instance are the part's in its slice and constant zeros elsewhere, every other part's monomial
reads a constant zero (its factors in its own slice, `Shape.Ok`), and without merging the parts
share the batch's shape. -/
theorem relShape_evalAt_instOperand {atom : Expr → Bool} {d b : ℕ} (hb : ir.PartsOk atom d b)
    {f : ℕ} {I : Interp} (val : BOperand → (I f).K) (hval : val .zero = 0)
    (j : Fin (ir.batch b).parts.length) :
    (ir.relShape atom d b).evalAt (fun o => val (ir.instOperand atom d b j o)) =
      (ir.partShape atom d b j).evalAt (fun o => val ((ir.partOperands atom d b j).getD o default)) := by
  have hself : ∀ o < (ir.partShape atom d b j).k,
      ir.instOperand atom d b j (o + ir.partOffset atom d b j) =
        (ir.partOperands atom d b j).getD o default := fun o ho => by
    rw [instOperand, if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel]
  cases hm : ir.merged b
  · have hoff : ∀ j', ir.partOffset atom d b j' = 0 := fun j' => by simp [partOffset, hm]
    have hsh := hb.shapes hm j j.2
    simp only [relShape, hm, Bool.false_eq_true, ↓reduceIte, ← hsh]
    refine monosEval_congr fun c hc o ho => ?_
    have := hself o ((hb.ok j j.2).lt c hc o ho)
    rw [hoff, Nat.add_zero] at this
    rw [this]
  · simp only [relShape, hm, ↓reduceIte]
    show monosEval _ _ = _
    rw [monosEval_flatMap, sum_map_range_single j.2 fun p hp hpj => ?_, Shape.monosEval_shift]
    · refine monosEval_congr fun c hc o ho => ?_
      rw [hself o ((hb.ok j j.2).lt c hc o ho)]
    · refine monosEval_eq_zero fun c hc => ?_
      obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
      obtain ⟨o, ho⟩ := List.exists_mem_of_ne_nil c'.2 ((hb.ok p hp).ne_nil c' hc')
      refine ⟨o + ir.partOffset atom d b p, List.mem_map.2 ⟨o, ho, rfl⟩, ?_⟩
      have hlt := (hb.ok p hp).lt c' hc' o ho
      rw [instOperand, if_neg, hval]
      rintro ⟨h1, h2⟩
      have := partOffset_disjoint hm hpj (o := o + ir.partOffset atom d b p) (by omega) (by omega) h1
      omega

variable (ir) in
/-- **The slice of part `q` in the batch's operands**: part `q`'s monomials on its operands in the
operand vector of the batch's relation (`relShape`); `Σ_p γ^p Q_p` merges these. -/
def sliceShape (atom : Expr → Bool) (d b q : ℕ) : Shape :=
  ⟨(ir.relShape atom d b).k, (ir.partShape atom d b q).shift (ir.partOffset atom d b q)⟩

theorem sliceShape_evalAt {atom : Expr → Bool} {d b q : ℕ} {f : ℕ} {I : Interp}
    (y : ℕ → (I f).K) :
    (ir.sliceShape atom d b q).evalAt y =
      (ir.partShape atom d b q).evalAt fun o => y (o + ir.partOffset atom d b q) :=
  Shape.monosEval_shift _ _ y

/-- **A part's slice is a relation of the batch's degree** on the batch's operands, when merged. -/
theorem PartsOk.sliceShape_ok {atom : Expr → Bool} {d b : ℕ} (hb : ir.PartsOk atom d b)
    (hm : ir.merged b = true) {q : ℕ} (hq : q < (ir.batch b).parts.length) :
    (ir.sliceShape atom d b q).Ok (ir.batch b).degree := by
  refine ⟨fun c hc => ?_, fun c hc => ?_, fun c hc o ho => ?_⟩
  · obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
    simpa using (hb.ok q hq).ne_nil c' hc'
  · obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
    simpa using (hb.ok q hq).length_le c' hc'
  · obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
    obtain ⟨o', ho', rfl⟩ := List.mem_map.1 ho
    have h1 := (hb.ok q hq).lt c' hc' o' ho'
    have h2 := partOffset_mono (atom := atom) (d := d) hm (Nat.succ_le_of_lt hq)
    rw [partOffset_succ hm] at h2
    change o' + ir.partOffset atom d b q < (ir.relShape atom d b).k
    rw [relShape_k_of_merged hm]
    omega

/-- **The batch's operand in part `q`'s slice** is part `q`'s operand. -/
theorem instOperand_self {atom : Expr → Bool} {d b q o : ℕ} (ho : o < (ir.partShape atom d b q).k) :
    ir.instOperand atom d b q (o + ir.partOffset atom d b q) =
      (ir.partOperands atom d b q).getD o default := by
  rw [instOperand, if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel]

/-- **Another part's operand in part `q`'s slice** is a constant zero, when merged. -/
theorem instOperand_other {atom : Expr → Bool} {d b p q o : ℕ} (hm : ir.merged b = true)
    (hpq : p ≠ q) (ho : o < (ir.partShape atom d b q).k) :
    ir.instOperand atom d b p (o + ir.partOffset atom d b q) = .zero := by
  rw [instOperand, if_neg]
  rintro ⟨h1, h2⟩
  have := partOffset_disjoint hm hpq.symm (o := o + ir.partOffset atom d b q) (by omega) (by omega) h1
  omega

/-- **The parts' operands summed at part `q`'s slice** are part `q`'s, when merged: every other
part reads a constant zero there. -/
theorem sum_instOperand_slice {atom : Expr → Bool} {d b : ℕ} (hm : ir.merged b = true)
    {f : ℕ} {I : Interp} (val : Fin (ir.batch b).parts.length → BOperand → (I f).K)
    (hval : ∀ p, val p .zero = 0) (q : Fin (ir.batch b).parts.length) {o : ℕ}
    (ho : o < (ir.partShape atom d b q).k) :
    ∑ p, val p (ir.instOperand atom d b p (o + ir.partOffset atom d b q)) =
      val q ((ir.partOperands atom d b q).getD o default) := by
  rw [Finset.sum_eq_single q (fun p _ hpq => by
      rw [instOperand_other hm (Fin.val_ne_of_ne hpq) ho, hval]) (by simp),
    instOperand_self ho]

variable (I : Interp)

/-- **The reading of the cells alone** of domain `d`: the reader at the zero statement, the
realized assignment of the committed assignment read from the cells, no challenge and no late
value. A batch operand reads only committed values of phase `0`, pad copies and constants, which
this reading gives as the cells' valuation does (`evalWith_cellValuation_of_atomB`). -/
def cellReader (d : ℕ) (z : ir.Cell d → (I (ir.domainField d)).K) : ir.Valuation I :=
  ir.reader ⟨0, ir.bindAsg (ir.ofCells I d z), fun _ _ => 0, 0⟩

/-- **The value of an operand** at coordinate `i` and a valuation `rd`. -/
def opValAt (d : ℕ) (rd : ir.Valuation I) (o : BOperand) (i : ℕ) : (I (ir.domainField d)).K :=
  o.val (fun a i => ir.evalWith rd d a i) i

/-- **The gradient of a function of the cells**: the differences at the unit vectors, weighted by
the cells, as a linear map. -/
def gradLin {κ : Type} [Fintype κ] [DecidableEq κ] {K : Type} [Field K] (g : (κ → K) → K) :
    (κ → K) →ₗ[K] K :=
  ∑ c, (g (fun j => if c = j then 1 else 0) - g 0) • LinearMap.proj c

theorem gradLin_apply {κ : Type} [Fintype κ] [DecidableEq κ] {K : Type} [Field K]
    {g : (κ → K) → K} (hg : IsAff g) (z : κ → K) : gradLin g z + g 0 = g z := by
  rw [hg.eq_gradient z, add_comm]
  simp only [gradLin, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul,
    mul_comm]

/-- **The batched relation of batch `b` on columns** on the cells of domain `d` (see the module
docstring): the relation of the batch's shape (`relShape`); the instances every coordinate of every
part; operand `o` of coordinate `i` of part `j` the gradient of the operand's value at the cells
(`instOperand`), its offset the value at zero. -/
def batchRelation (d b : ℕ) :
    BatchRelation (ir.Valuation I) (I (ir.domainField d)).K (ir.Cell d) where
  arity := (ir.relShape ir.atomB d b).k
  Q := (ir.relShape ir.atomB d b).evalFin
  Inst := Σ j : Fin (ir.batch b).parts.length, Fin (ir.partLen d b j)
  operand t o := (gradLin fun z => ir.opValAt I d (ir.cellReader I d z)
    (ir.instOperand ir.atomB d b t.1 o) t.2).toAddMonoidHom
  offset _ t o := ir.opValAt I d (ir.cellReader I d 0) (ir.instOperand ir.atomB d b t.1 o) t.2

variable {I}

/-- **A value a batch operand reads is read alike** by the cells' valuation and by the reading of
the cells alone. -/
theorem cellValuation_eq_cellReader {d : ℕ} {x : ir.Valuation I} {r : (ir.layout I).Run}
    {z : ir.Cell d → (I (ir.domainField d)).K} {v : ℕ} (hv : ir.batchLeafOk v = true) :
    ir.cellValuation I d x r z v = ir.cellReader I d z v := by
  funext i
  unfold batchLeafOk at hv
  split at hv
  · rename_i hk
    simp only [cellValuation, cellReader, reader_of_priv _ hk, layoutEnv]
  · rename_i hk
    simp only [cellValuation, cellReader, reader_of_padCopy _ hk, layoutEnv]
  · rename_i es hk
    simp only [cellValuation, cellReader, reader_of_constant _ hk]
  · cases hv

/-- **An atom is read alike** by the cells' valuation and by the reading of the cells alone. -/
theorem evalWith_cellValuation_of_atomB {d : ℕ} {x : ir.Valuation I} {r : (ir.layout I).Run}
    {z : ir.Cell d → (I (ir.domainField d)).K} {a : Expr} (ha : ir.atomB a = true) :
    ir.evalWith (ir.cellValuation I d x r z) d a = ir.evalWith (ir.cellReader I d z) d a := by
  simp only [atomB, Bool.and_eq_true, List.all_eq_true] at ha
  funext i
  exact congrFun (evalE_congr fun v hv => cellValuation_eq_cellReader (ha.1.1 v hv)) i

/-- **The reading of the cells alone is affine, or constant, at every value a batch operand
reads.** -/
theorem leafOk_cellReader {d : ℕ} {v : ℕ} (hv : ir.batchLeafOk v = true) :
    LeafOk ir (f := ir.domainField d) (ir.cellReader I d) ir.cellNd v := by
  unfold batchLeafOk at hv
  split at hv
  · rename_i hk
    refine ⟨fun _ i => ?_, fun h0 => ?_⟩
    · simp only [cellReader, reader_of_priv _ hk,
        ir.bindAsg_val_of_isBound (v := v) _ (by rw [hk]; rfl), ofCells, castElt_dite,
        castElt_castElt]
      exact IsAff.dite _ (fun _ => IsAff.ite _ (isAff_proj _) isAff_zero) fun _ =>
        (isConst_const _).isAff
    · simp [cellNd, isCommitted, hk] at h0
  · rename_i u m hk
    refine ⟨fun _ i => ?_, fun h0 => ?_⟩
    · simp only [cellReader, reader_of_padCopy _ hk,
        ir.bindAsg_val_of_isBound (v := v) _ (by rw [hk]; rfl), ofCells, castElt_dite,
        castElt_castElt]
      exact IsAff.dite _ (fun _ => IsAff.ite _ (isAff_proj _) isAff_zero) fun _ =>
        (isConst_const _).isAff
    · simp [cellNd, isCommitted, hk] at h0
  · rename_i es hk
    have hc : IsConst fun z => ir.cellReader I d z v := fun z z' => by
      funext i
      simp only [cellReader, reader_of_constant _ hk]
    exact ⟨fun _ i => (hc.comp fun g => (castElt (g i) : (I (ir.domainField d)).K)).isAff,
      fun _ => hc⟩
  · cases hv

/-- **An atom is affine in the cells.** -/
theorem isAff_atom {d : ℕ} {a : Expr} (ha : ir.atomB a = true) (i : ℕ) :
    IsAff fun z => ir.evalWith (ir.cellReader I d z) d a i := by
  simp only [atomB, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at ha
  exact evalE_isAff (fun v hv => leafOk_cellReader (ha.1.1 v hv)) ha.1.2 ha.2 i

/-- **An operand of atoms is affine in the cells.** -/
theorem isAff_opValAt {d : ℕ} {o : BOperand}
    (ho : (∃ a, o = .atom a ∧ ir.atomB a = true) ∨
      (∃ ts, o = .lin ts ∧ ∀ t ∈ ts, ir.atomB t.2 = true) ∨ o = .zero) (i : ℕ) :
    IsAff fun z => ir.opValAt I d (ir.cellReader I d z) o i := by
  rcases ho with ⟨a, rfl, ha⟩ | ⟨ts, rfl, hts⟩ | rfl
  · exact isAff_atom ha i
  · exact IsAff.list_sum ts fun t ht => IsAff.const_mul (isConst_const _) (isAff_atom (hts t ht) i)
  · exact (isConst_const _).isAff

/-- **An operand of atoms is read alike** by the cells' valuation and by the reading of the cells
alone. -/
theorem opValAt_cellValuation {d : ℕ} {x : ir.Valuation I} {r : (ir.layout I).Run}
    {z : ir.Cell d → (I (ir.domainField d)).K} {o : BOperand}
    (ho : (∃ a, o = .atom a ∧ ir.atomB a = true) ∨
      (∃ ts, o = .lin ts ∧ ∀ t ∈ ts, ir.atomB t.2 = true) ∨ o = .zero) (i : ℕ) :
    ir.opValAt I d (ir.cellValuation I d x r z) o i = ir.opValAt I d (ir.cellReader I d z) o i := by
  rcases ho with ⟨a, rfl, ha⟩ | ⟨ts, rfl, hts⟩ | rfl
  · simp only [opValAt, BOperand.val, evalWith_cellValuation_of_atomB ha]
  · simp only [opValAt, BOperand.val]
    exact sum_map_congr fun t ht => by rw [evalWith_cellValuation_of_atomB (hts t ht)]
  · rfl

/-- **The batch's operands beyond its relation's are constant zeros.** -/
theorem instOperand_of_le {atom : Expr → Bool} {d b : ℕ} (j : Fin (ir.batch b).parts.length)
    (hb : ir.PartsOk atom d b) {o : ℕ} (ho : (ir.relShape atom d b).k ≤ o) :
    ir.instOperand atom d b j o = .zero := by
  rw [instOperand, if_neg]
  rintro ⟨-, h2⟩
  cases hm : ir.merged b
  · have hoff : ir.partOffset atom d b j = 0 := by simp [partOffset, hm]
    simp only [relShape, hm, Bool.false_eq_true, ↓reduceIte, ← hb.shapes hm j j.2] at ho
    omega
  · have h1 := partOffset_mono (atom := atom) (d := d) hm (Nat.succ_le_of_lt j.2)
    rw [partOffset_succ hm] at h1
    rw [relShape_k_of_merged hm] at ho
    omega

/-- **Every operand of an instance reads atoms only**: an operand of its part's form, or a
constant zero. -/
theorem instOperand_atoms {atom : Expr → Bool} {d b : ℕ} {j : Fin (ir.batch b).parts.length}
    {e e' : Expr} {pf : PartForm} (hpf : ir.partForm atom e e' = some pf)
    (hops : ir.partOperands atom d b j = pf.operands) (hk : (ir.partShape atom d b j).k = pf.operands.length)
    (o : ℕ) : (∃ a, ir.instOperand atom d b j o = .atom a ∧ atom a = true) ∨
      (∃ ts, ir.instOperand atom d b j o = .lin ts ∧ ∀ t ∈ ts, atom t.2 = true) ∨
        ir.instOperand atom d b j o = .zero := by
  unfold instOperand
  split_ifs with h
  · rw [hops]
    exact operand_atoms hpf (by
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact List.getElem_mem _)
  · exact .inr (.inr rfl)

/-- **The relation on the batch's operands at a reading that reads the constant zero as `0`** is
the shape's value at the reading (`instOperand_of_le`). -/
theorem evalFin_instOperand {atom : Expr → Bool} {d b : ℕ} (hb : ir.PartsOk atom d b) {f : ℕ}
    {I : Interp} (val : BOperand → (I f).K) (hval : val .zero = 0)
    (j : Fin (ir.batch b).parts.length) :
    (ir.relShape atom d b).evalFin (fun o => val (ir.instOperand atom d b j o)) =
      (ir.relShape atom d b).evalAt (fun o => val (ir.instOperand atom d b j o)) := by
  unfold Shape.evalFin
  congr 1
  funext o
  split_ifs with ho
  · rfl
  · rw [instOperand_of_le j hb (not_lt.1 ho), hval]

/-- **The batched relation at an instance of part `j` is the part's shape** on the part's operands
read from the cells alone: the operands' values are their gradients plus their offsets (an operand
of atoms is affine, `isAff_opValAt`), and the batch's relation on the instance's operands is the
part's (`relShape_evalAt_instOperand`). -/
theorem batchRelation_Q {d b : ℕ} (hb : ir.PartsOk ir.atomB d b)
    (j : Fin (ir.batch b).parts.length) (x : ir.Valuation I)
    (a : ir.Cell d → (I (ir.domainField d)).K) (i : Fin (ir.partLen d b j)) :
    (ir.batchRelation I d b).Q (fun o => (ir.batchRelation I d b).operand ⟨j, i⟩ o a +
        (ir.batchRelation I d b).offset x ⟨j, i⟩ o) =
      (ir.partShape ir.atomB d b j).evalAt
        (fun o => ir.opValAt I d (ir.cellReader I d a) ((ir.partOperands ir.atomB d b j).getD o default) i) := by
  obtain ⟨e, e', pf, -, hpf, hsh, hops⟩ := hb.exists_part j
  have hk : (ir.partShape ir.atomB d b j).k = pf.operands.length := by rw [hsh]; rfl
  have hval : (fun o : Fin (ir.batchRelation I d b).arity =>
      (ir.batchRelation I d b).operand ⟨j, i⟩ o a + (ir.batchRelation I d b).offset x ⟨j, i⟩ o) =
        fun o : Fin (ir.batchRelation I d b).arity =>
          ir.opValAt I d (ir.cellReader I d a) (ir.instOperand ir.atomB d b j o) i := by
    funext o
    exact gradLin_apply (isAff_opValAt (instOperand_atoms hpf hops hk o) i) a
  rw [hval]
  exact (evalFin_instOperand hb (fun op => ir.opValAt I d (ir.cellReader I d a) op i) rfl j).trans
    (relShape_evalAt_instOperand hb (fun op => ir.opValAt I d (ir.cellReader I d a) op i) rfl j)

/-- **A leaf of a zero constant reads `0`** at a valuation reading every constant by decoding its
entries (`reader_of_constant`), when the program's fields decode `0` to `0`. -/
theorem eval_zeroLeaf (hz : ir.ZeroDecodes I) {rd : ir.Valuation I}
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0))
    {f : ℕ} {ref : ℕ → ℕ → (I f).K} {rl : ℕ → ℕ} {a : Expr} (ha : ir.zeroLeafB a = true) (i : ℕ) :
    Expr.eval ir f rd ref rl a i = 0 := by
  cases a with
  | leaf v =>
    simp only [zeroLeafB, Bool.and_eq_true, decide_eq_true_eq] at ha
    obtain ⟨hf, ha⟩ := ha
    split at ha
    · rename_i es hk
      have h0 : es.getD i 0 = 0 := by
        rw [List.getD_eq_getElem?_getD]
        cases hg : es[i]? with
        | none => rfl
        | some c =>
          simpa using List.all_eq_true.1 ha c (List.mem_of_getElem? hg)
      simp only [Expr.eval, hK v es hk i, h0, hz _ hf, castElt_zero]
    · cases ha
  | _ => simp [zeroLeafB] at ha

/-- **The leaves of zero constants read `0` at the cells' valuation.** -/
theorem eval_cellValuation_zeroLeaf (hz : ir.ZeroDecodes I) {d : ℕ} {x : ir.Valuation I}
    {r : (ir.layout I).Run} {z : ir.Cell d → (I (ir.domainField d)).K} {f : ℕ}
    {ref : ℕ → ℕ → (I f).K} {rl : ℕ → ℕ} {a : Expr} (ha : ir.zeroLeafB a = true) (i : ℕ) :
    Expr.eval ir f (ir.cellValuation I d x r z) ref rl a i = 0 :=
  eval_zeroLeaf hz (fun _ _ hk i => reader_of_constant _ hk i) ha i

/-- **The batched relation at an instance of part `j` is the part's shape** on the part's operands
at the cells' valuation (`batchRelation_Q`, `opValAt_cellValuation`). -/
theorem batchRelation_Q_cellValuation {d b : ℕ} (hb : ir.PartsOk ir.atomB d b)
    (j : Fin (ir.batch b).parts.length) {e e' : Expr} {pf : PartForm}
    (hs : ir.partSides d b j = some (e, e')) (hpf : ir.partForm ir.atomB e e' = some pf)
    (x : ir.Valuation I) (r : (ir.layout I).Run) (a : ir.Cell d → (I (ir.domainField d)).K)
    (i : Fin (ir.partLen d b j)) :
    (ir.batchRelation I d b).Q (fun o => (ir.batchRelation I d b).operand ⟨j, i⟩ o a +
        (ir.batchRelation I d b).offset x ⟨j, i⟩ o) =
      pf.shape.evalAt
        (fun o => ir.opValAt I d (ir.cellValuation I d x r a) (pf.operands.getD o default) i) := by
  have hsh : ir.partShape ir.atomB d b j = pf.shape := by
    simp [partShape, partFormAt, hs, hpf]
  have hops : ir.partOperands ir.atomB d b j = pf.operands := by
    simp [partOperands, partFormAt, hs, hpf]
  have hok := hb.ok j j.2
  rw [hsh] at hok
  rw [batchRelation_Q hb j x a i, hsh, hops]
  refine monosEval_congr fun c hc o ho => (opValAt_cellValuation (operand_atoms hpf ?_) i).symm
  rw [List.getD_eq_getElem _ _ (hok.lt c hc o ho)]
  exact List.getElem_mem _

/-- **An instance of the batched relation is its part's field equation**: at coordinate `i` of
part `j`, the relation on the operands plus their offsets is `e − e'` at the cells' valuation, when
the program's fields decode `0` to `0` (`hz`, a property of the model). -/
theorem batchRelation_instance (hz : ir.ZeroDecodes I) {d b : ℕ} (hb : ir.PartsOk ir.atomB d b)
    (j : Fin (ir.batch b).parts.length) {e e' : Expr} {pf : PartForm}
    (hs : ir.partSides d b j = some (e, e')) (hpf : ir.partForm ir.atomB e e' = some pf)
    (x : ir.Valuation I) (r : (ir.layout I).Run) (a : ir.Cell d → (I (ir.domainField d)).K)
    (i : Fin (ir.partLen d b j)) :
    (ir.batchRelation I d b).Q (fun o => (ir.batchRelation I d b).operand ⟨j, i⟩ o a +
        (ir.batchRelation I d b).offset x ⟨j, i⟩ o) =
      ir.evalWith (ir.cellValuation I d x r a) d e i -
        ir.evalWith (ir.cellValuation I d x r a) d e' i := by
  rw [batchRelation_Q_cellValuation hb j hs hpf x r a i]
  exact (partForm_eval (leaf := ir.cellValuation I d x r a)
    (ref := ir.refVal (ir.cellValuation I d x r a) ir.exprs.length (ir.domainField d))
    (rl := ir.refLen ir.exprs.length) (fun _ ha i => eval_cellValuation_zeroLeaf hz ha i) hpf i).symm

/-- **The batched relation reads the cells through their valuation**: at cells of one valuation, it
holds at both or at neither. -/
theorem batchRelation_holds_congr {d b : ℕ} (hb : ir.PartsOk ir.atomB d b) {x : ir.Valuation I}
    {r r' : (ir.layout I).Run} {a a' : ir.Cell d → (I (ir.domainField d)).K}
    (h : ir.cellValuation I d x r a = ir.cellValuation I d x r' a') :
    (ir.batchRelation I d b).Holds x a ↔ (ir.batchRelation I d b).Holds x a' := by
  refine forall_congr' fun t => ?_
  obtain ⟨j, i⟩ := t
  obtain ⟨e, e', pf, hs, hpf, -, -⟩ := hb.exists_part j
  rw [batchRelation_Q_cellValuation hb j hs hpf x r a i,
    batchRelation_Q_cellValuation hb j hs hpf x r' a' i, h]

/-- **The batched relation holds exactly when every part placed holds** at the cells' valuation
(`PlacedHolds`: a field `equal` itself, a `mod_0` its field equation), when the parts have forms:
at each part's coordinate, the operands' values are their gradients plus their offsets (an operand
of atoms is affine, `isAff_opValAt`), and the batch's relation on them is the part's field equation
(`relShape_evalAt_instOperand`, `partForm_eval`, the program's fields decoding `0` to `0`). -/
theorem batchRelation_holds_iff (hz : ir.ZeroDecodes I) {d b : ℕ} (hb : ir.PartsOk ir.atomB d b)
    (x : ir.Valuation I)
    (r : (ir.layout I).Run) (a : ir.Cell d → (I (ir.domainField d)).K) :
    (ir.batchRelation I d b).Holds x a ↔
      ∀ p ∈ (ir.batch b).parts, ir.PlacedHolds (ir.cellValuation I d x r a) (ir.predicate p).body := by
  have hpred : ∀ n (hn : n < (ir.batch b).parts.length), ir.partPred b n = (ir.batch b).parts[n] :=
    fun n hn => List.getD_eq_getElem _ _ hn
  constructor
  · intro h p hp
    obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.1 hp
    obtain ⟨e, e', pf, hs, hpf, -, -⟩ := hb.exists_part ⟨n, hn⟩
    have hs' := hs
    simp only [partSides, hpred n hn] at hs'
    rw [placedHolds_iff_of_batchSides hs']
    intro i hi
    have hlen : ir.partLen d b n = ir.exprLen e := by simp [partLen, hs]
    have := h ⟨⟨n, hn⟩, ⟨i, by rw [hlen]; exact hi⟩⟩
    rw [batchRelation_instance hz hb ⟨n, hn⟩ hs hpf x r a] at this
    exact sub_eq_zero.1 this
  · rintro h ⟨j, i⟩
    obtain ⟨e, e', pf, hs, hpf, -, -⟩ := hb.exists_part j
    rw [batchRelation_instance hz hb j hs hpf x r a, sub_eq_zero]
    have hs' := hs
    simp only [partSides, hpred j j.2] at hs'
    have hlen : ir.partLen d b j = ir.exprLen e := by simp [partLen, hs]
    exact (placedHolds_iff_of_batchSides hs' _).1 (h _ (List.getElem_mem _)) i (hlen ▸ i.2)

end

end GordieHowe.RealizedProgram
