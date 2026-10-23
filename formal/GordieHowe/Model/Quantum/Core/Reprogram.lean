-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Core.Constructions
public import GordieHowe.Model.Quantum.Core.Circuit
public import GordieHowe.Model.QROM.NIZK

@[expose] public section

/-!
# The reprogrammed query as a sub-circuit of the core

A reprogrammed oracle answers the inputs of an assignment list `ass` by the list and the other
inputs by `H` (`Function.reprogram`; Unruh 2017, ePrint 2017/398, section 2, p. 7: "We call a list
ass = (x1 := y1, . . . , xn := yn) an assignment-list. We then write H(ass) for
H(x1 := y1)(x2 := y2) . . . (xn := yn)"). Unruh 2017 (p. 12) uses the unitary `U^{oracle,H,ℓ}`
that queries `H(ass)` with the assignment list held in a register `T`:
`|x⟩_X ⊗ |ass⟩_T ⊗ |y'⟩_Y ↦ |x⟩_X ⊗ |ass⟩_T ⊗ |y' ⊕ H(ass)(x)⟩_Y`. With the assignment list a
function `ass s` of the work register, this is `permOp (queryPermOf fun s => H.reprogram (ass s))`.

In the model (`GordieHowe/Model/Quantum/Core/Model.lean`) the only oracle is `H`, so a reprogrammed query is a
sub-circuit of the core: Kraus maps and one query to `H`. This file defines it and proves that
it acts as Unruh's controlled query (`reprogQuery_eq_controlled`).

## The sub-circuit (`reprogSwap`, `reprogAdd`)

The work register is `V` with an ancilla `(a, b, f) : X × Y × Bool`, clean when it holds a fixed
input `x₀`, the uniform superposition of answers, and the flag `false` (`reprogAnc x₀`). On a
basis state with query pair `(x, y)`:

1. `reprogSwap`: if `x` is assigned in `ass v`, exchange the query pair with the ancilla's pair
   and set the flag;
2. the query to `H`. On the branches where `x` is assigned, the query register holds `x₀` and
   the uniform superposition of answers, which `U_H` fixes: `|x₀⟩ ⊗ ∑_y |y⟩ ↦ |x₀⟩ ⊗ ∑_y |y + H x₀⟩`;
3. `reprogSwap` again, which exchanges the pairs back and clears the flag;
4. `reprogAdd`: add the last assignment to `x` in `ass v` (`lastAssign`), if any, to `y`.

On an assigned input the answer register ends as `y + lastAssign (ass v) x`, on the others as
`y + H x`; that is `y + H.reprogram (ass v) x` (`reprogram_apply_eq_lastAssign`), and the
ancilla is clean again. The sub-circuit makes one query. `reprogSwap` is a basis permutation
(an involution), so steps 1 and 3–4 are unitary Kraus maps.

This is the one-query form, with the uniform superposition in a clean ancilla. The circuit
depends on the assignment list and the work register only, never on `H`.
-/

open Finset Matrix
open scoped BigOperators Kronecker

namespace GordieHowe.Quantum


section LastAssign

variable {X Y : Type*} [DecidableEq X]

/-- The value of the last assignment to `x` in an assignment list, if any. -/
def lastAssign (ass : List (Assignment X Y)) (x : X) : Option Y :=
  ass.foldl (fun o a => if a.input = x then some a.output else o) none

theorem lastAssign_append_singleton (ass : List (Assignment X Y)) (a : Assignment X Y) (x : X) :
    lastAssign (ass ++ [a]) x = if a.input = x then some a.output else lastAssign ass x := by
  simp [lastAssign, List.foldl_append]

/-- **A reprogrammed oracle reads the last assignment**, or `H` on an input without one. -/
theorem reprogram_apply_eq_lastAssign (H : X → Y) (ass : List (Assignment X Y)) (x : X) :
    H.reprogram ass x = (lastAssign ass x).getD (H x) := by
  induction ass using List.reverseRecOn with
  | nil => rfl
  | append_singleton l a ih =>
    rw [lastAssign_append_singleton]
    simp only [Function.reprogram, List.foldl_append, List.foldl_cons, List.foldl_nil] at ih ⊢
    by_cases hx : a.input = x
    · subst hx
      simp
    · rw [Function.update_of_ne (Ne.symm hx), ih, ite_eq_right_iff.2 fun h => absurd h hx]

/-- Mapping the outputs of an assignment list maps its last assignment. -/
theorem lastAssign_map {Z : Type*} (f : Y → Z) (ass : List (Assignment X Y)) (x : X) :
    lastAssign (ass.map (Assignment.mapOutput f)) x = (lastAssign ass x).map f := by
  induction ass using List.reverseRecOn with
  | nil => rfl
  | append_singleton l a ih =>
    rw [List.map_append, List.map_singleton, lastAssign_append_singleton,
      lastAssign_append_singleton, ih]
    by_cases h : a.input = x <;> simp [h, Assignment.mapOutput]

/-- An input with a last assignment is assigned somewhere in the list. -/
theorem exists_mem_of_lastAssign_eq_some {ass : List (Assignment X Y)} {x : X} {y : Y}
    (h : lastAssign ass x = some y) : ∃ a ∈ ass, a.input = x := by
  induction ass using List.reverseRecOn with
  | nil => simp [lastAssign] at h
  | append_singleton l a ih =>
    rw [lastAssign_append_singleton] at h
    split_ifs at h with ha
    · exact ⟨a, by simp, ha⟩
    · obtain ⟨b, hb, hb'⟩ := ih h
      exact ⟨b, by simp [hb], hb'⟩

/-- An input assigned nowhere in the list has no last assignment. -/
theorem lastAssign_eq_none {ass : List (Assignment X Y)} {x : X}
    (h : ∀ a ∈ ass, a.input ≠ x) : lastAssign ass x = none := by
  rcases hl : lastAssign ass x with _ | y
  · rfl
  · obtain ⟨a, ha, rfl⟩ := exists_mem_of_lastAssign_eq_some hl
    exact absurd rfl (h a ha)

end LastAssign

/-! ### Registers and the sub-circuit -/

/-- The basis of the reprogrammed query: the work register `V`, an ancilla `X × Y × Bool`, and
one query pair. -/
abbrev ReprogrammedQueryReg (V X Y : Type*) := QueryReg (V × (X × Y × Bool)) 1 X Y

section Circuit

variable {V X Y : Type*} [DecidableEq X] (ass : V → List (Assignment X Y))

/-- Whether the sub-circuit exchanges the pairs at a basis state: with the flag clear, when the
query input is assigned; with the flag set, when the ancilla's input is assigned. -/
def reprogCond (p : ReprogrammedQueryReg V X Y) : Prop :=
  if p.1.2.2.2 then (lastAssign (ass p.1.1) p.1.2.1).isSome else
    (lastAssign (ass p.1.1) (p.2 0).1).isSome

instance : DecidablePred (reprogCond ass) := fun p => by
  unfold reprogCond
  infer_instance

/-- Exchange the query pair with the ancilla's pair and flip the flag. -/
def swapFlip (p : ReprogrammedQueryReg V X Y) : ReprogrammedQueryReg V X Y :=
  ((p.1.1, ((p.2 0).1, (p.2 0).2, !p.1.2.2.2)), fun _ => (p.1.2.1, p.1.2.2.1))

omit [DecidableEq X] in
theorem swapFlip_swapFlip (p : ReprogrammedQueryReg V X Y) : swapFlip (swapFlip p) = p := by
  obtain ⟨⟨v, a, y, f⟩, e⟩ := p
  refine Prod.ext (by simp [swapFlip]) (funext fun i => ?_)
  simp [swapFlip, Fin.fin_one_eq_zero i]

theorem reprogCond_swapFlip (p : ReprogrammedQueryReg V X Y) :
    reprogCond ass (swapFlip p) ↔ reprogCond ass p := by
  obtain ⟨⟨v, a, y, f⟩, e⟩ := p
  cases f <;> simp [reprogCond, swapFlip]

/-- **Steps 1 and 3 of the sub-circuit**: `swapFlip` where `reprogCond` holds; an involution. -/
def reprogSwap : Equiv.Perm (ReprogrammedQueryReg V X Y) :=
  Function.Involutive.toPerm (fun p => if reprogCond ass p then swapFlip p else p) fun p => by
    by_cases h : reprogCond ass p
    · simp [h, (reprogCond_swapFlip ass p).2 h, swapFlip_swapFlip]
    · simp [h]

theorem reprogSwap_apply (p : ReprogrammedQueryReg V X Y) :
    reprogSwap ass p = if reprogCond ass p then swapFlip p else p :=
  rfl

theorem reprogSwap_symm : (reprogSwap ass).symm = reprogSwap ass :=
  Function.Involutive.toPerm_symm _

variable [AddGroup Y]

/-- **Step 4 of the sub-circuit**: add the last assignment to the query input, if any, to the
answer register. -/
def reprogAdd : Equiv.Perm (ReprogrammedQueryReg V X Y) :=
  queryPermOf fun s x => (lastAssign (ass s.1) x).getD 0

/-- **The reprogrammed query** with oracle `H`: the basis permutations of the sub-circuit in
order, `reprogSwap`, the query `queryPerm H`, `reprogSwap`, `reprogAdd`. -/
def reprogPerm (H : X → Y) : Equiv.Perm (ReprogrammedQueryReg V X Y) :=
  (((reprogSwap ass).trans (queryPerm H)).trans (reprogSwap ass)).trans (reprogAdd ass)

end Circuit

/-! ### The clean ancilla -/

section Anc

variable {V X Y : Type*} [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y]

/-- The weight of an ancilla basis state in the clean ancilla, up to the factor `1/√|Y|`: `1` at
input `x₀` and flag `false`, else `0`. -/
def ancWeight (x₀ : X) (a : X × Y × Bool) : ℂ :=
  if a.1 = x₀ ∧ a.2.2 = false then 1 else 0

/-- **The clean ancilla** `|x₀⟩⟨x₀| ⊗ |u⟩⟨u| ⊗ |false⟩⟨false|`, with `u` the uniform
superposition of answers: entries `ancWeight x₀ a * ancWeight x₀ a' / |Y|`. -/
noncomputable def reprogAnc (x₀ : X) : Matrix (X × Y × Bool) (X × Y × Bool) ℂ :=
  fun a a' => ancWeight x₀ a * ancWeight x₀ a' / Fintype.card Y

/-- A state of `QueryReg V 1 X Y` with the clean ancilla appended in the work register. -/
noncomputable def withAnc (x₀ : X) (ρ : Matrix (QueryReg V 1 X Y) (QueryReg V 1 X Y) ℂ) :
    Matrix (ReprogrammedQueryReg V X Y) (ReprogrammedQueryReg V X Y) ℂ :=
  fun p p' => ρ (p.1.1, p.2) (p'.1.1, p'.2) * reprogAnc x₀ p.1.2 p'.1.2

end Anc

/-! ### The sub-circuit is the controlled query -/

section Eq

variable {V X Y : Type*} [DecidableEq X] [AddGroup Y] (ass : V → List (Assignment X Y)) (H : X → Y)

/-- The inverse of the sub-circuit keeps the ancilla's input. -/
theorem reprogPerm_symm_anc_fst (p : ReprogrammedQueryReg V X Y) :
    ((reprogPerm ass H).symm p).1.2.1 = p.1.2.1 := by
  obtain ⟨⟨v, a, y, f⟩, e⟩ := p
  cases f <;>
  · simp only [reprogPerm, Equiv.symm_trans_apply, reprogSwap_symm, reprogSwap_apply, reprogAdd,
      queryPermOf, queryPerm, reprogCond, swapFlip]
    split_ifs <;> simp_all

/-- The inverse of the sub-circuit keeps the flag. -/
theorem reprogPerm_symm_flag (p : ReprogrammedQueryReg V X Y) :
    ((reprogPerm ass H).symm p).1.2.2.2 = p.1.2.2.2 := by
  obtain ⟨⟨v, a, y, f⟩, e⟩ := p
  cases f <;>
  · simp only [reprogPerm, Equiv.symm_trans_apply, reprogSwap_symm, reprogSwap_apply, reprogAdd,
      queryPermOf, queryPerm, reprogCond, swapFlip]
    split_ifs <;> simp_all

/-- With the flag clear, the inverse of the sub-circuit acts on the work register and the query
pair as the inverse of the controlled query `queryPermOf fun s => H.reprogram (ass s)`. -/
theorem reprogPerm_symm_sys (p : ReprogrammedQueryReg V X Y) (hf : p.1.2.2.2 = false) :
    (((reprogPerm ass H).symm p).1.1, ((reprogPerm ass H).symm p).2) =
      (queryPermOf (n := 1) fun s => H.reprogram (ass s)).symm (p.1.1, p.2) := by
  obtain ⟨⟨v, a, b, f⟩, e⟩ := p
  simp only at hf
  subst hf
  rcases hL : lastAssign (ass v) (e 0).1 with _ | L
  · simp [reprogPerm, reprogSwap_symm, reprogSwap_apply, reprogAdd, queryPermOf_symm_apply,
      queryPerm_symm_apply, reprogCond, hL, reprogram_apply_eq_lastAssign]
    funext j
    rw [Fin.fin_one_eq_zero j]
    simp [hL]
  · simp [reprogPerm, reprogSwap_symm, reprogSwap_apply, reprogAdd, queryPermOf_symm_apply,
      queryPerm_symm_apply, reprogCond, swapFlip, hL, reprogram_apply_eq_lastAssign]
    funext j
    rw [Fin.fin_one_eq_zero j]
    simp [hL]

end Eq

section EqMat

variable {V X Y : Type*} [DecidableEq X] [Fintype Y] [AddGroup Y] (ass : V → List (Assignment X Y)) (H : X → Y)

/-- **The reprogrammed query is Unruh's controlled query** (Unruh 2017 p. 12, `U^{oracle,H,ℓ}`):
on a state with the clean ancilla, the sub-circuit `reprogPerm` (one query to `H`) acts as the
query to `H.reprogram (ass s)` controlled by the work register `s`, and leaves the ancilla
clean. -/
theorem reprogQuery_eq_controlled (x₀ : X)
    (ρ : Matrix (QueryReg V 1 X Y) (QueryReg V 1 X Y) ℂ) :
    (withAnc x₀ ρ).submatrix (reprogPerm ass H).symm (reprogPerm ass H).symm =
      withAnc x₀ (ρ.submatrix (queryPermOf fun s => H.reprogram (ass s)).symm
        (queryPermOf fun s => H.reprogram (ass s)).symm) := by
  ext p p'
  simp only [submatrix_apply, withAnc, reprogAnc, ancWeight]
  rw [reprogPerm_symm_anc_fst, reprogPerm_symm_flag, reprogPerm_symm_anc_fst,
    reprogPerm_symm_flag]
  by_cases hp : p.1.2.2.2 = false
  · by_cases hp' : p'.1.2.2.2 = false
    · rw [reprogPerm_symm_sys ass H p hp, reprogPerm_symm_sys ass H p' hp']
    · simp [hp']
  · simp [hp]

end EqMat

/-! ### Circuits with reprogrammed queries -/

/-- A basis permutation as a Kraus map with one operator. -/
def KrausMap.ofPerm {ι : Type*} [Fintype ι] [DecidableEq ι] (π : Equiv.Perm ι) :
    KrausMap Unit ι ι :=
  (KrausMap.identity ι).permConj (Equiv.refl ι) π

theorem KrausMap.ofPerm_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (π : Equiv.Perm ι)
    (ρ : Matrix ι ι ℂ) : (KrausMap.ofPerm π) ρ = ρ.submatrix π.symm π.symm := by
  rw [ofPerm, permConj_apply, id_apply]
  simp

/-- **A basis permutation is trace preserving.** -/
theorem KrausMap.tp_ofPerm {ι : Type*} [Fintype ι] [DecidableEq ι] (π : Equiv.Perm ι) :
    ∑ r, ((KrausMap.ofPerm π).op r)ᴴ * (KrausMap.ofPerm π).op r = 1 := by
  simp only [KrausMap.ofPerm, KrausMap.permConj, KrausMap.identity, Fintype.univ_punit,
    Finset.sum_singleton]
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.conjTranspose_one,
    Matrix.one_mul, Matrix.submatrix_one_equiv]

section RCirc

variable {V X Y : Type} [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y]

/-- The basis of the reprogrammed query with the ancilla moved to the end. -/
def ancSplit (V X Y : Type) : ReprogrammedQueryReg V X Y ≃ QueryReg V 1 X Y × (X × Y × Bool) where
  toFun p := ((p.1.1, p.2), p.1.2)
  invFun q := ((q.1.1, q.2), q.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem withAnc_eq_kronecker (x₀ : X) (ρ : Matrix (QueryReg V 1 X Y) (QueryReg V 1 X Y) ℂ) :
    withAnc x₀ ρ = (ρ ⊗ₖ reprogAnc x₀).submatrix (ancSplit V X Y) (ancSplit V X Y) :=
  rfl

/-- A Kraus map on the system, the identity on the ancilla. -/
def KrausMap.liftAnc {R : Type*} [Fintype R]
    (K : KrausMap R (QueryReg V 1 X Y) (QueryReg V 1 X Y)) : KrausMap R (ReprogrammedQueryReg V X Y) (ReprogrammedQueryReg V X Y) :=
  (K.tensorId (X × Y × Bool)).reindex (ancSplit V X Y).symm

theorem KrausMap.liftAnc_apply_withAnc {R : Type*} [Fintype R]
    (K : KrausMap R (QueryReg V 1 X Y) (QueryReg V 1 X Y)) (x₀ : X)
    (ρ : Matrix (QueryReg V 1 X Y) (QueryReg V 1 X Y) ℂ) :
    K.liftAnc (withAnc x₀ ρ) = withAnc x₀ (K ρ) := by
  rw [KrausMap.liftAnc, KrausMap.reindex_apply, withAnc_eq_kronecker, submatrix_submatrix]
  simp only [Equiv.symm_symm, Equiv.self_comp_symm, submatrix_id_id]
  rw [KrausMap.tensorId_apply, withAnc_eq_kronecker]

/-- **A circuit of the core with reprogrammed queries** on `QueryReg V 1 X Y`: Kraus maps and
queries to `H.reprogram (ass s)`, controlled by the work register `s`. It compiles into a circuit
of the core (`Quantum.ReprogrammedCircuit.toCircuit`) in which each reprogrammed query is the one-query sub-circuit of
`reprogPerm`, on the work register with the ancilla of `ReprogrammedQueryReg`. -/
inductive ReprogrammedCircuit (V X Y : Type) [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X] [Fintype Y]
    [DecidableEq Y] : Type 1 where
  /-- The empty circuit. -/
  | nil : ReprogrammedCircuit V X Y
  /-- A Kraus map, then the rest. -/
  | kraus {R : Type} [Fintype R] (K : KrausMap R (QueryReg V 1 X Y) (QueryReg V 1 X Y))
      (c : ReprogrammedCircuit V X Y) : ReprogrammedCircuit V X Y
  /-- A query to `H.reprogram (ass s)`, then the rest. -/
  | rquery (ass : V → List (Assignment X Y)) (c : ReprogrammedCircuit V X Y) : ReprogrammedCircuit V X Y

namespace ReprogrammedCircuit

/-- The number of reprogrammed queries. -/
def queries : ReprogrammedCircuit V X Y → ℕ
  | nil => 0
  | kraus _ c => queries c
  | rquery _ c => queries c + 1

/-- Concatenation. -/
def append : ReprogrammedCircuit V X Y → ReprogrammedCircuit V X Y → ReprogrammedCircuit V X Y
  | nil, d => d
  | kraus K c, d => kraus K (append c d)
  | rquery a c, d => rquery a (append c d)

instance : Append (ReprogrammedCircuit V X Y) :=
  ⟨append⟩

@[simp] theorem nil_append (d : ReprogrammedCircuit V X Y) : (nil : ReprogrammedCircuit V X Y) ++ d = d := rfl
@[simp] theorem kraus_append {R : Type} [Fintype R]
    (K : KrausMap R (QueryReg V 1 X Y) (QueryReg V 1 X Y)) (c d : ReprogrammedCircuit V X Y) :
    kraus K c ++ d = kraus K (c ++ d) := rfl
@[simp] theorem rquery_append (a : V → List (Assignment X Y)) (c d : ReprogrammedCircuit V X Y) :
    rquery a c ++ d = rquery a (c ++ d) := rfl

theorem queries_append (c d : ReprogrammedCircuit V X Y) : (c ++ d).queries = c.queries + d.queries := by
  induction c with
  | nil => simp [queries]
  | kraus K c ih => simpa [queries] using ih
  | rquery a c ih =>
    simp only [rquery_append, queries, ih]
    omega

variable [AddGroup Y]

/-- **The run with the reprogrammed queries as controlled queries** (Unruh 2017 p. 12): each
`rquery ass` is `UρU*` for `U = permOp (queryPermOf fun s => H.reprogram (ass s))`. -/
def run (H : X → Y) : ReprogrammedCircuit V X Y → Matrix (QueryReg V 1 X Y) (QueryReg V 1 X Y) ℂ →
    Matrix (QueryReg V 1 X Y) (QueryReg V 1 X Y) ℂ
  | nil, ρ => ρ
  | kraus K c, ρ => run H c (K ρ)
  | rquery a c, ρ => run H c (ρ.submatrix (queryPermOf fun s => H.reprogram (a s)).symm
      (queryPermOf fun s => H.reprogram (a s)).symm)

theorem run_append (H : X → Y) (c d : ReprogrammedCircuit V X Y) (ρ : Matrix (QueryReg V 1 X Y) (QueryReg V 1 X Y) ℂ) :
    (c ++ d).run H ρ = d.run H (c.run H ρ) := by
  induction c generalizing ρ with
  | nil => rfl
  | kraus K c ih => exact ih _
  | rquery a c ih => exact ih _

/-- **The compilation into the core**: each reprogrammed query becomes `reprogSwap`, one query,
`reprogSwap` and `reprogAdd`; each Kraus map acts on the system with the identity on the
ancilla. -/
def toCircuit : ReprogrammedCircuit V X Y → Circuit (ReprogrammedQueryReg V X Y)
  | nil => .nil
  | kraus K c => .kraus K.liftAnc (toCircuit c)
  | rquery a c => .kraus (KrausMap.ofPerm (reprogSwap a))
      (.query (.kraus ((KrausMap.ofPerm (reprogAdd a)).comp (KrausMap.ofPerm (reprogSwap a)))
        (toCircuit c)))

theorem queries_toCircuit (c : ReprogrammedCircuit V X Y) : (toCircuit c).queries = c.queries := by
  induction c with
  | nil => rfl
  | kraus K c ih => exact ih
  | rquery a c ih => simp [toCircuit, Circuit.queries, queries, ih]

/-- **The compiled circuit runs the reprogrammed queries**: with the clean ancilla, the run of
the compiled circuit with oracle `H` is the run with Unruh's controlled queries, with the ancilla
still clean (`reprogQuery_eq_controlled`). -/
theorem run_toCircuit (H : X → Y) (x₀ : X) (c : ReprogrammedCircuit V X Y)
    (ρ : Matrix (QueryReg V 1 X Y) (QueryReg V 1 X Y) ℂ) :
    (toCircuit c).run (queryPerm H) (withAnc x₀ ρ) = withAnc x₀ (c.run H ρ) := by
  induction c generalizing ρ with
  | nil => rfl
  | kraus K c ih => rw [toCircuit, Circuit.run, KrausMap.liftAnc_apply_withAnc, ih]; rfl
  | rquery a c ih =>
    rw [toCircuit, Circuit.run, Circuit.run, Circuit.run, KrausMap.comp_apply, KrausMap.ofPerm_apply,
      KrausMap.ofPerm_apply, KrausMap.ofPerm_apply, submatrix_perm_submatrix_perm,
      submatrix_perm_submatrix_perm, submatrix_perm_submatrix_perm]
    rw [show (reprogSwap a).trans ((queryPerm H).trans ((reprogSwap a).trans (reprogAdd a))) =
      reprogPerm a H from rfl, reprogQuery_eq_controlled, ih]
    rfl

end ReprogrammedCircuit

end RCirc

end GordieHowe.Quantum
