-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.RealizeGrouped

@[expose] public section

/-!
# GordieHowe: the field form of `mod_q`, realized

The lemma that turns a `mod_p` in the field form (`GordieHowe.RealizedProgram.FieldFormOk`; compiler/mod.h, `m = p`:
the field equation `lhs − rhs = 0` and nothing else) into its integer congruence
(`GordieHowe.RealizedProgram.holdsWith_mod_of_field`).

The field equation `e = e'` holds in the field of the domain, which may be an extension of the
prime field `F_p` (Falcon native's `F_q^9`), and a side may apply a named operator whose public
operand lies outside `F_p` (the public key `ĥ` of `signature.equation`, an untyped statement
value). The integer reading of the field's elements (`FieldInterp.toNat`) is then read through its
projection `x ↦ (toNat x : K)`:

* **The model** (`FieldInterp.ReadLinear`, a property of the interpretation): the projection is
  additive and commutes with multiplication by the casts of naturals (for `F_q^9` the integer
  reading is the first coordinate in the power basis, an `F_q`-linear map). `Interp.FieldFormModel`
  asks it of the field of every `mod_q` in the field form (vacuous for a program without one,
  `Interp.fieldFormModel_of_none`).
* **The linear operators** (`NamedOp.block_eq_sum`): the negacyclic convolution, a number from its
  digits, a sum of groups and their batches are linear in their input, so their matrix entries
  (`NamedOp.applyInt`) give their values.
* **The projection** (`GordieHowe.RealizedProgram.evalIntWith_proj`): the integer reading of a side accepted by
  `projOkB` (sums, differences and constant multiples of expressions with an interval, and linear
  operators on them) casts to the projection of its value.

So the field equation gives `p ∣ e − e'` over the integers.
-/

namespace GordieHowe.RealizedProgram

open Export

/-! ## The model -/

/-- **The integer reading is linear over the prime field** (a property of the model): the
projection `x ↦ (toNat x : K)` is additive and commutes with multiplication by the casts of
naturals. For an extension of `F_p` whose integer reading is the first coordinate of a basis
containing `1`, it is that coordinate, an `F_p`-linear map. -/
structure FieldInterp.ReadLinear (F : FieldInterp) : Prop where
  /-- The projection is additive. -/
  add : ∀ x y : F.K, ((F.toNat (x + y) : ℕ) : F.K) = F.toNat x + F.toNat y
  /-- The projection commutes with multiplication by the cast of a natural. -/
  natMul : ∀ (n : ℕ) (x : F.K), ((F.toNat ((n : F.K) * x) : ℕ) : F.K) = n * F.toNat x

/-- **The fields of the field-form `mod_q`s read linearly** (a property of the model): the field of
the domain of every `mod_q` realized in the field form has a linear integer reading
(`FieldInterp.ReadLinear`). -/
def Interp.FieldFormModel (I : Interp) (ir : RealizedProgram) : Prop :=
  ∀ p < ir.predicates.length, ∀ d q e e' real, (ir.predicate p).body = .mod d q e e' real →
    real.form = .field → (I (ir.domainField d)).ReadLinear

section

/-- **Whether predicate `p` is a `mod_q` in the field form**, the predicates
`Interp.FieldFormModel` reads. -/
def isFieldForm (ir : RealizedProgram) (p : ℕ) : Bool :=
  match (ir.predicate p).body with
  | .mod _ _ _ _ real => real.form == .field
  | _ => false

end

/-- **A program without field-form `mod_q`s constrains no interpretation's integer readings**
(`Interp.FieldFormModel` holds vacuously). -/
theorem Interp.fieldFormModel_of_none {I : Interp} {ir : RealizedProgram}
    (h : ∀ p < ir.predicates.length, ir.isFieldForm p = false) : I.FieldFormModel ir := by
  intro p hp d q e e' real hb hf
  have := h p hp
  simp [RealizedProgram.isFieldForm, hb, hf] at this

/-- **Whether every field-form `mod_q` of the program is in a domain of field `f`** (decided): the
program's part of `Interp.FieldFormModel` (`Interp.fieldFormModel_of_field`). -/
def fieldFormsIn (ir : RealizedProgram) (f : ℕ) : Bool :=
  (List.range ir.predicates.length).all fun p =>
    match (ir.predicate p).body with
    | .mod d _ _ _ real => !(real.form == .field) || ir.domainField d == f
    | _ => true

/-- **The field-form model from one linear field** (`RealizedProgram.fieldFormsIn`): where every field-form
`mod_q` is in a domain of field `f`, the interpretation is a field-form model when `f` reads
linearly. -/
theorem Interp.fieldFormModel_of_field {I : Interp} {ir : RealizedProgram} {f : ℕ}
    (h : ir.fieldFormsIn f = true) (hRL : (I f).ReadLinear) : I.FieldFormModel ir := by
  intro p hp d q e e' real hb hf
  have h1 := List.all_eq_true.1 h p (List.mem_range.2 hp)
  simp only [hb, hf, beq_self_eq_true, Bool.not_true, Bool.false_or, beq_iff_eq] at h1
  rw [h1]
  exact hRL

/-! ## The projection -/

namespace FieldInterp

variable {F : FieldInterp} {p : ℕ}

/-- **The projection of an element**: its integer reading cast back into the field. -/
def proj (F : FieldInterp) (x : F.K) : F.K := ((F.toNat x : ℕ) : F.K)

theorem proj_zero (h0 : F.toNat 0 = 0) : F.proj 0 = 0 := by
  simp [proj, h0]

theorem ReadLinear.proj_add (h : F.ReadLinear) (x y : F.K) : F.proj (x + y) = F.proj x + F.proj y :=
  h.add x y

theorem ReadLinear.proj_sub (h : F.ReadLinear) (x y : F.K) : F.proj (x - y) = F.proj x - F.proj y := by
  have := h.proj_add (x - y) y
  rw [sub_add_cancel] at this
  rw [this]
  ring

theorem ReadLinear.proj_sum (h : F.ReadLinear) (h0 : F.toNat 0 = 0) {ι : Type*} (s : Finset ι)
    (g : ι → F.K) : F.proj (∑ t ∈ s, g t) = ∑ t ∈ s, F.proj (g t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [proj_zero h0]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, h.proj_add, ih]

/-- **An additive projection is linear** (`FieldInterp.ReadLinear`): multiplication by the cast of a
natural is repeated addition. -/
theorem ReadLinear.of_add
    (hadd : ∀ x y : F.K, ((F.toNat (x + y) : ℕ) : F.K) = F.toNat x + F.toNat y)
    (h0 : ((F.toNat 0 : ℕ) : F.K) = 0) : F.ReadLinear where
  add := hadd
  natMul n x := by
    rw [← nsmul_eq_mul, ← nsmul_eq_mul]
    induction n with
    | zero => rw [zero_smul, zero_smul, h0]
    | succ k ih => rw [succ_nsmul, hadd, ih, succ_nsmul]

/-- **The projection commutes with multiplication by the cast of an integer.** -/
theorem ReadLinear.proj_intCast_mul [CharP F.K p] (hp : 0 < p) (h : F.ReadLinear) (z : ℤ)
    (x : F.K) : F.proj ((z : F.K) * x) = (z : F.K) * F.proj x := by
  have hz : (z : F.K) = ((z % p).toNat : ℕ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hp.ne')),
      (CharP.intCast_eq_intCast F.K p).2 (Int.emod_emod_of_dvd z (dvd_refl _)).symm]
  rw [hz]
  exact h.natMul _ x

/-- **The projection fixes the casts of integers**, where the integer reading inverts the cast of a
natural below the characteristic. -/
theorem proj_intCast [CharP F.K p] (hp : 0 < p) (htn : ∀ k < p, F.toNat (k : F.K) = k) (z : ℤ) :
    F.proj (z : F.K) = (z : F.K) := by
  have hz : (z : F.K) = ((z % p).toNat : ℕ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hp.ne')),
      (CharP.intCast_eq_intCast F.K p).2 (Int.emod_emod_of_dvd z (dvd_refl _)).symm]
  have hlt : (z % p).toNat < p := by
    have := Int.emod_lt_of_pos z (by exact_mod_cast hp : (0 : ℤ) < p)
    omega
  rw [hz, proj, htn _ hlt]

end FieldInterp

/-! ## Linear operators -/

/-- **A linear operator's block is the sum of its matrix entries times its input** (`NamedOp.linB`):
coordinate `j` of the block on `y` is `Σ_{t < cols} block(e_t)_j · y_t`, `e_t` the unit vector. -/
theorem NamedOp.block_eq_sum (ir : RealizedProgram) {I : Interp} {f : ℕ} (leaf : ir.Valuation I) :
    ∀ (op : NamedOp), op.linB = true → ∀ (y : ℕ → (I f).K) (j : ℕ),
      NamedOp.block ir f leaf op y j = ∑ t ∈ Finset.range (NamedOp.cols ir op),
        NamedOp.block ir f leaf op (fun s => if s = t then 1 else 0) j * y t
  | .negacyclicConv h form, _, y, j => by
    simp only [NamedOp.block, NamedOp.cols]
    by_cases hj : j < (ir.value h).size
    · simp only [Ops.negacyclic_eq_sum _ _ _ hj]
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [sum_mul_unit _ _ (Finset.mem_range.1 ht)]
    · simp [Ops.negacyclic_eq, hj]
  | .fromDigits k base, _, y, j => by
    simp only [NamedOp.block, NamedOp.cols, Ops.fromDigits]
    split_ifs with hj
    · rw [Fin.sum_univ_eq_sum_range (fun l => (I f).decode base ^ l * y l) k]
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [Fin.sum_univ_eq_sum_range (fun l => (I f).decode base ^ l * if l = t then 1 else 0) k,
        sum_mul_unit _ _ (Finset.mem_range.1 ht)]
    · simp
  | .sum w, _, y, j => by
    simp only [NamedOp.block, NamedOp.cols, Ops.sum]
    split_ifs with hj
    · rw [Fin.sum_univ_eq_sum_range (fun l => y l) w]
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [Fin.sum_univ_eq_sum_range (fun l => if l = t then (1 : (I f).K) else 0) w]
      simp [Finset.mem_range.1 ht]
    · simp
  | .batched b op, h, y, j => by
    have hop : op.linB = true := h
    simp only [NamedOp.block, NamedOp.cols]
    split_ifs with hj
    · have hr : 0 < NamedOp.rows ir op := by
        rcases Nat.eq_zero_or_pos (NamedOp.rows ir op) with h0 | h0
        · rw [h0, Nat.mul_zero] at hj
          omega
        · exact h0
      have hq : j / NamedOp.rows ir op < b := by
        rw [Nat.div_lt_iff_lt_mul hr]
        exact hj
      set base := j / NamedOp.rows ir op * NamedOp.cols ir op with hbase
      rw [NamedOp.block_eq_sum ir leaf op hop]
      have hinner : ∀ t, NamedOp.block ir f leaf op (fun t' => if base + t' = t then 1 else 0)
          (j % NamedOp.rows ir op) = ∑ t' ∈ Finset.range (NamedOp.cols ir op),
            NamedOp.block ir f leaf op (fun s => if s = t' then 1 else 0) (j % NamedOp.rows ir op) *
              (if base + t' = t then 1 else 0) := fun t =>
        NamedOp.block_eq_sum ir leaf op hop _ _
      simp only [hinner, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun t' ht' => ?_
      have hlt : base + t' < b * NamedOp.cols ir op := by
        have := Finset.mem_range.1 ht'
        have : (j / NamedOp.rows ir op + 1) * NamedOp.cols ir op ≤ b * NamedOp.cols ir op :=
          Nat.mul_le_mul_right _ hq
        rw [hbase]
        nlinarith
      simp only [mul_assoc, ite_mul, one_mul, zero_mul, mul_ite, mul_zero]
      rw [Finset.sum_ite_eq (Finset.range _) (base + t'), if_pos (Finset.mem_range.2 hlt)]
    · simp

section

variable {ir : RealizedProgram} {I : Interp} {primeNodes : ℕ → List String} {L : ℕ → ℕ → Option Ivl}

/-! ## The integer reading of a side -/

/-- **An expression with an interval reads its projection on the integers**: its integer reading
casts to its value (`exprIvl_within_of_shape`), which the projection fixes
(`FieldInterp.proj_intCast`). -/
theorem evalIntWith_proj_of_ivl (hwf : ir.WellFormed) (hI : I.Registered ir)
    (hL : I.Lawful ir primeNodes) {rd : ir.Valuation I} (hF : ir.LeafFacts rd) {sr : List (ℕ × ℕ)}
    (hK : ir.ShiftFacts rd sr) (hLok : ir.LeafIvlsOk primeNodes sr L) {d : ℕ}
    (hd : d < ir.domains.length) (h2 : 2 < ir.charOf (ir.domainField d)) {e : Expr}
    (h : (ir.exprIvl L (ir.domainField d) e).isSome = true)
    (hs : ir.exprShapeOk e = true) (hr : ∀ k ∈ e.refs, k < ir.exprs.length) {i : ℕ}
    (hi : i < ir.exprLen e) : ((ir.evalIntWith rd d e i : ℤ) : (I (ir.domainField d)).K) =
      (I (ir.domainField d)).proj (ir.evalWith rd d e i) ∧
    ((ir.evalIntWith rd d e i : ℤ) : (I (ir.domainField d)).K) = ir.evalWith rd d e i := by
  obtain ⟨-, hcharF, -, -⟩ := modData hwf hI hL hd h2
  obtain ⟨J, hJ⟩ := Option.isSome_iff_exists.1 h
  have hw : IvlWithin (ir.exprIvl L (ir.domainField d) e) J.lo J.hi := by
    rw [hJ]
    exact ⟨le_rfl, le_rfl⟩
  obtain ⟨-, hc⟩ := exprIvl_within_of_shape hwf hI hL hF hK hLok hd h2 hs hr hw hi
  refine ⟨?_, hc⟩
  rw [← hc, FieldInterp.proj_intCast (p := ir.charOf (ir.domainField d)) (by omega)
    (hL.toNat_natCast _ (domainField_lt hwf hd))]

/-- **The integer reading of a side accepted by `projOkB` is the projection of its value**: under
the leaf facts and a linear integer reading (`FieldInterp.ReadLinear`), at every coordinate below
its length. -/
theorem evalIntWith_proj (hwf : ir.WellFormed) (hI : I.Registered ir)
    (hL : I.Lawful ir primeNodes) {rd : ir.Valuation I} (hF : ir.LeafFacts rd) {sr : List (ℕ × ℕ)}
    (hK : ir.ShiftFacts rd sr) (hLok : ir.LeafIvlsOk primeNodes sr L) {d : ℕ}
    (hd : d < ir.domains.length) (h2 : 2 < ir.charOf (ir.domainField d))
    (hRL : (I (ir.domainField d)).ReadLinear) :
    ∀ (e : Expr), ir.projOkB L (ir.domainField d) e = true → ir.exprShapeOk e = true →
      (∀ k ∈ e.refs, k < ir.exprs.length) → ∀ i < ir.exprLen e,
        ((ir.evalIntWith rd d e i : ℤ) : (I (ir.domainField d)).K) =
          (I (ir.domainField d)).proj (ir.evalWith rd d e i)
  | e, h, hs, hr, i, hi => by
    obtain ⟨hpch, hcharF, h01, hdec⟩ := modData hwf hI hL hd h2
    have hp0 : 0 < ir.charOf (ir.domainField d) := by omega
    unfold projOkB at h
    rcases Bool.or_eq_true_iff.1 h with hc | hm
    · exact (evalIntWith_proj_of_ivl hwf hI hL hF hK hLok hd h2 hc hs hr hi).1
    match e, hm, hs, hr, hi with
    | .add a b, hm, hs, hr, hi =>
      simp only [Bool.and_eq_true] at hm
      simp only [exprShapeOk, Bool.and_eq_true, beq_iff_eq] at hs
      have hra : ∀ k ∈ a.refs, k < ir.exprs.length := fun k hk => hr k (by simp [Expr.refs, hk])
      have hrb : ∀ k ∈ b.refs, k < ir.exprs.length := fun k hk => hr k (by simp [Expr.refs, hk])
      have hia : i < ir.exprLen a := hi
      have hib : i < ir.exprLen b := hs.2 ▸ hi
      have ha := evalIntWith_proj hwf hI hL hF hK hLok hd h2 hRL a hm.1 hs.1.1 hra i hia
      have hb := evalIntWith_proj hwf hI hL hF hK hLok hd h2 hRL b hm.2 hs.1.2 hrb i hib
      change ((ir.evalIntWith rd d a i + ir.evalIntWith rd d b i : ℤ) : (I (ir.domainField d)).K) =
        (I (ir.domainField d)).proj (ir.evalWith rd d a i + ir.evalWith rd d b i)
      rw [Int.cast_add, ha, hb, hRL.proj_add]
    | .sub a b, hm, hs, hr, hi =>
      simp only [Bool.and_eq_true] at hm
      simp only [exprShapeOk, Bool.and_eq_true, beq_iff_eq] at hs
      have hra : ∀ k ∈ a.refs, k < ir.exprs.length := fun k hk => hr k (by simp [Expr.refs, hk])
      have hrb : ∀ k ∈ b.refs, k < ir.exprs.length := fun k hk => hr k (by simp [Expr.refs, hk])
      have hia : i < ir.exprLen a := hi
      have hib : i < ir.exprLen b := hs.2 ▸ hi
      have ha := evalIntWith_proj hwf hI hL hF hK hLok hd h2 hRL a hm.1 hs.1.1 hra i hia
      have hb := evalIntWith_proj hwf hI hL hF hK hLok hd h2 hRL b hm.2 hs.1.2 hrb i hib
      change ((ir.evalIntWith rd d a i - ir.evalIntWith rd d b i : ℤ) : (I (ir.domainField d)).K) =
        (I (ir.domainField d)).proj (ir.evalWith rd d a i - ir.evalWith rd d b i)
      rw [Int.cast_sub, ha, hb, hRL.proj_sub]
    | .scale (.const c) a, hm, hs, hr, hi =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
      have ha := evalIntWith_proj hwf hI hL hF hK hLok hd h2 hRL a hm.2 hs hr i hi
      change (((I (ir.domainField d)).centered c * ir.evalIntWith rd d a i : ℤ) :
          (I (ir.domainField d)).K) =
        (I (ir.domainField d)).proj ((I (ir.domainField d)).decode c * ir.evalWith rd d a i)
      rw [Int.cast_mul, ha, FieldInterp.centered_eq, hpch, centeredZ_cast, hdec c hm.1,
        ← Int.cast_natCast c, hRL.proj_intCast_mul hp0]
    | .apply op a, hm, hs, hr, hi =>
      simp only [Bool.and_eq_true] at hm
      simp only [exprShapeOk, Bool.and_eq_true, beq_iff_eq] at hs
      have hrows : 0 < NamedOp.rows ir op := by
        rcases Nat.eq_zero_or_pos (NamedOp.rows ir op) with h0 | h0
        · change i < _ / _ * NamedOp.rows ir op at hi
          rw [h0, Nat.mul_zero] at hi
          omega
        · exact h0
      have hcast : ∀ t < NamedOp.cols ir op,
          ((ir.evalIntWith rd d a (i / NamedOp.rows ir op * NamedOp.cols ir op + t) : ℤ) :
            (I (ir.domainField d)).K) =
          ir.evalWith rd d a (i / NamedOp.rows ir op * NamedOp.cols ir op + t) := fun t ht =>
        (evalIntWith_proj_of_ivl hwf hI hL hF hK hLok hd h2 hm.2 hs.1.1 hr
          (NamedOp.lt_of_cols ir hrows hi ht)).2
      change ((NamedOp.applyInt ir (ir.domainField d) rd op (ir.evalIntWith rd d a) i : ℤ) :
          (I (ir.domainField d)).K) =
        (I (ir.domainField d)).proj (NamedOp.apply ir (ir.domainField d) rd op
          (ir.evalWith rd d a) i)
      unfold NamedOp.applyInt NamedOp.apply
      rw [NamedOp.block_eq_sum ir rd op hm.1, hRL.proj_sum h01.1, Int.cast_sum,
        ← Fin.sum_univ_eq_sum_range (fun t => (I (ir.domainField d)).proj
          (NamedOp.block ir (ir.domainField d) rd op (fun s => if s = t then 1 else 0)
            (i % NamedOp.rows ir op) *
            ir.evalWith rd d a (i / NamedOp.rows ir op * NamedOp.cols ir op + t)))]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [Int.cast_mul, hcast t t.2, ← hcast t t.2]
      conv_rhs => rw [mul_comm, hRL.proj_intCast_mul hp0]
      rw [FieldInterp.coefInt, FieldInterp.centered_eq, hpch, centeredZ_cast, mul_comm]
      rfl
    | .leaf _, hm, _, _, _ => cases hm
    | .scale (.node _ _) _, hm, _, _, _ => cases hm
    | .mul _ _, hm, _, _, _ => cases hm
    | .reindex _ _, hm, _, _, _ => cases hm
    | .concat _ _, hm, _, _, _ => cases hm
    | .linear _ _, hm, _, _, _ => cases hm
    | .prod _ _, hm, _, _, _ => cases hm
    | .mux _ _ _, hm, _, _, _ => cases hm
    | .ref _, hm, _, _, _ => cases hm
    | .logic _ _ _, hm, _, _, _ => cases hm

/-! ## The field form -/

/-- **A `mod_p` in the field form has its field equation** (`FieldFormOk`): under the leaf facts,
the field equation `e + (p − 1) e' = 0` is a field `equal` of the program (`fieldRowB`), so
`e = e'` in the field at every coordinate below `e`'s length. -/
theorem fieldEq_of_fieldFormOk (hwf : ir.WellFormed) (hI : I.Registered ir)
    (hL : I.Lawful ir primeNodes) {rd : ir.Valuation I} (hF : ir.LeafFacts rd) {sr : List (ℕ × ℕ)}
    (hK : ir.ShiftFacts rd sr) (hLok : ir.LeafIvlsOk primeNodes sr L) {d q : ℕ}
    {e e' : Expr} {real : ModRealization} (hpo : ir.PredOk (.mod d q e e' real))
    (hok : ir.FieldFormOk L d q e e' real) :
    ∀ i < ir.exprLen e, ir.evalWith rd d e i = ir.evalWith rd d e' i := by
  have hd : d < ir.domains.length := (hpo.1 (d, e) (by simp [PredBody.exprs])).1
  have hdF := domainField_lt hwf hd
  have h2 : 2 < ir.charOf (ir.domainField d) := hok.char ▸ hok.two
  obtain ⟨-, hcharF, -, hdec⟩ := modData hwf hI hL hd h2
  obtain ⟨pr, hpr, hrow⟩ := List.any_eq_true.1 hok.row
  obtain ⟨pid, hpid, rfl⟩ := exists_index_of_mem hpr
  unfold fieldRowB at hrow
  split at hrow
  · rename_i d' e₁ c e₂ z tgt hbody
    simp only [Bool.and_eq_true, beq_iff_eq] at hrow
    obtain ⟨⟨⟨⟨hd', h1⟩, h2'⟩, hc⟩, hz⟩ := hrow
    subst d'
    have hH := hF.equals pid hpid (by rw [hbody]; rfl)
    rw [hbody, Expr.eq_of_beq h1, Expr.eq_of_beq h2'] at hH
    intro i hi
    have hrowi := hH i hi
    simp only [evalWith, evalE_add, evalE_scale_const] at hrowi
    rw [evalE_leaf_constAll hL hF hz hdF (by omega) hi, hdec c (by omega)] at hrowi
    have hc1 : ((c : ℕ) : (I (ir.domainField d)).K) = -1 := by
      have : ((c + 1 : ℕ) : (I (ir.domainField d)).K) = 0 := by
        rw [hc]
        exact CharP.cast_eq_zero _ _
      push_cast at this
      linear_combination this
    rw [hc1, Nat.cast_zero] at hrowi
    simp only [evalWith]
    linear_combination hrowi
  · cases hrow

/-- **A `mod_p` in the field form holds where its field equation does** (`FieldFormOk`): under the
leaf facts, the field equation gives `e = e'` in the field (`fieldEq_of_fieldFormOk`); both sides'
integer readings cast to the projections of their values (`evalIntWith_proj`, under a linear integer
reading), so they are congruent modulo `p`. -/
theorem holdsWith_mod_of_field (hwf : ir.WellFormed) (hI : I.Registered ir)
    (hL : I.Lawful ir primeNodes) {rd : ir.Valuation I} (hF : ir.LeafFacts rd) {sr : List (ℕ × ℕ)}
    (hK : ir.ShiftFacts rd sr) (hLok : ir.LeafIvlsOk primeNodes sr L) {d q : ℕ}
    {e e' : Expr} {real : ModRealization} (hpo : ir.PredOk (.mod d q e e' real))
    (hok : ir.FieldFormOk L d q e e' real) (hRL : (I (ir.domainField d)).ReadLinear) :
    ir.HoldsWith rd (.mod d q e e' real) := by
  have heq := fieldEq_of_fieldFormOk hwf hI hL hF hK hLok hpo hok
  obtain ⟨hex, hlen⟩ := hpo
  have he := hex (d, e) (by simp [PredBody.exprs])
  have he' := hex (d, e') (by simp [PredBody.exprs])
  have hd : d < ir.domains.length := he.1
  have h2 : 2 < ir.charOf (ir.domainField d) := hok.char ▸ hok.two
  obtain ⟨-, hcharF, -, -⟩ := modData hwf hI hL hd h2
  intro i hi
  have hpe := evalIntWith_proj hwf hI hL hF hK hLok hd h2 hRL e hok.lhs he.2.shape he.2.refs i hi
  have hpe' := evalIntWith_proj hwf hI hL hF hK hLok hd h2 hRL e' hok.rhs he'.2.shape he'.2.refs i
    (hlen ▸ hi)
  rw [hok.char, ← CharP.intCast_eq_zero_iff (I (ir.domainField d)).K, Int.cast_sub, hpe, hpe',
    heq i hi, sub_self]

end

end GordieHowe.RealizedProgram
