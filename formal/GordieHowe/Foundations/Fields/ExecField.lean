-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.FieldTheory.Finite.Basic

@[expose] public section

/-!
# Executable fields from an injective map to a specification field

The concrete fields of the development (`GF2_128`, `GF2_256`, the Goldilocks, Falcon and ML-DSA
extensions) are specified as `AdjoinRoot` quotients of Mathlib polynomial rings, whose ring
operations do not compile. Each concrete field is a computable carrier (bit vectors or coefficient
vectors) with executable operations, and its `Field` instance is pulled back along an injective
map to the specification field that carries the operations to the specification's
(`Function.Injective.field`).

`ExecOps` holds the primitive operations (zero, one, addition, negation, multiplication,
inversion, the cast of naturals); the derived ones (powers by square-and-multiply, the integer and
rational casts, the scalar multiplications, division) are defined from them. `ExecOps.Hom` is an
injective map to a field that preserves the primitive operations; `ExecOps.Hom.field` is the
pulled-back `Field` instance, and `ExecOps.Hom.ringHom`/`ringEquiv` the map as a ring
homomorphism or isomorphism for it.

`inv_eq_pow_natCard_sub_two` is the inverse by exponentiation in a finite field, which the
concrete fields use for `ExecOps.inv`.
-/

namespace GordieHowe

/-! ## Powers by square-and-multiply -/

section PowBySquaring

variable {α : Type*}

/-- `b ^ e` by square-and-multiply from `one` and `mul`, with `k` recursion steps of fuel; the
recursion stops when the exponent reaches `0`, so fuel `e` costs `O(log e)` steps. -/
def powBySquaringAux (one : α) (mul : α → α → α) : ℕ → ℕ → α → α
  | 0, _, _ => one
  | k + 1, e, b =>
    if e = 0 then one
    else
      let r := powBySquaringAux one mul k (e / 2) (mul b b)
      if e % 2 = 1 then mul b r else r

/-- `b ^ e` by square-and-multiply from `one` and `mul`. -/
def powBySquaring (one : α) (mul : α → α → α) (b : α) (e : ℕ) : α :=
  powBySquaringAux one mul e e b

variable {M : Type*} [Monoid M] {one : α} {mul : α → α → α} {f : α → M}

theorem map_powBySquaringAux (h1 : f one = 1) (hmul : ∀ x y, f (mul x y) = f x * f y) :
    ∀ (k e : ℕ) (b : α), e ≤ k → f (powBySquaringAux one mul k e b) = f b ^ e
  | 0, e, b, he => by
    obtain rfl : e = 0 := by omega
    simp [powBySquaringAux, h1]
  | k + 1, e, b, he => by
    rw [powBySquaringAux]
    split_ifs with h0 hodd
    · simp [h0, h1]
    · rw [hmul, map_powBySquaringAux h1 hmul k (e / 2) _ (by omega), hmul, ← sq, ← pow_mul,
        ← pow_succ']
      congr 1
      omega
    · rw [map_powBySquaringAux h1 hmul k (e / 2) _ (by omega), hmul, ← sq, ← pow_mul]
      congr 1
      omega

theorem map_powBySquaring (h1 : f one = 1) (hmul : ∀ x y, f (mul x y) = f x * f y) (b : α)
    (e : ℕ) : f (powBySquaring one mul b e) = f b ^ e :=
  map_powBySquaringAux h1 hmul e e b le_rfl

end PowBySquaring

/-! ## The inverse by exponentiation -/

/-- In a finite field with more than two elements, `x⁻¹ = x ^ (q - 2)` for `q` the number of
elements (`x = 0` included, both sides `0`). -/
theorem inv_eq_pow_natCard_sub_two {L : Type*} [Field L] [Finite L] (h : 2 < Nat.card L)
    (x : L) : x⁻¹ = x ^ (Nat.card L - 2) := by
  have := Fintype.ofFinite L
  rw [Nat.card_eq_fintype_card] at h ⊢
  rcases eq_or_ne x 0 with rfl | hx
  · rw [inv_zero, zero_pow (by omega)]
  · refine inv_eq_of_mul_eq_one_left ?_
    rw [← pow_succ, show Fintype.card L - 2 + 1 = Fintype.card L - 1 by omega,
      FiniteField.pow_card_sub_one_eq_one x hx]

/-! ## Executable operations -/

/-- **The primitive operations of an executable field** on a carrier `α`. The other operations of
the pulled-back `Field` instance are derived from these (`ExecOps.pow`, `ExecOps.intCast`,
`ExecOps.ratCast`, …). -/
structure ExecOps (α : Type*) where
  /-- The zero element. -/
  zero : α
  /-- The unit element. -/
  one : α
  /-- Addition. -/
  add : α → α → α
  /-- Negation. -/
  neg : α → α
  /-- Multiplication. -/
  mul : α → α → α
  /-- Inversion (`0` at `0`). -/
  inv : α → α
  /-- The image of a natural number. -/
  natCast : ℕ → α

namespace ExecOps

variable {α : Type*} (o : ExecOps α)

/-- Subtraction, as addition of the negation. -/
def sub (x y : α) : α := o.add x (o.neg y)

/-- Division, as multiplication by the inverse. -/
def div (x y : α) : α := o.mul x (o.inv y)

/-- Natural powers by square-and-multiply. -/
def pow (x : α) (n : ℕ) : α := powBySquaring o.one o.mul x n

/-- The image of an integer. -/
def intCast : ℤ → α
  | .ofNat n => o.natCast n
  | .negSucc n => o.neg (o.natCast (n + 1))

/-- The image of a nonnegative rational, numerator times the inverse of the denominator. -/
def nnratCast (q : ℚ≥0) : α := o.div (o.natCast q.num) (o.natCast q.den)

/-- The image of a rational, numerator times the inverse of the denominator. -/
def ratCast (q : ℚ) : α := o.div (o.intCast q.num) (o.natCast q.den)

/-- Integer powers; a negative power is the inverse of the positive one. -/
def zpow (x : α) : ℤ → α
  | .ofNat n => o.pow x n
  | .negSucc n => o.inv (o.pow x (n + 1))

/-- **An injective map to a field preserving the primitive operations** (and hence, by the
lemmas below, the derived ones). The concrete fields map to their `AdjoinRoot` specifications. -/
structure Hom (L : Type*) [Field L] where
  /-- The map. -/
  toFun : α → L
  injective : Function.Injective toFun
  map_zero : toFun o.zero = 0
  map_one : toFun o.one = 1
  map_add : ∀ x y, toFun (o.add x y) = toFun x + toFun y
  map_neg : ∀ x, toFun (o.neg x) = -toFun x
  map_mul : ∀ x y, toFun (o.mul x y) = toFun x * toFun y
  map_inv : ∀ x, toFun (o.inv x) = (toFun x)⁻¹
  map_natCast : ∀ n : ℕ, toFun (o.natCast n) = n

namespace Hom

variable {o} {L : Type*} [Field L] (φ : o.Hom L)

theorem map_sub (x y : α) : φ.toFun (o.sub x y) = φ.toFun x - φ.toFun y := by
  rw [sub, φ.map_add, φ.map_neg, sub_eq_add_neg]

theorem map_div (x y : α) : φ.toFun (o.div x y) = φ.toFun x / φ.toFun y := by
  rw [div, φ.map_mul, φ.map_inv, div_eq_mul_inv]

theorem map_pow (x : α) (n : ℕ) : φ.toFun (o.pow x n) = φ.toFun x ^ n :=
  map_powBySquaring φ.map_one φ.map_mul x n

theorem map_intCast (z : ℤ) : φ.toFun (o.intCast z) = z := by
  cases z with
  | ofNat n => simp [intCast, φ.map_natCast]
  | negSucc n => rw [intCast, φ.map_neg, φ.map_natCast, Int.cast_negSucc]

theorem map_nnratCast (q : ℚ≥0) : φ.toFun (o.nnratCast q) = q := by
  rw [nnratCast, φ.map_div, φ.map_natCast, φ.map_natCast, NNRat.cast_def]

theorem map_ratCast (q : ℚ) : φ.toFun (o.ratCast q) = q := by
  rw [ratCast, φ.map_div, φ.map_intCast, φ.map_natCast, Rat.cast_def]

theorem map_zpow (x : α) (z : ℤ) : φ.toFun (o.zpow x z) = φ.toFun x ^ z := by
  cases z with
  | ofNat n => simp [zpow, φ.map_pow]
  | negSucc n => rw [zpow, φ.map_inv, φ.map_pow, zpow_negSucc]

/-- The field structure pulled back along `φ` (`Function.Injective.field`). It takes `φ` and
the field structure of `L` as arguments, so it compiles only when they do; `ExecOps.field` is the
same structure built from `o` alone. -/
abbrev fieldOfHom : Field α :=
  letI : Zero α := ⟨o.zero⟩
  letI : One α := ⟨o.one⟩
  letI : Add α := ⟨o.add⟩
  letI : Neg α := ⟨o.neg⟩
  letI : Sub α := ⟨o.sub⟩
  letI : Mul α := ⟨o.mul⟩
  letI : Inv α := ⟨o.inv⟩
  letI : Div α := ⟨o.div⟩
  letI : SMul ℕ α := ⟨fun n x => o.mul (o.natCast n) x⟩
  letI : SMul ℤ α := ⟨fun n x => o.mul (o.intCast n) x⟩
  letI : SMul ℚ≥0 α := ⟨fun q x => o.mul (o.nnratCast q) x⟩
  letI : SMul ℚ α := ⟨fun q x => o.mul (o.ratCast q) x⟩
  letI : Pow α ℕ := ⟨o.pow⟩
  letI : Pow α ℤ := ⟨o.zpow⟩
  letI : NatCast α := ⟨o.natCast⟩
  letI : IntCast α := ⟨o.intCast⟩
  letI : NNRatCast α := ⟨o.nnratCast⟩
  letI : RatCast α := ⟨o.ratCast⟩
  φ.injective.field φ.toFun φ.map_zero φ.map_one φ.map_add φ.map_mul φ.map_neg φ.map_sub
    φ.map_inv φ.map_div
    (fun n x => by
      change φ.toFun (o.mul _ x) = _
      rw [φ.map_mul, φ.map_natCast, nsmul_eq_mul])
    (fun n x => by
      change φ.toFun (o.mul _ x) = _
      rw [φ.map_mul, φ.map_intCast, zsmul_eq_mul])
    (fun q x => by
      change φ.toFun (o.mul _ x) = _
      rw [φ.map_mul, φ.map_nnratCast, NNRat.smul_def])
    (fun q x => by
      change φ.toFun (o.mul _ x) = _
      rw [φ.map_mul, φ.map_ratCast, Rat.smul_def])
    φ.map_pow φ.map_zpow φ.map_natCast φ.map_intCast φ.map_nnratCast φ.map_ratCast

end Hom

/-- The operations are those of a field: some injective map to a field preserves them. A `Prop`,
so that `ExecOps.field` takes no computationally relevant argument besides `o`. -/
def IsField : Prop := ∃ (L : Type) (_ : Field L), Nonempty (o.Hom L)

set_option hygiene false in
/-- `Hom.fieldOfHom` gives the field axioms under `IsField`. -/
local macro "exec_field_axiom " fld:ident : tactic =>
  `(tactic| (obtain ⟨L, _, ⟨φ⟩⟩ := h; exact (φ.fieldOfHom).$fld))

/-- **The executable field structure** on the carrier: every operation is the executable one of
`o` (or derived from it), and the axioms hold because some injective map to a field preserves
the operations (`Hom.fieldOfHom`, `Function.Injective.field`). -/
abbrev field (h : o.IsField) : Field α where
  zero := o.zero
  one := o.one
  add := o.add
  neg := o.neg
  sub := o.sub
  mul := o.mul
  inv := o.inv
  div := o.div
  nsmul n x := o.mul (o.natCast n) x
  zsmul n x := o.mul (o.intCast n) x
  nnqsmul q x := o.mul (o.nnratCast q) x
  qsmul q x := o.mul (o.ratCast q) x
  npow n x := o.pow x n
  zpow n x := o.zpow x n
  natCast := o.natCast
  intCast := o.intCast
  nnratCast := o.nnratCast
  ratCast := o.ratCast
  add_assoc := by exec_field_axiom add_assoc
  zero_add := by exec_field_axiom zero_add
  add_zero := by exec_field_axiom add_zero
  nsmul_zero := by exec_field_axiom nsmul_zero
  nsmul_succ := by exec_field_axiom nsmul_succ
  add_comm := by exec_field_axiom add_comm
  neg_add_cancel := by exec_field_axiom neg_add_cancel
  sub_eq_add_neg := by exec_field_axiom sub_eq_add_neg
  zsmul_zero' := by exec_field_axiom zsmul_zero'
  zsmul_succ' := by exec_field_axiom zsmul_succ'
  zsmul_neg' := by exec_field_axiom zsmul_neg'
  left_distrib := by exec_field_axiom left_distrib
  right_distrib := by exec_field_axiom right_distrib
  zero_mul := by exec_field_axiom zero_mul
  mul_zero := by exec_field_axiom mul_zero
  mul_assoc := by exec_field_axiom mul_assoc
  one_mul := by exec_field_axiom one_mul
  mul_one := by exec_field_axiom mul_one
  npow_zero := by exec_field_axiom npow_zero
  npow_succ := by exec_field_axiom npow_succ
  natCast_zero := by exec_field_axiom natCast_zero
  natCast_succ := by exec_field_axiom natCast_succ
  intCast_ofNat := by exec_field_axiom intCast_ofNat
  intCast_negSucc := by exec_field_axiom intCast_negSucc
  mul_comm := by exec_field_axiom mul_comm
  exists_pair_ne := by exec_field_axiom exists_pair_ne
  mul_inv_cancel := by exec_field_axiom mul_inv_cancel
  inv_zero := by exec_field_axiom inv_zero
  div_eq_mul_inv := by exec_field_axiom div_eq_mul_inv
  zpow_zero' := by exec_field_axiom zpow_zero'
  zpow_succ' := by exec_field_axiom zpow_succ'
  zpow_neg' := by exec_field_axiom zpow_neg'
  nnratCast_def := by exec_field_axiom nnratCast_def
  nnqsmul_def := by exec_field_axiom nnqsmul_def
  ratCast_def := by exec_field_axiom ratCast_def
  qsmul_def := by exec_field_axiom qsmul_def

section FieldLemmas

variable (h : o.IsField)

/-! The operations of `o.field h` are those of `o`, by definition. -/

theorem field_zero : letI := o.field h; (0 : α) = o.zero := rfl

theorem field_one : letI := o.field h; (1 : α) = o.one := rfl

theorem field_add (x y : α) : letI := o.field h; x + y = o.add x y := rfl

theorem field_neg (x : α) : letI := o.field h; -x = o.neg x := rfl

theorem field_mul (x y : α) : letI := o.field h; x * y = o.mul x y := rfl

theorem field_inv (x : α) : letI := o.field h; x⁻¹ = o.inv x := rfl

theorem field_pow (x : α) (n : ℕ) : letI := o.field h; x ^ n = o.pow x n := rfl

theorem field_natCast (n : ℕ) : letI := o.field h; (n : α) = o.natCast n := rfl

end FieldLemmas

namespace Hom

variable {o} {L : Type} [Field L] (φ : o.Hom L)

include φ in
theorem isField : o.IsField := ⟨L, inferInstance, ⟨φ⟩⟩

/-- The map as a ring homomorphism for the pulled-back structure. -/
def ringHom : letI := o.field φ.isField; α →+* L :=
  letI := o.field φ.isField
  { toFun := φ.toFun
    map_one' := φ.map_one
    map_mul' := φ.map_mul
    map_zero' := φ.map_zero
    map_add' := φ.map_add }

theorem ringHom_apply (x : α) : letI := o.field φ.isField; φ.ringHom x = φ.toFun x := rfl

/-- The map as a ring isomorphism, when it is also surjective. -/
noncomputable def ringEquiv (hs : Function.Surjective φ.toFun) :
    letI := o.field φ.isField; α ≃+* L :=
  letI := o.field φ.isField
  RingEquiv.ofBijective φ.ringHom ⟨φ.injective, hs⟩

theorem ringEquiv_apply (hs : Function.Surjective φ.toFun) (x : α) :
    letI := o.field φ.isField; φ.ringEquiv hs x = φ.toFun x := rfl

end Hom

end ExecOps

end GordieHowe
