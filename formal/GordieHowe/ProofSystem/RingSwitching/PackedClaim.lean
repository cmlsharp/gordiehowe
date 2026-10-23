-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Field.Subfield.Defs
public import GordieHowe.Foundations.Algebra.FrobeniusOrder

@[expose] public section

/-!
# Packed bit witnesses: the trace decode and the packed input claim

A proposed proof format for the H circuits commits private bit wires packed
`2^a` per element of a subfield `E` of a characteristic-two field `F`
(`GF(2^16)` inside `GF(2^128)`, `a = 4`): `p = ∑_i bit_i · β_i` for a basis `β`
of `E` over `F₂`. The bits are recovered by the trace decode
`bit_i = Tr(β*_i · p)` with the dual basis `β*` and `Tr x = ∑_{k < 2^a} x^(2^k)`.

GKR reduces circuit satisfaction to an input claim `∑_x (eq(g0, x) + α · eq(g1, x)) · w_x = v`
(`claimCoeff`). On the packed region the verifier checks it through `2^a` linear forms `a_k` on the
packed values: with `z_k = ⟨a_k, p⟩`, the packed part of the claim equals `∑_k z_k^(2^k)`, for every
`p ∈ F`. This identity is `PackingStage.StageBasis.linear_identity` at the stage of a packed basis
(`PackedBasis.toStageBasis`, whose decode is `decode`, `PackingStage.coord_toStageBasis`).

Subfield membership is used only for Booleanity: `Tr(β*_i · p)` is `0` or `1` when `p ∈ E`
(`decode_bool`). The verifier's check that opened entries of packed rows lie in `E` supplies that
membership (`GordieHowe.Ligero.SubfieldTest.subfieldCheck_sound_exact`).

Multilinear indexing follows Longfellow's convention: coordinate `t` of a claim point matches bit
`t` of the index (little-endian), so the first `a` coordinates select the position inside a packed
element and the rest select the element (`eqPt`).
-/

namespace GordieHowe.PackedClaim

open scoped BigOperators

variable {F : Type*} [Field F]

/-- The multilinear equality polynomial at a point `g`, evaluated at the
hypercube point with the bits of `x` (little-endian). -/
def eqPt {ℓ : ℕ} (g : Fin ℓ → F) (x : ℕ) : F :=
  ∏ t : Fin ℓ, if x.testBit t then g t else 1 - g t

/-- The combined claim coefficient at input index `x`. -/
def claimCoeff {ℓ : ℕ} (g0 g1 : Fin ℓ → F) (α : F) (x : ℕ) : F :=
  eqPt g0 x + α * eqPt g1 x

/-- The trace from a subfield of size `2^(2^a)` to `F₂`, written in `F`. -/
def trace (a : ℕ) (x : F) : F := ∑ k : Fin (2 ^ a), x ^ (2 ^ (k : ℕ))

/-- A packing subfield with a basis and its trace-dual basis. The fields are
`field` facts, certified once for the concrete field. -/
structure PackedBasis (F : Type*) [Field F] (a : ℕ) where
  E : Subfield F
  fixed : ∀ x ∈ E, x ^ (2 ^ (2 ^ a)) = x
  β : Fin (2 ^ a) → F
  β_mem : ∀ i, β i ∈ E
  βdual : Fin (2 ^ a) → F
  βdual_mem : ∀ i, βdual i ∈ E
  dual : ∀ i j, trace a (βdual i * β j) = if i = j then 1 else 0

variable {a : ℕ}

/-- The trace decode of a packed value: its `i`-th bit. -/
def decode (P : PackedBasis F a) (p : F) (i : Fin (2 ^ a)) : F := trace a (P.βdual i * p)

/-- Packing bits into the subfield. -/
def pack (P : PackedBasis F a) (b : Fin (2 ^ a) → Bool) : F :=
  ∑ j, if b j then P.β j else 0

theorem trace_zero : trace a (0 : F) = 0 := by
  simp [trace]

theorem decode_zero (P : PackedBasis F a) (i : Fin (2 ^ a)) : decode P 0 i = 0 := by
  simp [decode, trace_zero]

theorem pack_mem (P : PackedBasis F a) (b : Fin (2 ^ a) → Bool) : pack P b ∈ P.E := by
  refine P.E.sum_mem fun j _ => ?_
  split_ifs
  · exact P.β_mem j
  · exact P.E.zero_mem

variable [CharP F 2]

/-- The trace is additive. -/
theorem trace_sum {ι : Type*} (s : Finset ι) (f : ι → F) :
    trace a (∑ j ∈ s, f j) = ∑ j ∈ s, trace a (f j) := by
  simp only [trace, sum_pow_char_pow]
  exact Finset.sum_comm

/-- Decoding is additive in characteristic two (the trace is). -/
theorem decode_add (P : PackedBasis F a) (x y : F) (i : Fin (2 ^ a)) :
    decode P (x + y) i = decode P x i + decode P y i := by
  simp only [decode, trace, mul_add, add_pow_char_pow, Finset.sum_add_distrib]

/-- On an element fixed by `x ↦ x^(2^(2^a))` the trace is fixed by squaring:
squaring shifts the terms of the trace cyclically. -/
theorem trace_sq {x : F} (hx : x ^ (2 ^ (2 ^ a)) = x) : trace a x ^ 2 = trace a x := by
  have hlast := Finset.sum_range_succ (fun k => x ^ (2 ^ k)) (2 ^ a)
  have hfirst := Finset.sum_range_succ' (fun k => x ^ (2 ^ k)) (2 ^ a)
  rw [hx] at hlast
  rw [pow_zero, pow_one, hlast] at hfirst
  rw [trace, sum_pow_char]
  simp only [← pow_mul, ← pow_succ]
  rw [Fin.sum_univ_eq_sum_range (fun k => x ^ (2 ^ (k + 1))),
    Fin.sum_univ_eq_sum_range (fun k => x ^ (2 ^ k))]
  exact (add_right_cancel hfirst).symm

/-- Decoding a packed vector returns its bits. -/
theorem decode_pack (P : PackedBasis F a) (b : Fin (2 ^ a) → Bool) (i : Fin (2 ^ a)) :
    decode P (pack P b) i = if b i then 1 else 0 := by
  simp only [decode, pack, Finset.mul_sum, mul_ite, mul_zero, trace_sum, apply_ite (trace a),
    trace_zero, P.dual]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

/-- On the subfield the decode is Boolean. -/
theorem decode_bool (P : PackedBasis F a) {p : F} (hp : p ∈ P.E) (i : Fin (2 ^ a)) :
    decode P p i = 0 ∨ decode P p i = 1 :=
  eq_zero_or_one_of_sq_eq_self (trace_sq (P.fixed _ (P.E.mul_mem (P.βdual_mem i) hp)))

/-- Packing is injective: decoding recovers the bits. -/
theorem pack_injective (P : PackedBasis F a) : Function.Injective (pack P) := by
  intro b c h
  funext i
  have hi := decode_pack P b i
  rw [h, decode_pack] at hi
  cases hb : b i <;> cases hc : c i <;> simp_all

/-- **The subfield element of a natural** `u`: its low `2^a` bits packed, `Σ_i bit_i(u) β_i`.
This is the C++ `of_scalar(u)` of a binary field with a subfield basis `beta_[]`
(`lib/gf2k/gf2_256.h:167-173`), whose Reed–Solomon points are `of_scalar(0), of_scalar(1), …`. -/
def ofScalar (P : PackedBasis F a) (u : ℕ) : F := pack P fun i => u.testBit i

omit [CharP F 2] in
theorem ofScalar_mem (P : PackedBasis F a) (u : ℕ) : ofScalar P u ∈ P.E := pack_mem P _

/-- `ofScalar` is injective below `2^(2^a)`. -/
theorem ofScalar_inj (P : PackedBasis F a) {u v : ℕ} (hu : u < 2 ^ 2 ^ a) (hv : v < 2 ^ 2 ^ a)
    (h : ofScalar P u = ofScalar P v) : u = v := by
  have hb := congrFun (pack_injective P h)
  refine Nat.eq_of_testBit_eq fun i => ?_
  by_cases hi : i < 2 ^ a
  · exact hb ⟨i, hi⟩
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hu (Nat.pow_le_pow_right (by norm_num)
      (not_lt.mp hi))), Nat.testBit_lt_two_pow (lt_of_lt_of_le hv
      (Nat.pow_le_pow_right (by norm_num) (not_lt.mp hi)))]

variable {b : ℕ}

end GordieHowe.PackedClaim
