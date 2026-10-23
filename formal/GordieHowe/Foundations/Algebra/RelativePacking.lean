-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import GordieHowe.Foundations.Algebra.FrobeniusOrder

@[expose] public section

/-!
# Relative extension packing: trace decoding and the linear identity

A second packing layer commits `D` coordinates of a subfield `E` as one element of
the field `K`, `[K : E] = D`. Here `E` is the fixed field of the relative Frobenius
`φ(x) = x^q`, `q = p^m = |E|` for `K` of exponential characteristic `p`
(`fixedField`), and `φ^D` is the identity on `K` (`field` instance
`RelFrobeniusOrder K p m D`). A relative basis `β` of `K/E` with its trace-dual basis
(`RelativeBasis`: `Tr_{K/E}(dual_i · β_j) = δ_ij`, `Tr_{K/E} x = Σ_{k<D} φ^k(x)`) packs
coordinates `c_i ∈ E` as `W = Σ_i β_i · c_i` (`pack`) and decodes them as
`c_i = Tr_{K/E}(dual_i · W)` (`coord`, `coord_pack`).

Every decoded coordinate lies in `E`, for every `W ∈ K` (`coord_mem`): the trace is fixed by `φ`. A
linear query `Σ_{y,i} coeff[y,i] · c[y,i]` on the coordinates of words `W_y` is evaluated through
`D` linear forms on the words, `a_k[y] = φ^(D-k)(Σ_i φ^k(dual_i) · coeff[y,i])` (`form`):
`Σ_k φ^k(Σ_y a_k[y] · W_y) = Σ_{y,i} coeff[y,i] · Tr_{K/E}(dual_i · W_y)` (`linear_identity`), for
every `W` (no subfield hypothesis). `form_eq` is the rearrangement
`φ^(D-k)(Σ_i φ^k(dual_i) · c_i) = Σ_i dual_i · φ^(D-k)(c_i)` between the two C++ evaluations of the
form.

Source: `lib/zk/zk_extension_packed.h` on `main` (commit `783b08e`).

* Degree and `q`. `ExtensionTraits<GF2_256<>>`: `degree = 16`, `q = 65536` (lines
  46-50), so `p = 2`, `m = 16`, `D = 16`; the Goldilocks quartic `Fp64G4`: `degree = 4`,
  `q = Fp64G::kP` (lines 51-55), `m = 1`. The Ligero subfield of `GF2_256` is
  `GF(2^16)` (`lib/gf2k/gf2_256.h:55-56`, `in_subfield` at `lib/gf2k/gf2_256.h:214-218`),
  the fixed field of `φ`.
* `φ`. `power(x, e)` is `x^e` (lines 102-110); `slow_phi(x, k)` applies `x ↦ x^q`
  `k mod D` times (lines 111-117), our `phi p m (k % D)` (`phi_mod`); `phi_public` is the
  same map through lookup tables (lines 239-263, binary tables lines 213-229).
* Trace. `trace(x) = Σ_{j<D} slow_phi(x, j)` (lines 118-125): `relTrace`.
* Basis. `beta[i] = g^i` for `g = x` (`of_scalar_field(2)`, lines 127-130) or the
  coordinate generator (lines 131-138), `beta[0] = 1` (lines 139-146). `beta_phi[k][i] =
  φ^k(beta[i])` (lines 147-149). The dual basis is `dual[i] = Σ_j (T⁻¹)_{ij} beta[j]` with
  `T_{ij} = trace(beta[i] · beta[j])`, by Gauss-Jordan on `[T | I]` (lines 150-176), so
  `trace(dual[i] · beta[j]) = δ_ij`: `RelativeBasis.trace_dual`.
* Packing. `pack_coordinate(x, i, y)` adds `beta[i] · y` (line 293; lines 285-292 for the
  native coordinate fields, where `beta` is the coordinate basis): `pack`.
* Forms. The characteristic-two path (lines 377-390) computes
  `a[k][y] = phi_public(Σ_i phi_public(dual[i], k) · coeff[yD + i], D − k)`, our `form`;
  the other path (lines 391-395) computes `Σ_i mul_dual(i, phi_public(coeff[yD+i], D−k))`,
  `mul_dual(i, x) = dual[i] · x` (lines 264-283), the right side of `form_eq`.
-/

namespace GordieHowe.RelativePacking

open scoped BigOperators

/-- **The relative Frobenius order.** `φ^D`, `x ↦ x^(p^(m D))`, is the identity on `K`,
for a positive `D`. For `K` of `p^(m D)` elements this holds with `[K : E] = D`,
`|E| = p^m`. A `field` fact about `K`. -/
class RelFrobeniusOrder (K : Type*) [Field K] (p m D : ℕ) : Prop where
  pos : 0 < D
  pow_eq : ∀ y : K, y ^ p ^ (m * D) = y

/-- The relative order from the absolute Frobenius order of a characteristic-two field:
if `y^(2^M) = y` for every `y` and `m · D = M`, then `φ = x^(2^m)` has order dividing `D`. -/
theorem RelFrobeniusOrder.of_frobeniusOrder {K : Type*} [Field K] {M m D : ℕ}
    [FrobeniusOrder K M] (h : m * D = M) (hD : 0 < D) : RelFrobeniusOrder K 2 m D where
  pos := hD
  pow_eq y := by rw [h]; exact FrobeniusOrder.pow_eq y

variable {K : Type*} [Field K] {p m D : ℕ} [ExpChar K p]

/-! ### The relative Frobenius -/

/-- `φ^k`, the `k`-th iterate of `x ↦ x^(p^m)`: `x ↦ x^(p^(m k))`. -/
def phi (p m k : ℕ) [ExpChar K p] (x : K) : K := iterateFrobenius K p (m * k) x

theorem phi_def (k : ℕ) (x : K) : phi p m k x = x ^ p ^ (m * k) := rfl

@[simp] theorem phi_zero (x : K) : phi p m 0 x = x := by
  simp [phi_def]

theorem phi_phi (j k : ℕ) (x : K) : phi p m j (phi p m k x) = phi p m (j + k) x := by
  simp only [phi, mul_add, iterateFrobenius_add_apply]

@[simp] theorem phi_add (k : ℕ) (x y : K) : phi p m k (x + y) = phi p m k x + phi p m k y :=
  map_add (iterateFrobenius K p (m * k)) x y

/-- `φ^k` preserves differences. -/
theorem phi_sub (k : ℕ) (x y : K) : phi p m k (x - y) = phi p m k x - phi p m k y :=
  map_sub (iterateFrobenius K p (m * k)) x y

@[simp] theorem phi_mul (k : ℕ) (x y : K) : phi p m k (x * y) = phi p m k x * phi p m k y :=
  map_mul (iterateFrobenius K p (m * k)) x y

@[simp] theorem phi_sum {ι : Type*} (s : Finset ι) (k : ℕ) (f : ι → K) :
    phi p m k (∑ i ∈ s, f i) = ∑ i ∈ s, phi p m k (f i) :=
  map_sum (iterateFrobenius K p (m * k)) f s

variable [RelFrobeniusOrder K p m D]

/-- `φ^D` is the identity. -/
theorem phi_order (x : K) : phi p m D x = x :=
  RelFrobeniusOrder.pow_eq x

variable (D) in
theorem phi_mul_order (j : ℕ) (x : K) : phi p m (D * j) x = x := by
  induction j with
  | zero => simp
  | succ j ih => rw [Nat.mul_succ, ← phi_phi, phi_order (D := D), ih]

/-- `φ^k` depends on `k mod D`: `slow_phi` and `phi_public` reduce `k` modulo `D`. -/
theorem phi_mod (k : ℕ) (x : K) : phi p m (k % D) x = phi p m k x := by
  conv_rhs => rw [← Nat.mod_add_div k D, ← phi_phi, phi_mul_order D]

/-- `φ^k ∘ φ^(D-k)` is the identity for `k ≤ D`. -/
theorem phi_phi_sub {k : ℕ} (hk : k ≤ D) (x : K) : phi p m k (phi p m (D - k) x) = x := by
  rw [phi_phi, Nat.add_sub_cancel' hk, phi_order]

/-- `φ^(D-k) ∘ φ^k` is the identity for `k ≤ D`. -/
theorem phi_sub_phi {k : ℕ} (hk : k ≤ D) (x : K) : phi p m (D - k) (phi p m k x) = x := by
  rw [phi_phi, Nat.sub_add_cancel hk, phi_order]

/-! ### The subfield -/

variable (K p m) in
/-- The subfield `E`: the fixed field of `φ`. -/
def fixedField : Subfield K := (iterateFrobenius K p m).eqLocusField (RingHom.id K)

omit [RelFrobeniusOrder K p m D] in
theorem mem_fixedField {x : K} : x ∈ fixedField K p m ↔ phi p m 1 x = x := by
  rw [fixedField, RingHom.mem_eqLocusField, phi, mul_one, RingHom.id_apply]

omit [RelFrobeniusOrder K p m D] in
/-- **The Frobenius test**: `x` lies in `E` exactly when `x ^ p ^ m = x`. -/
theorem mem_fixedField_iff_pow {x : K} : x ∈ fixedField K p m ↔ x ^ p ^ m = x := by
  rw [mem_fixedField, phi_def, mul_one]

/-- Membership in `E` decided by the Frobenius test `x ^ p ^ m = x` (`mem_fixedField_iff_pow`):
one exponentiation and one comparison. Not an instance: the finite type `fixedField K p m` keeps
the `Fintype` instance of a subtype under classical decidability throughout the development; the
verifiers use this decision explicitly. -/
def decidableMemFixedField [DecidableEq K] (x : K) : Decidable (x ∈ fixedField K p m) :=
  decidable_of_iff _ mem_fixedField_iff_pow.symm

omit [RelFrobeniusOrder K p m D] in
/-- Every power of `φ` fixes the subfield. -/
theorem phi_of_mem {x : K} (hx : x ∈ fixedField K p m) (k : ℕ) : phi p m k x = x := by
  induction k with
  | zero => simp
  | succ k ih => rw [← phi_phi, mem_fixedField.mp hx, ih]

/-! ### The relative trace -/

omit [RelFrobeniusOrder K p m D] in
variable (p m D) in
/-- `Tr_{K/E} x = Σ_{k<D} φ^k(x)`. -/
def relTrace (x : K) : K := ∑ k : Fin D, phi p m k x

omit [RelFrobeniusOrder K p m D] in
/-- The trace is `E`-linear. -/
theorem relTrace_mul_left {c : K} (hc : c ∈ fixedField K p m) (x : K) :
    relTrace p m D (c * x) = c * relTrace p m D x := by
  simp only [relTrace, phi_mul, phi_of_mem hc, Finset.mul_sum]

/-- `φ` fixes the trace: applying `φ` shifts the terms of the trace cyclically. -/
theorem phi_relTrace (x : K) : phi p m 1 (relTrace p m D x) = relTrace p m D x := by
  have hlast := Finset.sum_range_succ (fun k => phi p m k x) D
  have hfirst := Finset.sum_range_succ' (fun k => phi p m k x) D
  rw [phi_order] at hlast
  rw [phi_zero, hlast] at hfirst
  rw [relTrace, phi_sum]
  simp only [phi_phi, add_comm 1]
  rw [Fin.sum_univ_eq_sum_range (fun k => phi p m (k + 1) x),
    Fin.sum_univ_eq_sum_range (fun k => phi p m k x)]
  exact (add_right_cancel hfirst).symm

/-- The trace lies in `E`. -/
theorem relTrace_mem (x : K) : relTrace p m D x ∈ fixedField K p m :=
  mem_fixedField.mpr (phi_relTrace x)

omit [RelFrobeniusOrder K p m D] in
/-- **The trace of a `φ^D`-fixed element is `φ`-fixed**: applying `φ` shifts the terms of
`Σ_{k<D} φ^k(x)` cyclically when `φ^D(x) = x` (`phi_relTrace` is the case `φ^D = id` on `K`). -/
theorem phi_relTrace_of_fixed {x : K} (hx : phi p m D x = x) :
    phi p m 1 (relTrace p m D x) = relTrace p m D x := by
  have hlast := Finset.sum_range_succ (fun k => phi p m k x) D
  have hfirst := Finset.sum_range_succ' (fun k => phi p m k x) D
  rw [hx] at hlast
  rw [phi_zero, hlast] at hfirst
  rw [relTrace, phi_sum]
  simp only [phi_phi, add_comm 1]
  rw [Fin.sum_univ_eq_sum_range (fun k => phi p m (k + 1) x),
    Fin.sum_univ_eq_sum_range (fun k => phi p m k x)]
  exact (add_right_cancel hfirst).symm

omit [RelFrobeniusOrder K p m D] in
/-- The trace of a `φ^D`-fixed element lies in the fixed field of `φ`. -/
theorem relTrace_mem_of_fixed {x : K} (hx : phi p m D x = x) :
    relTrace p m D x ∈ fixedField K p m :=
  mem_fixedField.mpr (phi_relTrace_of_fixed hx)

omit [RelFrobeniusOrder K p m D] in
/-- A ring homomorphism commutes with `φ^k`. -/
theorem map_phi {L F : Type*} [Field L] [ExpChar L p] [FunLike F K L] [RingHomClass F K L]
    (σ : F) (k : ℕ) (x : K) :
    σ (phi p m k x) = phi p m k (σ x) := by
  rw [phi_def, phi_def, map_pow]

omit [RelFrobeniusOrder K p m D] in
/-- A ring homomorphism commutes with the relative trace. -/
theorem map_relTrace {L F : Type*} [Field L] [ExpChar L p] [FunLike F K L] [RingHomClass F K L]
    (σ : F) (x : K) :
    σ (relTrace p m D x) = relTrace p m D (σ x) := by
  simp only [relTrace, map_sum, map_phi]

/-! ### The relative basis, packing and decoding -/

omit [RelFrobeniusOrder K p m D] in
variable (K p m D) in
/-- A relative basis `β` of `K/E` with its trace-dual basis: `Tr_{K/E}(dual_i · β_j) = δ_ij`.
The field `trace_dual` is a `field` fact, certified once for the concrete field. -/
structure RelativeBasis where
  β : Fin D → K
  dual : Fin D → K
  trace_dual : ∀ i j, relTrace p m D (dual i * β j) = if i = j then 1 else 0

omit [RelFrobeniusOrder K p m D] in
/-- Packing `D` subfield coordinates into one word: `Σ_i β_i · c_i`. -/
def pack (B : RelativeBasis K p m D) (c : Fin D → K) : K := ∑ i, B.β i * c i

omit [RelFrobeniusOrder K p m D] in
/-- Decoding coordinate `i` of a word: `Tr_{K/E}(dual_i · W)`.

Running time: one multiplication and the relative trace, `D` Frobenius
powers `φ^k` each computed by repeated squaring, so polynomial in `D` and the bit length of
`K`. This running time is argued here, not proved in Lean. -/
def coord (B : RelativeBasis K p m D) (W : K) (i : Fin D) : K := relTrace p m D (B.dual i * W)

/-- **Every decoded coordinate lies in `E`**, for every word `W ∈ K`. -/
theorem coord_mem (B : RelativeBasis K p m D) (W : K) (i : Fin D) :
    coord B W i ∈ fixedField K p m :=
  relTrace_mem _

omit [RelFrobeniusOrder K p m D] in
/-- Decoding a packed word returns its coordinates, when they lie in `E`. -/
theorem coord_pack (B : RelativeBasis K p m D) {c : Fin D → K}
    (hc : ∀ i, c i ∈ fixedField K p m) (i : Fin D) : coord B (pack B c) i = c i := by
  have hsum : relTrace p m D (∑ j, B.dual i * B.β j * c j) =
      ∑ j, relTrace p m D (B.dual i * B.β j * c j) := by
    simp only [relTrace, phi_sum]
    exact Finset.sum_comm
  simp only [coord, pack, Finset.mul_sum, ← mul_assoc]
  rw [hsum]
  simp only [mul_comm _ (c _), relTrace_mul_left (hc _), B.trace_dual, mul_ite, mul_one, mul_zero]
  simp

omit [RelFrobeniusOrder K p m D] in
/-- `φ^k` of a packed word with coordinates in `E` twists only the basis. -/
theorem phi_pack (B : RelativeBasis K p m D) {c : Fin D → K} (hc : ∀ i, c i ∈ fixedField K p m)
    (k : ℕ) : phi p m k (pack B c) = ∑ i, phi p m k (B.β i) * c i := by
  simp only [pack, phi_sum, phi_mul, phi_of_mem (hc _)]

/-! ### The linear forms -/

omit [RelFrobeniusOrder K p m D] in
/-- The coefficient of a packed word in the `k`-th form for the coordinate coefficients
`coeff`: `φ^(D-k)(Σ_i φ^k(dual_i) · coeff_i)` (the C++ characteristic-two path). -/
def form (B : RelativeBasis K p m D) (coeff : Fin D → K) (k : Fin D) : K :=
  phi p m (D - k) (∑ i, phi p m k (B.dual i) * coeff i)

/-- **The rearrangement of the form**: `φ^(D-k)(Σ_i φ^k(dual_i) · c_i) = Σ_i dual_i ·
φ^(D-k)(c_i)`, the other C++ path. -/
theorem form_eq (B : RelativeBasis K p m D) (coeff : Fin D → K) (k : Fin D) :
    form B coeff k = ∑ i, B.dual i * phi p m (D - k) (coeff i) := by
  simp only [form, phi_sum, phi_mul, phi_sub_phi k.isLt.le]

/-- `φ^k` undoes the outer `φ^(D-k)` of the form. -/
theorem phi_form (B : RelativeBasis K p m D) (coeff : Fin D → K) (k : Fin D) :
    phi p m k (form B coeff k) = ∑ i, phi p m k (B.dual i) * coeff i :=
  phi_phi_sub k.isLt.le _

/-- **The relative linear identity.** For coordinate coefficients `coeff` and every vector of words
`W` (no subfield hypothesis),
`Σ_k φ^k(Σ_y a_k[y] · W_y) = Σ_{y,i} coeff[y,i] · Tr_{K/E}(dual_i · W_y)` with
`a_k[y] = form B (coeff y) k`. -/
theorem linear_identity (B : RelativeBasis K p m D) {ι : Type*} [Fintype ι]
    (coeff : ι → Fin D → K) (W : ι → K) :
    ∑ k : Fin D, phi p m k (∑ y, form B (coeff y) k * W y) =
      ∑ y, ∑ i, coeff y i * coord B (W y) i := by
  simp only [phi_sum, phi_mul, phi_form, coord, relTrace, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

end GordieHowe.RelativePacking
