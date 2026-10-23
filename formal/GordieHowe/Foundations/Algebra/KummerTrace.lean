-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import GordieHowe.Foundations.Algebra.RelativePacking

@[expose] public section

/-!
# Relative traces of Kummer bases, tower transitivity and the uniform trace dual

Structural facts for `RelativeBasis` at fields presented as `AdjoinRoot`s of binomials, where
the trace-dual cannot be certified by computation.

* `RelFrobeniusOrder.of_card`: `|K| = p^(m D)` gives the relative Frobenius order.
* `fixedField_one_eq_range`: the fixed field of `x ↦ x^p` is the prime subfield, the image of
  `ZMod p` (at most `p` roots of `X^p − X`).
* Kummer layer. An eigenvector `x` of `φ`, `φ(x) = ζ x` with `ζ ∈ E`, has
  `φ^k(x) = ζ^k x` (`phi_eigen`), and `Tr_{K/E}(w x) = D · w x` if `ζ = 1` and `0` if
  `ζ ≠ 1`, `ζ^D = 1` (`relTrace_eigen`, the geometric sum). For `x^n = c ∈ E` and
  `p^m = n t + 1`, `x` is an eigenvector with `ζ = c^t` (`phi_one_of_pow_eq`).
* Tower: `Tr_{K/E} = Tr_{M/E} ∘ Tr_{K/M}`, `relTrace p m (D₁ D₂) = relTrace p m D₁ ∘
  relTrace p (m D₁) D₂` (`relTrace_tower`); no order hypothesis.
  For two Kummer layers, `Tr_{K/E}(x^a y^b / (x^a' y^b')) = D₁ D₂ δ` (`relTrace_tower_quot`),
  giving the tower basis `x^(k mod D₁) y^(k / D₁)` (`RelativeBasis.ofTower`) and, when the
  outer generator is `y^D₂`, the power basis `y^k` (`RelativeBasis.ofTowerPow`).
* Uniform dual: if `Tr(β_i / β_j) = D δ_ij`, the trace dual is `dual_j = (D β_j)⁻¹`
  (`RelativeBasis.ofTraceQuot`); for `β_i = x^i` with `ζ` a primitive `D`-th root this holds
  (`RelativeBasis.ofEigen`). The trace dual of a basis is unique, so this is the dual the C++
  computes by Gauss-Jordan on `[T | I]` (`lib/zk/zk_extension_packed.h:150-176`); uniqueness is not
  formalized here.
-/

namespace GordieHowe.RelativePacking

open scoped BigOperators
open Polynomial

variable {K : Type*} [Field K] {p m D : ℕ} [ExpChar K p]

omit [ExpChar K p] in
/-- The relative Frobenius order from the cardinality: `|K| = p^(m D)`. -/
theorem RelFrobeniusOrder.of_card [Fintype K] (h : Fintype.card K = p ^ (m * D)) (hD : 0 < D) :
    RelFrobeniusOrder K p m D where
  pos := hD
  pow_eq y := by rw [← h]; exact FiniteField.pow_card y

theorem relTrace_zero : relTrace p m D (0 : K) = 0 := by
  simp [relTrace, phi_def, zero_pow (pow_ne_zero _ (expChar_ne_zero K p))]

/-- Natural casts lie in the fixed field. -/
theorem natCast_mem_fixedField (n : ℕ) : (n : K) ∈ fixedField K p m := natCast_mem _ n

/-- The fixed field of `x ↦ x^(p^m)` lies in the fixed field of `x ↦ x^(p^(m k))`. -/
theorem mem_fixedField_mul {x : K} (hx : x ∈ fixedField K p m) (k : ℕ) :
    x ∈ fixedField K p (m * k) := by
  rw [mem_fixedField, phi_def, mul_one, ← phi_def]
  exact phi_of_mem hx k

/-! ### The prime subfield -/

section PrimeSubfield

variable [Fact p.Prime] [Algebra (ZMod p) K]

/-- **The fixed field of `x ↦ x^p` is the prime subfield**: `ZMod p` gives `p` roots of
`X^p − X`, and there are no others. -/
theorem fixedField_one_eq_range : fixedField K p 1 = (algebraMap (ZMod p) K).fieldRange := by
  classical
  have hp := (Fact.out : p.Prime)
  apply le_antisymm
  · intro y hy
    rw [mem_fixedField, phi_def, mul_one, pow_one] at hy
    by_contra hn
    have hP : (X ^ p - X : K[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero K hp.one_lt
    have hdeg : (X ^ p - X : K[X]).natDegree = p :=
      FiniteField.X_pow_card_sub_X_natDegree_eq K hp.one_lt
    have hroot : ∀ z : K, z ^ p = z → z ∈ (X ^ p - X : K[X]).roots.toFinset := by
      intro z hz
      rw [Multiset.mem_toFinset, mem_roots hP, IsRoot, eval_sub, eval_pow, eval_X, hz, sub_self]
    have hS : insert y (Finset.univ.image (algebraMap (ZMod p) K)) ⊆
        (X ^ p - X : K[X]).roots.toFinset := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hroot _ hy
      · obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hz
        exact hroot _ (by rw [← map_pow, ZMod.pow_card])
    have hcard := Finset.card_le_card hS
    rw [Finset.card_insert_of_notMem (fun h => hn (by
      obtain ⟨a, -, ha⟩ := Finset.mem_image.mp h
      exact ⟨a, ha⟩)), Finset.card_image_of_injective _ (algebraMap (ZMod p) K).injective,
      Finset.card_univ, ZMod.card] at hcard
    have h1 := Multiset.toFinset_card_le (X ^ p - X : K[X]).roots
    have h2 := card_roots' (X ^ p - X : K[X])
    omega
  · rintro _ ⟨a, rfl⟩
    rw [mem_fixedField, phi_def, mul_one, pow_one, ← map_pow, ZMod.pow_card]

theorem algebraMap_mem_fixedField_one (a : ZMod p) : algebraMap (ZMod p) K a ∈ fixedField K p 1 :=
  fixedField_one_eq_range (K := K) (p := p) ▸ ⟨a, rfl⟩

end PrimeSubfield

/-! ### Kummer layers -/

/-- An eigenvector of `φ` with an eigenvalue in `E`: `φ^k(x) = ζ^k x`. -/
theorem phi_eigen {x ζ : K} (hζ : ζ ∈ fixedField K p m) (hx : phi p m 1 x = ζ * x) (k : ℕ) :
    phi p m k x = ζ ^ k * x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [add_comm k 1, ← phi_phi 1 k, ih, phi_mul, hx, phi_of_mem (pow_mem hζ k)]
    ring

theorem phi_eigen_mul {x y ζ η : K} (hx : phi p m 1 x = ζ * x) (hy : phi p m 1 y = η * y) :
    phi p m 1 (x * y) = (ζ * η) * (x * y) := by
  rw [phi_mul, hx, hy]; ring

theorem phi_eigen_inv {x ζ : K} (hx : phi p m 1 x = ζ * x) :
    phi p m 1 x⁻¹ = ζ⁻¹ * x⁻¹ := by
  rw [phi_def, inv_pow, ← phi_def, hx, mul_inv]

theorem phi_eigen_pow {x ζ : K} (hx : phi p m 1 x = ζ * x) (n : ℕ) :
    phi p m 1 (x ^ n) = ζ ^ n * x ^ n := by
  rw [phi_def, ← pow_mul, mul_comm, pow_mul, ← phi_def, hx, mul_pow]

/-- **Kummer-layer trace.** For an eigenvector `x` of `φ` with eigenvalue `ζ ∈ E`,
`ζ^D = 1`, and `w ∈ E`: `Tr(w x) = D · w x` if `ζ = 1`, and `0` otherwise. -/
theorem relTrace_eigen [DecidableEq K] {x ζ w : K} (hw : w ∈ fixedField K p m)
    (hζ : ζ ∈ fixedField K p m) (hx : phi p m 1 x = ζ * x) (hD : ζ ^ D = 1) :
    relTrace p m D (w * x) = if ζ = 1 then (D : K) * (w * x) else 0 := by
  rw [relTrace_mul_left hw, relTrace]
  simp only [phi_eigen hζ hx]
  rw [← Finset.sum_mul, Fin.sum_univ_eq_sum_range (fun k => ζ ^ k)]
  split_ifs with h1
  · simp [h1]; ring
  · rw [geom_sum_eq h1, hD, sub_self, zero_div, zero_mul, mul_zero]

/-- A root of a binomial `x^n = c ∈ E` with `p^m = n t + 1` is an eigenvector of `φ` with
eigenvalue `c^t`. -/
theorem phi_one_of_pow_eq {x c : K} {n t : ℕ} (hxc : x ^ n = c) (hq : p ^ m = n * t + 1) :
    phi p m 1 x = c ^ t * x := by
  rw [phi_def, mul_one, hq, pow_succ, pow_mul, hxc]

/-! ### Tower transitivity -/

/-- **Tower transitivity**: `Tr_{K/E} = Tr_{M/E} ∘ Tr_{K/M}` for `E ⊆ M ⊆ K` the fixed
fields of `x ↦ x^(p^m₁)` and `x ↦ x^(p^m₂)`, `m₂ = m₁ D₁`. -/
theorem relTrace_tower {m₁ m₂ D₁ D₂ : ℕ} (hm : m₂ = m₁ * D₁) (x : K) :
    relTrace p m₁ (D₁ * D₂) x = relTrace p m₁ D₁ (relTrace p m₂ D₂ x) := by
  subst hm
  have h : ∀ (a : Fin D₁) (b : Fin D₂),
      phi p m₁ (a : ℕ) (phi p (m₁ * D₁) (b : ℕ) x) =
        phi p m₁ ((finProdFinEquiv (b, a) : Fin (D₂ * D₁)) : ℕ) x := by
    intro a b
    rw [finProdFinEquiv_apply_val, phi_def, phi_def, phi_def, ← pow_mul, ← pow_add]
    congr 2
    ring
  simp only [relTrace, phi_sum, h]
  rw [Finset.sum_comm, ← Fintype.sum_prod_type', Fintype.sum_equiv finProdFinEquiv _
    (fun k : Fin (D₂ * D₁) => phi p m₁ (k : ℕ) x) (fun _ => rfl)]
  exact Fintype.sum_equiv (finCongr (mul_comm D₁ D₂)) _ _ (fun _ => rfl)

/-! ### The uniform trace dual -/

theorem natCast_inv_mem_fixedField (n : ℕ) : (n : K)⁻¹ ∈ fixedField K p m :=
  inv_mem (natCast_mem _ n)

/-- **The uniform dual.** A family `β` with `Tr(β_i · β_j⁻¹) = D δ_ij` and `D ≠ 0` in `K`
is a relative basis with trace dual `dual_j = (D β_j)⁻¹`. -/
def RelativeBasis.ofTraceQuot (β : Fin D → K) (hD : (D : K) ≠ 0)
    (h : ∀ i j, relTrace p m D (β i * (β j)⁻¹) = if i = j then (D : K) else 0) :
    RelativeBasis K p m D where
  β := β
  dual j := ((D : K) * β j)⁻¹
  trace_dual i j := by
    rw [mul_inv, mul_comm, mul_left_comm, relTrace_mul_left (natCast_inv_mem_fixedField D), h j i]
    split_ifs with h1 h2 h2
    · exact inv_mul_cancel₀ hD
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · exact mul_zero _

theorem RelativeBasis.ofTraceQuot_dual (β : Fin D → K) (hD : (D : K) ≠ 0) (h) (j : Fin D) :
    (RelativeBasis.ofTraceQuot (p := p) (m := m) β hD h).dual j = ((D : K) * β j)⁻¹ := rfl

/-- **Trace of a quotient of powers.** For an eigenvector `x ≠ 0` of `φ` whose eigenvalue
`ζ ∈ E` is a primitive `D`-th root of unity, `w ∈ E` and `a, b < D`:
`Tr(w · x^a / x^b) = D · w` if `a = b`, and `0` otherwise. -/
theorem relTrace_pow_quot {x ζ w : K} (hw : w ∈ fixedField K p m) (hζ : ζ ∈ fixedField K p m)
    (hx : phi p m 1 x = ζ * x) (hprim : IsPrimitiveRoot ζ D) (hx0 : x ≠ 0) {a b : ℕ}
    (ha : a < D) (hb : b < D) :
    relTrace p m D (w * (x ^ a * (x ^ b)⁻¹)) = if a = b then (D : K) * w else 0 := by
  classical
  have hz0 : ζ ≠ 0 := hprim.ne_zero (by omega)
  have he := phi_eigen_mul (phi_eigen_pow hx a) (phi_eigen_inv (phi_eigen_pow hx b))
  have hmem : ζ ^ a * (ζ ^ b)⁻¹ ∈ fixedField K p m :=
    mul_mem (pow_mem hζ _) (inv_mem (pow_mem hζ _))
  have hpow : (ζ ^ a * (ζ ^ b)⁻¹) ^ D = 1 := by
    rw [mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm a, mul_comm b, pow_mul,
      pow_mul, hprim.pow_eq_one, one_pow, one_pow, inv_one, mul_one]
  have hiff : ζ ^ a * (ζ ^ b)⁻¹ = 1 ↔ a = b := by
    rw [mul_inv_eq_one₀ (pow_ne_zero _ hz0)]
    exact ⟨fun h => hprim.pow_inj ha hb h, fun h => by rw [h]⟩
  rw [relTrace_eigen hw hmem he hpow]
  by_cases hab : a = b
  · subst hab
    simp only [hiff, ite_true, mul_inv_cancel₀ (pow_ne_zero _ hx0), mul_one]
  · simp only [hiff, hab, ite_false]

/-- **Power basis of a Kummer layer.** If `φ(x) = ζ x` with `ζ ∈ E` a primitive `D`-th
root of unity, `x ≠ 0` and `D ≠ 0` in `K`, then `β_i = x^i` is a relative basis with dual
`(D x^j)⁻¹`. -/
def RelativeBasis.ofEigen {x ζ : K} (hζ : ζ ∈ fixedField K p m)
    (hx : phi p m 1 x = ζ * x) (hprim : IsPrimitiveRoot ζ D) (hx0 : x ≠ 0)
    (hD : (D : K) ≠ 0) : RelativeBasis K p m D :=
  RelativeBasis.ofTraceQuot (fun i => x ^ (i : ℕ)) hD fun i j => by
    have h := relTrace_pow_quot (one_mem _) hζ hx hprim hx0 i.isLt j.isLt
    rw [one_mul, mul_one] at h
    rw [h]
    simp only [Fin.val_inj]

/-- **Trace of a quotient of tower monomials.** `E ⊆ M ⊆ K`, `E`, `M` the fixed fields of
`x ↦ x^(p^m₁)` and `x ↦ x^(p^m₂)`, `m₂ = m₁ D₁`. The outer generator `x ∈ M` is an eigenvector
of `φ_E` with a primitive `D₁`-th root `ζ ∈ E`; the inner generator `y` is an eigenvector of
`φ_M` with a primitive `D₂`-th root `η ∈ M`. For `a, a' < D₁` and `b, b' < D₂`:
`Tr_{K/E}(x^a y^b / (x^a' y^b')) = D₁ D₂` if `(a, b) = (a', b')`, and `0` otherwise. -/
theorem relTrace_tower_quot {m₁ m₂ D₁ D₂ : ℕ} (hm : m₂ = m₁ * D₁) {x ζ y η : K}
    (hxM : x ∈ fixedField K p m₂) (hζ : ζ ∈ fixedField K p m₁) (hx : phi p m₁ 1 x = ζ * x)
    (hζp : IsPrimitiveRoot ζ D₁) (hx0 : x ≠ 0)
    (hη : η ∈ fixedField K p m₂) (hy : phi p m₂ 1 y = η * y)
    (hηp : IsPrimitiveRoot η D₂) (hy0 : y ≠ 0) {a a' b b' : ℕ} (ha : a < D₁) (ha' : a' < D₁)
    (hb : b < D₂) (hb' : b' < D₂) :
    relTrace p m₁ (D₁ * D₂) (x ^ a * y ^ b * (x ^ a' * y ^ b')⁻¹) =
      if a = a' ∧ b = b' then ((D₁ * D₂ : ℕ) : K) else 0 := by
  have hsplit : x ^ a * y ^ b * (x ^ a' * y ^ b')⁻¹ =
      (x ^ a * (x ^ a')⁻¹) * (y ^ b * (y ^ b')⁻¹) := by
    rw [mul_inv]; ring
  have hXM : x ^ a * (x ^ a')⁻¹ ∈ fixedField K p m₂ :=
    mul_mem (pow_mem hxM _) (inv_mem (pow_mem hxM _))
  rw [hsplit, relTrace_tower hm, relTrace_pow_quot hXM hη hy hηp hy0 hb hb']
  have houter : relTrace p m₁ D₁ ((D₂ : K) * (x ^ a * (x ^ a')⁻¹)) =
      if a = a' then (D₂ : K) * D₁ else 0 := by
    rw [relTrace_mul_left (natCast_mem_fixedField D₂), ← one_mul (x ^ a * _),
      relTrace_pow_quot (one_mem _) hζ hx hζp hx0 ha ha', mul_ite, mul_one, mul_zero]
  split_ifs with hbb haa haa
  · rw [houter]
    simp only [haa.1, ite_true]
    push_cast; ring
  · rw [houter]
    simp only [show ¬a = a' from fun h => haa ⟨h, hbb⟩, ite_false]
  · exact absurd haa.2 hbb
  · exact relTrace_zero

/-- **Tower basis of two Kummer layers.** Under the hypotheses of `relTrace_tower_quot`,
`β_k = x^(k mod D₁) · y^(k / D₁)` is a relative basis of `K/E` with dual `(D₁ D₂ β_j)⁻¹`. -/
def RelativeBasis.ofTower {m₁ m₂ D₁ D₂ : ℕ} (hm : m₂ = m₁ * D₁) {x ζ y η : K}
    (hxM : x ∈ fixedField K p m₂) (hζ : ζ ∈ fixedField K p m₁) (hx : phi p m₁ 1 x = ζ * x)
    (hζp : IsPrimitiveRoot ζ D₁) (hx0 : x ≠ 0)
    (hη : η ∈ fixedField K p m₂) (hy : phi p m₂ 1 y = η * y)
    (hηp : IsPrimitiveRoot η D₂) (hy0 : y ≠ 0) (hD : ((D₁ * D₂ : ℕ) : K) ≠ 0) :
    RelativeBasis K p m₁ (D₁ * D₂) :=
  RelativeBasis.ofTraceQuot (fun k => x ^ ((k : ℕ) % D₁) * y ^ ((k : ℕ) / D₁)) hD fun i j => by
    have hD₁ : 0 < D₁ := Nat.pos_of_ne_zero (by rintro rfl; simp at hD)
    have hij : i = j ↔ (i : ℕ) % D₁ = (j : ℕ) % D₁ ∧ (i : ℕ) / D₁ = (j : ℕ) / D₁ := by
      refine ⟨fun h => by rw [h]; exact ⟨rfl, rfl⟩, fun ⟨h1, h2⟩ => Fin.ext ?_⟩
      rw [← Nat.mod_add_div (i : ℕ) D₁, ← Nat.mod_add_div (j : ℕ) D₁, h1, h2]
    rw [relTrace_tower_quot hm hxM hζ hx hζp hx0 hη hy hηp hy0 (Nat.mod_lt _ hD₁)
      (Nat.mod_lt _ hD₁) (Nat.div_lt_of_lt_mul i.isLt) (Nat.div_lt_of_lt_mul j.isLt)]
    exact if_congr hij.symm rfl rfl

theorem RelativeBasis.ofTower_β {m₁ m₂ D₁ D₂ : ℕ} (hm : m₂ = m₁ * D₁) {x ζ y η : K}
    (hxM hζ hx hζp hx0 hη hy hηp hy0 hD) (k : Fin (D₁ * D₂)) :
    (RelativeBasis.ofTower (p := p) hm (x := x) (ζ := ζ) (y := y) (η := η)
      hxM hζ hx hζp hx0 hη hy hηp hy0 hD).β k = x ^ ((k : ℕ) % D₁) * y ^ ((k : ℕ) / D₁) := rfl

/-- **Power basis of a two-layer tower.** `E ⊆ M ⊆ K` as in `relTrace_tower_quot`, with a single
generator `y`: `y` is an eigenvector of `φ_M` with a primitive `D₂`-th root `η ∈ M`, and
`y^D₂` is an eigenvector of `φ_E` with a primitive `D₁`-th root `ζ ∈ E`. Then `β_k = y^k` is a
relative basis of `K/E` with dual `(D₁ D₂ y^j)⁻¹`: `y^k = (y^D₂)^(k / D₂) · y^(k mod D₂)`. -/
def RelativeBasis.ofTowerPow {m₁ m₂ D₁ D₂ : ℕ} (hm : m₂ = m₁ * D₁) {ζ y η : K}
    (hζ : ζ ∈ fixedField K p m₁) (hx : phi p m₁ 1 (y ^ D₂) = ζ * y ^ D₂)
    (hζp : IsPrimitiveRoot ζ D₁)
    (hη : η ∈ fixedField K p m₂) (hy : phi p m₂ 1 y = η * y)
    (hηp : IsPrimitiveRoot η D₂) (hy0 : y ≠ 0) (hD : ((D₁ * D₂ : ℕ) : K) ≠ 0) :
    RelativeBasis K p m₁ (D₁ * D₂) :=
  RelativeBasis.ofTraceQuot (fun k => y ^ (k : ℕ)) hD fun i j => by
    have hD₂ : 0 < D₂ := Nat.pos_of_ne_zero (by rintro rfl; simp at hD)
    have hxM : y ^ D₂ ∈ fixedField K p m₂ := by
      rw [mem_fixedField, phi_eigen_pow hy, hηp.pow_eq_one, one_mul]
    have hpow : ∀ k : ℕ, y ^ k = (y ^ D₂) ^ (k / D₂) * y ^ (k % D₂) := fun k => by
      rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    have hdiv : ∀ k : Fin (D₁ * D₂), (k : ℕ) / D₂ < D₁ := fun k =>
      Nat.div_lt_of_lt_mul (lt_of_lt_of_eq k.isLt (mul_comm D₁ D₂))
    have hij : i = j ↔ (i : ℕ) / D₂ = (j : ℕ) / D₂ ∧ (i : ℕ) % D₂ = (j : ℕ) % D₂ := by
      refine ⟨fun h => by rw [h]; exact ⟨rfl, rfl⟩, fun ⟨h1, h2⟩ => Fin.ext ?_⟩
      rw [← Nat.div_add_mod (i : ℕ) D₂, ← Nat.div_add_mod (j : ℕ) D₂, h1, h2]
    rw [hpow i, hpow j, relTrace_tower_quot hm hxM hζ hx hζp (pow_ne_zero _ hy0) hη hy hηp hy0
      (hdiv i) (hdiv j) (Nat.mod_lt _ hD₂) (Nat.mod_lt _ hD₂)]
    exact if_congr hij.symm rfl rfl

theorem RelativeBasis.ofTowerPow_β {m₁ m₂ D₁ D₂ : ℕ} (hm : m₂ = m₁ * D₁) {ζ y η : K}
    (hζ hx hζp hη hy hηp hy0 hD) (k : Fin (D₁ * D₂)) :
    (RelativeBasis.ofTowerPow (p := p) hm (ζ := ζ) (y := y) (η := η)
      hζ hx hζp hη hy hηp hy0 hD).β k = y ^ (k : ℕ) := rfl

/-- **Power basis of a binomial root.** For `x^D = c` with `c ∈ E` and `c ≠ 0`,
`p^m = D t + 1`, and `c^t` a primitive `D`-th root of unity: `β_i = x^i` with dual
`(D x^j)⁻¹`. -/
def RelativeBasis.ofBinomialRoot {x c : K} {t : ℕ} (hxc : x ^ D = c)
    (hc : c ∈ fixedField K p m) (hc0 : c ≠ 0) (hq : p ^ m = D * t + 1)
    (hprim : IsPrimitiveRoot (c ^ t) D) (hD : (D : K) ≠ 0) : RelativeBasis K p m D :=
  RelativeBasis.ofEigen (pow_mem hc t) (phi_one_of_pow_eq hxc hq) hprim
    (fun h => hc0 (by rw [← hxc, h, zero_pow (by rintro rfl; simp at hD)])) hD

theorem RelativeBasis.ofBinomialRoot_β {x c : K} {t : ℕ} (hxc : x ^ D = c) (hc hc0 hq hprim hD)
    (i : Fin D) :
    (RelativeBasis.ofBinomialRoot (p := p) (m := m) (t := t) hxc hc hc0 hq hprim hD).β i =
      x ^ (i : ℕ) := rfl

end GordieHowe.RelativePacking
