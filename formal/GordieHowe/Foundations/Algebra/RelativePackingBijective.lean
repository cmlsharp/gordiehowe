-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Algebra.RelativePacking
public import Mathlib.FieldTheory.Fixed
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.ZMod.QuotientGroup

@[expose] public section

/-!
# Relative packing is a bijection from `E^D` onto `K`

For a finite field `K` with the relative Frobenius `φ(x) = x^(p^m)` of order dividing `D`
(`RelFrobeniusOrder K p m D`) and a relative basis `B` (`RelativeBasis`), packing `D`
coordinates of the fixed field `E` (`packSub`, the `pack` of `RelativePacking` on
`E`-valued coordinates) is a bijection `E^D → K` (`packSub_bijective`).

* Injective: `coord_pack` inverts it.
* Onto: `[K : E] ≤ D`. The powers of `φ`, as ring automorphisms of `K`, form a group
  `G` of order dividing `D` (`card_phiGroup_le`) whose fixed field is `E`
  (`fixedPoints_phiGroup`), and Artin's bound `[K : K^G] ≤ |G|`
  (`FixedPoints.finrank_le_card`) gives `|K| = |E|^[K:E] ≤ |E|^D = |E^D|`.

This is the fact the zero-knowledge argument of relative packing uses: the reveal
`M_k = c + Σ_i β_i μ[k,i]` under uniform subfield masks `μ[k, ·]` is uniform over `K`
(the bijection is the hypothesis of `GordieHowe.MaskKit.subfield`).
-/

namespace GordieHowe.RelativePacking

variable {K : Type} [Field K] [Fintype K] {p m D : ℕ} [ExpChar K p]

variable (K p m) in
/-- The relative Frobenius `φ` as a ring automorphism of the finite field `K`. -/
noncomputable def phiEquiv : K ≃+* K :=
  RingEquiv.ofBijective (iterateFrobenius K p m)
    (Finite.injective_iff_bijective.mp (iterateFrobenius K p m).injective)

theorem phiEquiv_apply (x : K) : phiEquiv K p m x = phi p m 1 x := by
  simp [phiEquiv, phi_def, iterateFrobenius_def]

theorem phiEquiv_pow_apply (k : ℕ) (x : K) : (phiEquiv K p m ^ k) x = phi p m k x := by
  induction k with
  | zero => simp [phi_def]
  | succ k ih =>
    rw [pow_succ']
    change phiEquiv K p m ((phiEquiv K p m ^ k) x) = _
    rw [ih]
    rw [phiEquiv_apply, phi_phi, Nat.add_comm]

variable [RelFrobeniusOrder K p m D]

variable (K p m D) in
theorem phiEquiv_pow_order : phiEquiv K p m ^ D = 1 := by
  ext x
  rw [phiEquiv_pow_apply, phi_order]
  rfl

instance instFiniteRingEquiv_pQ : Finite (K ≃+* K) := Finite.of_injective _ DFunLike.coe_injective

variable (K p m) in
/-- The group of powers of `φ`. -/
noncomputable abbrev phiGroup : Subgroup (K ≃+* K) := Subgroup.zpowers (phiEquiv K p m)

noncomputable instance : Fintype (phiGroup K p m) := Fintype.ofFinite _


variable (K p m D) in
/-- The group of powers of `φ` has at most `D` elements. -/
theorem card_phiGroup_le : Fintype.card (phiGroup K p m) ≤ D := by
  rw [← Nat.card_eq_fintype_card, Nat.card_zpowers]
  exact orderOf_le_of_pow_eq_one (RelFrobeniusOrder.pos K p m) (phiEquiv_pow_order K p m D)

omit [RelFrobeniusOrder K p m D] in
variable (K p m) in
/-- The fixed field of the powers of `φ` is the fixed field of `φ`. -/
theorem fixedPoints_phiGroup :
    FixedPoints.subfield (phiGroup K p m) K = fixedField K p m := by
  have hfin : IsOfFinOrder (phiEquiv K p m) := isOfFinOrder_of_finite _
  ext x
  change (∀ g : phiGroup K p m, g • x = x) ↔ x ∈ fixedField K p m
  constructor
  · intro h
    rw [mem_fixedField]
    have := h ⟨phiEquiv K p m, Subgroup.mem_zpowers _⟩
    rw [← phiEquiv_pow_apply, pow_one]
    exact this
  · intro hx g
    obtain ⟨k, hk⟩ := hfin.mem_powers_iff_mem_zpowers.mpr g.2
    change (g : K ≃+* K) x = x
    rw [← hk, phiEquiv_pow_apply, phi_of_mem hx]

variable (K p m D) in
/-- **`|K| ≤ |E|^D`**: the degree of `K` over the fixed field `E` of `φ` is at most `D`. -/
theorem card_le_fixedField_pow : Nat.card K ≤ Nat.card (fixedField K p m) ^ D := by
  have hfr := FixedPoints.finrank_le_card (phiGroup K p m) K
  have hcard := Module.natCard_eq_pow_finrank (K := FixedPoints.subfield (phiGroup K p m) K)
    (V := K)
  have hE : Nat.card (FixedPoints.subfield (phiGroup K p m) K) =
      Nat.card (fixedField K p m) := by
    rw [fixedPoints_phiGroup K p m]
  have hpos : 0 < Nat.card (FixedPoints.subfield (phiGroup K p m) K) := Nat.card_pos
  rw [hcard, ← hE]
  exact Nat.pow_le_pow_right hpos (hfr.trans (card_phiGroup_le K p m D))

omit [Fintype K] [RelFrobeniusOrder K p m D] in
/-- Packing `E`-valued coordinates: `Σ_i β_i · c_i`. -/
def packSub (B : RelativeBasis K p m D) (c : Fin D → fixedField K p m) : K :=
  pack B fun i => c i

omit [Fintype K] [RelFrobeniusOrder K p m D] in
theorem packSub_injective (B : RelativeBasis K p m D) : Function.Injective (packSub B) := by
  intro c c' h
  funext i
  apply Subtype.ext
  have h1 := coord_pack B (c := fun i => (c i : K)) (fun i => (c i).2) i
  have h2 := coord_pack B (c := fun i => (c' i : K)) (fun i => (c' i).2) i
  change coord B (packSub B c) i = _ at h1
  change coord B (packSub B c') i = _ at h2
  rw [← h1, ← h2, h]

/-- **Packing is a bijection from `E^D` onto `K`**: injective by `coord_pack`, and
`|K| ≤ |E|^D` (`card_le_fixedField_pow`). -/
theorem packSub_bijective (B : RelativeBasis K p m D) : Function.Bijective (packSub B) :=
  (packSub_injective B).bijective_of_nat_card_le (by
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin D), Fintype.card_fin]
    exact card_le_fixedField_pow K p m D)

end GordieHowe.RelativePacking
