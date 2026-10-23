-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Native.Fields.FalconNative20Relative
public import GordieHowe.Foundations.Algebra.RelativeBasisChange
public import GordieHowe.ProofSystem.RingSwitching.StageAlgebra

@[expose] public section

/-!
# The packing tree `F_q < F_q^4 < F_q^20` of `FalconNativeField20`

The bases of the two packing stages of a two-level domain over
`K = F_q[u]/(u^4 − 11)[v]/(v^5 − (u + 2))`, `q = 12289` (domain A of `Falcon512.Ring.Native.QROMParams`,
`lib/gordiehowe/examples/rings/falcon_ring.h`; the packing edges of its realized program `GF(p^1) < GF(p^4) < F_q^20`):

* `φ_{q^4}` has order `5` on `K` (`RelFrobeniusOrder FalconNativeField20 12289 4 5`).
* **The inner stage** `F_q < M = F_{q^4}` (`falconInnerStageBasis`, a `StageBasis` with top `M`):
  the C++ power basis of the first generator among the candidates (`stage.h`, `power_basis`; the
  candidates are `SubfieldInfo`'s basis of `M`, the traces `Tr_{K/M}(u^i) = 5 u^i`, so the
  generator is `5 + 5u`): `β_i = (5 + 5u)^i` (`falconInnerStageBasis_β`), a change of the
  eigenbasis `u^i` (`RelativeBasis.ofEigen`, `u^q = ζ u`) by the matrix `5^i C(i, l)`
  (`RelativeBasis.change`).
* **The root stage** `M < K` (`falconRootBasis`): the C++ generator among `ExtensionBasis`'s
  coordinate basis `u^i v^j` is `1 + v` (`1 + u^i` lies in `M`), so `β_j = (1 + v)^j`
  (`falconRootBasis_β`), a change of the eigenbasis `v^j` (`v^(q^4) = η v`) by the binomial matrix.

The trace-dual bases are the unique ones, so they agree with the C++'s Gauss–Jordan duals.
-/

namespace GordieHowe

open RelativePacking PackingStage

instance : RelFrobeniusOrder FalconNativeField20 12289 4 5 :=
  .of_card (by rw [falconNativeField20_card]) (by norm_num)

/-- `11^((q − 1)/4)` lies in `F_q`. -/
theorem eleven_pow_mem_fixedField :
    (11 : FalconNativeField20) ^ ((12289 - 1) / 4) ∈ fixedField FalconNativeField20 12289 1 := by
  rw [← map_ofNat (algebraMap (ZMod 12289) FalconNativeField20)]
  exact pow_mem (algebraMap_mem_fixedField_one _) _

/-- **The eigenbasis of `M` over `F_q`**: `u^i`, `u^q = 11^((q − 1)/4) u` with a primitive `4`th
root of unity (`RelativeBasis.ofEigen`). -/
def falconQuarticEigenBasis : RelativeBasis FalconNativeField20 12289 1 4 :=
  RelativeBasis.ofEigen eleven_pow_mem_fixedField phi_falconUTower
    (by
      rw [← map_ofNat (algebraMap (ZMod 12289) FalconNativeField20), ← map_pow]
      exact isPrimitiveRoot_eleven_pow_falconQ_sub_one_div_four.map_of_injective
        injective_algebraMap_falconNativeField20)
    falconUTower_ne_zero (falconNativeField20_natCast_ne_zero (by norm_num) (by norm_num))

/-- **The eigenbasis of `K` over `M`**: `v^j`, `v^(q^4) = η v` with `η = (u + 2)^((q^4 − 1)/5)` a
primitive `5`th root of unity (`RelativeBasis.ofEigen`). -/
def falconQuinticEigenBasis : RelativeBasis FalconNativeField20 12289 4 5 :=
  RelativeBasis.ofEigen (algebraMap_falconQuartic_mem_fixedField _) phi_falconV
    (isPrimitiveRoot_falconU_add_two_pow.map_of_injective
      (algebraMap FalconQuartic FalconNativeField20).injective)
    falconV_ne_zero (falconNativeField20_natCast_ne_zero (by norm_num) (by norm_num))

/-! ### The change matrices -/

/-- The matrix `5^i C(i, l)` over `F_q`: `(5 + 5u)^i = Σ_l 5^i C(i, l) u^l`. -/
def innerChange : Fin 4 → Fin 4 → ZMod 12289 :=
  ![![1, 0, 0, 0], ![5, 5, 0, 0], ![25, 50, 25, 0], ![125, 375, 375, 125]]

/-- The inverse of `innerChange`: `(−1)^(l + j) C(l, j) 5^(−j)`. -/
def innerChangeInv : Fin 4 → Fin 4 → ZMod 12289 :=
  ![![1, 0, 0, 0], ![12288, 2458, 0, 0], ![1, 7373, 7865, 0], ![12288, 7374, 983, 1573]]

theorem innerChange_mul_inv (i j : Fin 4) :
    ∑ l, innerChange i l * innerChangeInv l j = if i = j then 1 else 0 := by
  revert i j
  decide

/-- The binomial matrix `C(j, l)` over `F_q`: `(1 + v)^j = Σ_l C(j, l) v^l`. -/
def rootChange : Fin 5 → Fin 5 → ZMod 12289 :=
  ![![1, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 2, 1, 0, 0], ![1, 3, 3, 1, 0], ![1, 4, 6, 4, 1]]

/-- The inverse of `rootChange`: `(−1)^(l + j) C(l, j)`. -/
def rootChangeInv : Fin 5 → Fin 5 → ZMod 12289 :=
  ![![1, 0, 0, 0, 0], ![12288, 1, 0, 0, 0], ![1, 12287, 1, 0, 0], ![12288, 3, 12286, 1, 0],
    ![1, 12285, 6, 12285, 1]]

theorem rootChange_mul_inv (i j : Fin 5) :
    ∑ l, rootChange i l * rootChangeInv l j = if i = j then 1 else 0 := by
  revert i j
  decide

/-- An `F_q`-matrix identity in `K`. -/
theorem map_change_mul_inv {D : ℕ} {a a' : Fin D → Fin D → ZMod 12289}
    (h : ∀ i j, ∑ l, a i l * a' l j = if i = j then 1 else 0) (i j : Fin D) :
    ∑ l, algebraMap (ZMod 12289) FalconNativeField20 (a i l) *
      algebraMap (ZMod 12289) FalconNativeField20 (a' l j) = if i = j then 1 else 0 := by
  simp_rw [← map_mul, ← map_sum, h i j]
  split_ifs <;> simp

/-- An element of `F_q` lies in every `F_{q^m}`. -/
theorem algebraMap_mem_fixedField (m : ℕ) (a : ZMod 12289) :
    algebraMap (ZMod 12289) FalconNativeField20 a ∈ fixedField FalconNativeField20 12289 m := by
  simpa only [one_mul] using mem_fixedField_mul (algebraMap_mem_fixedField_one a) m

/-! ### The stage bases -/

/-- **The inner stage's basis** `F_q < M` (`stage.h`, `power_basis`): `β_i = (5 + 5u)^i`
(`falconInnerStageBasis_β`), the change of the eigenbasis by `innerChange`; top `M`, the fixed
field of `x ↦ x^(q^4)`. -/
def falconInnerStageBasis : StageBasis FalconNativeField20 12289 1 4 where
  toRelativeBasis := falconQuarticEigenBasis.change
    (fun i l => algebraMap (ZMod 12289) FalconNativeField20 (innerChange i l))
    (fun l j => algebraMap (ZMod 12289) FalconNativeField20 (innerChangeInv l j))
    (fun _ _ => algebraMap_mem_fixedField_one _) (fun _ _ => algebraMap_mem_fixedField_one _)
    (map_change_mul_inv innerChange_mul_inv)
  top := fixedField FalconNativeField20 12289 4
  top_fixed y hy := by
    rw [mem_fixedField, phi_def, mul_one] at hy
    rw [phi_def, one_mul]
    exact hy
  base_le _ hx := by simpa only [one_mul] using mem_fixedField_mul hx 4
  β_mem i := Subfield.sum_mem _ fun l _ => mul_mem (algebraMap_mem_fixedField 4 _)
    (pow_mem (algebraMap_falconQuartic_mem_fixedField falconU) _)
  dual_mem j := Subfield.sum_mem _ fun l _ => mul_mem (algebraMap_mem_fixedField 4 _)
    (inv_mem (mul_mem (natCast_mem _ _)
      (pow_mem (algebraMap_falconQuartic_mem_fixedField falconU) _)))

theorem falconInnerStageBasis_top :
    falconInnerStageBasis.top = fixedField FalconNativeField20 12289 4 :=
  rfl

/-- **The inner stage's basis is the C++ power basis** of `5 + 5u`. -/
theorem falconInnerStageBasis_β (i : Fin 4) :
    falconInnerStageBasis.β i = (5 + 5 * falconUTower) ^ (i : ℕ) := by
  change ∑ l, algebraMap (ZMod 12289) FalconNativeField20 (innerChange i l) *
    falconUTower ^ (l : ℕ) = _
  fin_cases i <;> simp [Fin.sum_univ_four, innerChange, map_ofNat] <;> ring

/-- **The root stage's relative basis** `M < K` (`stage.h`, `power_basis`): `β_j = (1 + v)^j`
(`falconRootBasis_β`), the change of the eigenbasis by the binomial matrix. -/
def falconRootBasis : RelativeBasis FalconNativeField20 12289 4 5 :=
  falconQuinticEigenBasis.change
    (fun i l => algebraMap (ZMod 12289) FalconNativeField20 (rootChange i l))
    (fun l j => algebraMap (ZMod 12289) FalconNativeField20 (rootChangeInv l j))
    (fun _ _ => algebraMap_mem_fixedField 4 _) (fun _ _ => algebraMap_mem_fixedField 4 _)
    (map_change_mul_inv rootChange_mul_inv)

/-- **The root stage's basis is the C++ power basis** of `1 + v`. -/
theorem falconRootBasis_β (j : Fin 5) : falconRootBasis.β j = (1 + falconV) ^ (j : ℕ) := by
  change ∑ l, algebraMap (ZMod 12289) FalconNativeField20 (rootChange j l) * falconV ^ (l : ℕ) = _
  fin_cases j <;> simp [Fin.sum_univ_five, rootChange, map_ofNat] <;> ring

end GordieHowe
