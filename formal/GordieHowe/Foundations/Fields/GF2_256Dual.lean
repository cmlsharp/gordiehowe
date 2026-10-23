-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Fields.GF2_256Selection
public import GordieHowe.ProofSystem.RingSwitching.PackedClaim

@[expose] public section

/-!
# The packing basis of `GF(2²⁵⁶)` and its trace-dual basis

`gf2_256PackedBasis` is the `PackedClaim.PackedBasis GF2_256 4` of the packed bit
witnesses of the batched-Keccak H circuit: the sixteen-bit subfield `gf2_256Subfield`,
the basis `β i = g ^ i` the C++ packs with (`beta_[i] = g^i`,
`lib/gf2k/gf2_256.h:119-123`), and the trace-dual basis `β*` of `β` for
`Tr x = ∑_{k < 16} x ^ 2^k`, which gives the decode `bit_i(p) = Tr(β*_i · p)`.

`β*_i = ∑_k C_ik β_k`, where the rows of `C`, the bit masks `gf2_256DualCoeff`, are the
inverse of the `16 × 16` trace matrix `Tr(β_i β_j)` over `GF(2)`, computed offline. So
`β*_i` lies in the subfield by construction, and the duality
`Tr(β*_i β_j) = δ_ij` for all `256` pairs is one `decide +kernel` computation on the
spread representation (`gf2_256DualN_trace`: `256` products and traces, about `40 000`
field multiplications).
-/

namespace GordieHowe

open BinarySpread

/-- `g ^ m` as a spread natural, for `m < 32`. -/
def gf2_256SubfieldPowN (m : ℕ) : ℕ := gf2_256Exec.pow 5 m (gf2_256Exec.ofBits gf2_256SubfieldGenN)

theorem canon_gf2_256SubfieldPowN {m : ℕ} (hm : m < 32) :
    Canon gf2_256Exec (gf2_256SubfieldPowN m) :=
  gf2_256Rep.canon_pow (Rep.canon_ofBits _) 5 m hm

theorem gf2_256Val_subfieldPowN {m : ℕ} (hm : m < 32) :
    valVia gf2_256RingEquiv gf2_256Exec (gf2_256SubfieldPowN m) = gf2_256SubfieldGen ^ m := by
  rw [gf2_256SubfieldPowN, gf2_256Rep.valVia_pow gf2_256RingEquiv (Rep.canon_ofBits _) hm, gf2_256Val_subfieldGen]

/-- Row `i` of the inverse of the trace matrix `Tr(β_i β_j)` over `GF(2)`, bit `k` the
coefficient of `β_k` in `β*_i`. -/
def gf2_256DualCoeff : Fin 16 → ℕ :=
  ![0xb901, 0xe514, 0x728a, 0x8044, 0x4022, 0x9910, 0x4c88, 0x2644, 0xaa23, 0x5584, 0x2ac2,
    0x1561, 0x0a25, 0x0587, 0x0256, 0x012b]

/-- `β*_i = ∑_k C_ik β_k` as a spread natural. -/
def gf2_256DualN (i : Fin 16) : ℕ :=
  gf2_256Exec.sum 16 fun k => if (gf2_256DualCoeff i).testBit k then gf2_256SubfieldPowN k else 0

/-- `Tr(β*_i β_j) = δ_ij`. -/
theorem gf2_256DualN_trace : ∀ i j : Fin 16,
    gf2_256Exec.trace 1 16 (gf2_256Exec.mul (gf2_256DualN i) (gf2_256SubfieldPowN j)) =
      if i = j then gf2_256Exec.ofBits 1 else 0 := by
  decide +kernel

/-- The trace-dual basis `β*` of `gf2_256SubfieldBasis`. -/
def gf2_256DualBasis (i : Fin 16) : GF2_256 :=
  ∑ k : Fin 16, if (gf2_256DualCoeff i).testBit k then gf2_256SubfieldBasis k else 0

theorem gf2_256DualBasis_mem (i : Fin 16) : gf2_256DualBasis i ∈ gf2_256Subfield := by
  refine gf2_256Subfield.sum_mem fun k _ => ?_
  split_ifs
  · exact gf2_256SubfieldBasis_mem k
  · exact gf2_256Subfield.zero_mem

theorem canon_gf2_256DualN (i : Fin 16) : Canon gf2_256Exec (gf2_256DualN i) :=
  gf2_256Rep.canon_sum _ _ fun k =>
    Rep.canon_ite _ (canon_gf2_256SubfieldPowN (by omega)) Rep.canon_zero

theorem gf2_256Val_dualN (i : Fin 16) :
    valVia gf2_256RingEquiv gf2_256Exec (gf2_256DualN i) = gf2_256DualBasis i := by
  rw [gf2_256DualN, gf2_256Rep.valVia_sum gf2_256RingEquiv _ _ fun k =>
    Rep.canon_ite _ (canon_gf2_256SubfieldPowN (by omega)) Rep.canon_zero]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [gf2_256Rep.valVia_ite gf2_256RingEquiv, gf2_256Val_subfieldPowN (by omega), gf2_256Rep.valVia_zero gf2_256RingEquiv, gf2_256SubfieldBasis]

/-- `Exec.trace 1 16` computes `PackedClaim.trace 4`. -/
theorem gf2_256Val_trace16 {y : ℕ} (hy : Canon gf2_256Exec y) :
    valVia gf2_256RingEquiv gf2_256Exec (gf2_256Exec.trace 1 16 y) =
      PackedClaim.trace 4 (valVia gf2_256RingEquiv gf2_256Exec y) := by
  rw [gf2_256Rep.valVia_trace gf2_256RingEquiv 1 hy 16]
  simp only [one_mul]
  rfl

theorem trace_gf2_256DualBasis_mul (i j : Fin 16) :
    PackedClaim.trace 4 (gf2_256DualBasis i * gf2_256SubfieldBasis j) = if i = j then 1 else 0 := by
  have hj : Canon gf2_256Exec (gf2_256SubfieldPowN j) := canon_gf2_256SubfieldPowN (by omega)
  have hm := gf2_256Rep.canon_mul (canon_gf2_256DualN i) hj
  have h := congrArg (valVia gf2_256RingEquiv gf2_256Exec) (gf2_256DualN_trace i j)
  rw [gf2_256Val_trace16 hm, gf2_256Rep.valVia_mul gf2_256RingEquiv (canon_gf2_256DualN i) hj, gf2_256Val_dualN,
    gf2_256Val_subfieldPowN (by omega), gf2_256Rep.valVia_ite gf2_256RingEquiv, gf2_256Val_ofBits, gf2_256OfNat_one,
    gf2_256Rep.valVia_zero gf2_256RingEquiv] at h
  exact h

/-- The packing data of `GF(2²⁵⁶)`: the sixteen-bit subfield, the basis `β i = g ^ i`
(`beta_`, `lib/gf2k/gf2_256.h:119-123`) and its trace-dual basis. -/
def gf2_256PackedBasis : PackedClaim.PackedBasis GF2_256 4 where
  E := gf2_256Subfield
  fixed _ hx := mem_gf2_256Subfield.mp hx
  β := gf2_256SubfieldBasis
  β_mem := gf2_256SubfieldBasis_mem
  βdual := gf2_256DualBasis
  βdual_mem := gf2_256DualBasis_mem
  dual := trace_gf2_256DualBasis_mul

/-- The selection subfield is the packing subfield. -/
theorem gf2_256SelectionField_E_le : gf2_256SelectionField.E ≤ gf2_256PackedBasis.E :=
  le_rfl

end GordieHowe
