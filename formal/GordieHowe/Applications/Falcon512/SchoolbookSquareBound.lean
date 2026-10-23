-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Data.Nat.ModEq
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The Falcon-512 native norm's per-coefficient square lower bound

A coefficient's magnitude is committed in three base-`64` digits `x0, x1, x2`; its schoolbook square
is committed as six digits `d0..d5` with five two-limb (base-`64²`) carries `C0..C4`, via the column
identities `GordieHowe.Falcon512.NativeNorm.square` asserts. Those identities hold only in the field `ZMod 12289`, so
a column equation is an exact identity on the naturals only where both sides are known to lie below
the characteristic; here that holds unconditionally for columns `2..5` (after already knowing digit
`d5 = 0` and `d4 ≤ 2` from the represented total being at most `β² = 34034726`, which pins the
carries `C3, C4` small enough), but columns `0` and `1` may still wrap by a nonnegative multiple of
the characteristic. This lemma is the resulting inequality: the represented total is at least the
squared magnitude, `t ≥ mag²`. It is pure integer arithmetic, independent of the field or gadget, so
it is proved once here, at the committed parameters (base `64`, characteristic `12289`, bound
`34034726`), and applied to the field equations by `GordieHowe.Falcon512.NativeNorm.square_lower_bound`.
-/

namespace GordieHowe

theorem schoolbook_square_lower_bound
    {x0 x1 x2 d0 d1 d2 d3 d4 d5 C0 C1 C2 C3 C4 : ℕ}
    (hx0 : x0 < 64) (hx1 : x1 < 64) (hx2 : x2 < 64)
    (hd0 : d0 < 64) (hd1 : d1 < 64) (hd2 : d2 < 64) (hd3 : d3 < 64) (hd4 : d4 < 64) (hd5 : d5 < 64)
    (hC0 : C0 < 4096) (hC1 : C1 < 4096) (hC2 : C2 < 4096) (hC3 : C3 < 4096) (hC4 : C4 < 4096)
    (hcol0 : Nat.ModEq 12289 (d0 + 64 * C0) (x0 * x0))
    (hcol1 : Nat.ModEq 12289 (d1 + 64 * C1) (2 * x0 * x1 + C0))
    (hcol2 : Nat.ModEq 12289 (d2 + 64 * C2) (2 * x0 * x2 + x1 * x1 + C1))
    (hcol3 : Nat.ModEq 12289 (d3 + 64 * C3) (2 * x1 * x2 + C2))
    (hcol4 : Nat.ModEq 12289 (d4 + 64 * C4) (x2 * x2 + C3))
    (hcol5 : Nat.ModEq 12289 d5 C4)
    (ht : d0 + 64 * d1 + 64 ^ 2 * d2 + 64 ^ 3 * d3 + 64 ^ 4 * d4 + 64 ^ 5 * d5 ≤ 34034726) :
    (x0 + 64 * x1 + 4096 * x2) ^ 2 ≤
      d0 + 64 * d1 + 64 ^ 2 * d2 + 64 ^ 3 * d3 + 64 ^ 4 * d4 + 64 ^ 5 * d5 := by
  simp only [Nat.ModEq] at hcol0 hcol1 hcol2 hcol3 hcol4 hcol5
  -- Digit position: `d5 = 0` and `d4 ≤ 2`, else the represented total alone
  -- would already exceed `β²`.
  have hd5_0 : d5 = 0 := by omega
  have hd4_2 : d4 ≤ 2 := by omega
  -- Column 5 is unconditionally exact (both sides trivially below `12289`),
  -- pinning the top carry `C4 = 0`.
  have hC4_0 : C4 = 0 := by omega
  -- Column 4 is exact once `C4 = 0` is substituted; its left side, bounded by
  -- the digit bounds alone, cannot wrap. This pins `x2 ≤ 1`, `C3 ≤ 2`.
  have hxx2 : x2 * x2 ≤ 63 * 63 := Nat.mul_le_mul (by omega) (by omega)
  have hR4 : x2 * x2 + C3 < 12289 := by omega
  have heq4 : d4 = x2 * x2 + C3 := by omega
  have hx2_1 : x2 ≤ 1 := by
    by_contra hcon
    have h2 : 2 ≤ x2 := by omega
    have : 2 * 2 ≤ x2 * x2 := Nat.mul_le_mul h2 h2
    omega
  have hC3_2 : C3 ≤ 2 := by omega
  -- Column 3 is exact given `x2 ≤ 1`, `C3 ≤ 2`.
  have hx1x2 : x1 * x2 ≤ 63 * 1 := Nat.mul_le_mul (by omega) hx2_1
  have hR3 : 2 * x1 * x2 + C2 < 12289 := by
    have : 2 * x1 * x2 = 2 * (x1 * x2) := by ring
    omega
  have heq3 : d3 + 64 * C3 = 2 * x1 * x2 + C2 := by omega
  have hC2_bound : C2 ≤ 191 := by omega
  -- Column 2 is exact given `x2 ≤ 1` and the tighter bound on `C2` just won.
  have hx0x2 : x0 * x2 ≤ 63 * 1 := Nat.mul_le_mul (by omega) hx2_1
  have hx1x1 : x1 * x1 ≤ 63 * 63 := Nat.mul_le_mul (by omega) (by omega)
  have hR2 : 2 * x0 * x2 + x1 * x1 + C1 < 12289 := by
    have : 2 * x0 * x2 = 2 * (x0 * x2) := by ring
    omega
  have heq2 : d2 + 64 * C2 = 2 * x0 * x2 + x1 * x1 + C1 := by omega
  -- Columns 1 and 0 have no established bound on the incoming carry, so they
  -- may wrap: the right side (below `12289`) and the left side differ by a
  -- nonnegative multiple of the characteristic.
  have hx0x1 : x0 * x1 ≤ 63 * 63 := Nat.mul_le_mul (by omega) (by omega)
  have hR1 : 2 * x0 * x1 + C0 < 12289 := by
    have : 2 * x0 * x1 = 2 * (x0 * x1) := by ring
    omega
  obtain ⟨k1, hk1⟩ : ∃ k1, d1 + 64 * C1 = 2 * x0 * x1 + C0 + 12289 * k1 :=
    ⟨(d1 + 64 * C1) / 12289, by omega⟩
  have hxx0 : x0 * x0 < 12289 := by
    have : x0 * x0 ≤ 63 * 63 := Nat.mul_le_mul (by omega) (by omega)
    omega
  obtain ⟨k0, hk0⟩ : ∃ k0, d0 + 64 * C0 = x0 * x0 + 12289 * k0 :=
    ⟨(d0 + 64 * C0) / 12289, by omega⟩
  -- Telescoping: weight each column identity by `64^m` and sum; every carry
  -- cancels, leaving `t = mag² + 12289 * (k0 + 64 * k1)`.
  have hexpand : (x0 + 64 * x1 + 4096 * x2) ^ 2 =
      x0 * x0 + 128 * (x0 * x1) + 8192 * (x0 * x2) + 4096 * (x1 * x1) +
        524288 * (x1 * x2) + 16777216 * (x2 * x2) := by ring
  have hkey : d0 + 64 * d1 + 64 ^ 2 * d2 + 64 ^ 3 * d3 + 64 ^ 4 * d4 + 64 ^ 5 * d5 =
      (x0 * x0 + 128 * (x0 * x1) + 8192 * (x0 * x2) + 4096 * (x1 * x1) +
        524288 * (x1 * x2) + 16777216 * (x2 * x2)) + 12289 * (k0 + 64 * k1) := by
    have h2x0x1 : 2 * x0 * x1 = 2 * (x0 * x1) := by ring
    have h2x0x2 : 2 * x0 * x2 = 2 * (x0 * x2) := by ring
    have h2x1x2 : 2 * x1 * x2 = 2 * (x1 * x2) := by ring
    omega
  rw [hexpand, hkey]
  omega

end GordieHowe
