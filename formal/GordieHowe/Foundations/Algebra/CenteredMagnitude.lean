-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Algebra.CharP.Basic
public import GordieHowe.Applications.Spec.Centered

@[expose] public section

/-!
# Centering a field sign equation

`GordieHowe.Falcon512.NativeNorm.square` pins each coefficient to the field value `±mag` directly
(`v * v = mag * mag`, giving `v = mag ∨ v = -mag` in a field), unlike the emulated norm's two-root
product form `(a - v) * (a - (q - v)) = 0` (`GordieHowe.Falcon512.EmulatedNorm.centered_le_of_centering`). This file
makes the same centering step from that different starting equation: from a sign choice between
casts of a natural at most the field's characteristic, extract the natural residue and bound its
centered representative by that natural, with equality when the natural is at most half the
characteristic.
-/

namespace GordieHowe.Centered

variable {K : Type*} [Field K] {q : ℕ} [NeZero q] [CharP K q]

omit [NeZero q] in
/-- A field value equal to `±` the cast of a natural at most the
characteristic `q` is the cast of a residue whose centered representative is
bounded by that natural. -/
theorem exists_cast_centered_le {magNat : ℕ} (hmag : magNat ≤ q)
    {v : K} (hv : v = (magNat : K) ∨ v = -(magNat : K)) :
    ∃ vals : ℕ, vals ≤ q ∧ (vals : K) = v ∧
      (LatticeCrypto.centeredRepr (vals : ZMod q)).natAbs ≤ magNat := by
  rcases hv with h | h
  · exact ⟨magNat, hmag, h.symm, Centered.natAbs_centeredRepr_natCast_le q magNat⟩
  · refine ⟨q - magNat, Nat.sub_le q magNat, ?_, ?_⟩
    · rw [h, Nat.cast_sub hmag, CharP.cast_eq_zero]
      ring
    · have hcast : ((q - magNat : ℕ) : ZMod q) = -(magNat : ZMod q) := by
        rw [Nat.cast_sub hmag]
        simp
      rw [hcast, LatticeCrypto.centeredRepr_natAbs_neg]
      exact Centered.natAbs_centeredRepr_natCast_le q magNat

omit [NeZero q] in
/-- **The converse direction: every residue's cast is `±` its own centered magnitude's cast.**
Unlike `exists_cast_centered_le`/`exists_cast_centered_eq` (which start from a sign equation and
produce a residue), this starts from an arbitrary natural and reads off the sign directly from
`LatticeCrypto.centeredRepr`'s own integer sign, via the unique ring homomorphism `ZMod q →+* K`
that `CharP K q` gives. No bound on the natural is needed: `centeredRepr` already reduces its
argument mod `q`. -/
theorem cast_eq_centeredRepr_natAbs (n : ℕ) :
    (n : K) = ((LatticeCrypto.centeredRepr (n : ZMod q)).natAbs : K) ∨
      (n : K) = -((LatticeCrypto.centeredRepr (n : ZMod q)).natAbs : K) := by
  set φ : ZMod q →+* K := ZMod.castHom (dvd_refl q) K with hφdef
  set z : ℤ := LatticeCrypto.centeredRepr (n : ZMod q) with hzdef
  have h2 : φ (n : ZMod q) = (n : K) := map_natCast φ n
  have h3 : (n : ZMod q) = ((z : ℤ) : ZMod q) := LatticeCrypto.centeredRepr_intCast (n : ZMod q)
  have hφz : φ ((z : ℤ) : ZMod q) = (z : K) := map_intCast φ z
  have hφn : (n : K) = (z : K) := by rw [← h2, h3, hφz]
  rcases Int.natAbs_eq z with h | h
  · left
    have step : ((z : ℤ) : K) = ((z.natAbs : ℤ) : K) := congrArg (fun w : ℤ => (w : K)) h
    rw [Int.cast_natCast] at step
    rw [hφn, step]
  · right
    have step : ((z : ℤ) : K) = ((-(z.natAbs : ℤ) : ℤ) : K) := congrArg (fun w : ℤ => (w : K)) h
    rw [Int.cast_neg, Int.cast_natCast] at step
    rw [hφn, step]

/-- When the natural is at most half the characteristic, centering is exact:
the centered representative's absolute value equals the natural itself. -/
theorem exists_cast_centered_eq {magNat : ℕ} (hmag : (magNat : ℤ) ≤ (q : ℤ) / 2)
    {v : K} (hv : v = (magNat : K) ∨ v = -(magNat : K)) :
    ∃ vals : ℕ, vals ≤ q ∧ (vals : K) = v ∧
      (LatticeCrypto.centeredRepr (vals : ZMod q)).natAbs = magNat := by
  have hqpos : 0 < q := NeZero.pos q
  have hlt : magNat < q := by omega
  have hvalcast : (ZMod.val ((magNat : ℕ) : ZMod q)) = magNat := ZMod.val_natCast_of_lt hlt
  have hval : LatticeCrypto.centeredRepr ((magNat : ℕ) : ZMod q) = (magNat : ℤ) := by
    have hle := LatticeCrypto.centeredRepr_of_le
      (x := ((magNat : ℕ) : ZMod q)) (by rw [hvalcast]; exact_mod_cast hmag)
    rwa [hvalcast] at hle
  have hnatAbs : (LatticeCrypto.centeredRepr ((magNat : ℕ) : ZMod q)).natAbs = magNat := by
    rw [hval]
    exact Int.natAbs_natCast magNat
  rcases hv with h | h
  · exact ⟨magNat, hlt.le, h.symm, hnatAbs⟩
  · refine ⟨q - magNat, Nat.sub_le q magNat, ?_, ?_⟩
    · rw [h, Nat.cast_sub hlt.le, CharP.cast_eq_zero]
      ring
    · have hcast : ((q - magNat : ℕ) : ZMod q) = -((magNat : ℕ) : ZMod q) := by
        rw [Nat.cast_sub hlt.le]
        simp
      rw [hcast, LatticeCrypto.centeredRepr_natAbs_neg]
      exact hnatAbs

end GordieHowe.Centered
