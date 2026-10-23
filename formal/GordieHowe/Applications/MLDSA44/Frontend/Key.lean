-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Spec.NTT
public import GordieHowe.Language.RealizedProgram.Ops
public import GordieHowe.Applications.Params
public import Mathlib.Algebra.Field.ZMod

@[expose] public section

/-!
# The ML-DSA NTT is the program's scheme-order transform

The statement of an ML-DSA program holds `Â = ExpandA(ρ)` as the vendored NTT spectra (the C++
`fill_public_key`), and the program's `signature.relation` reads each entry through the program's
inverse transform at `ψ = ζ = 1753` (`polyMatVec … (ntt 1753)`: `Ops.inverseNtt 256 ψ`). In
`ZMod q`:

* coefficient `m` of the vendored `ntt f` is the value of `f` at `ζ^(2·br₈(m) + 1)`
  (`GordieHowe.MLDSA44.NTTEval.ntt_get`), that is the program's scheme-order transform `Ops.nttScheme 256 ζ`
  (`ofFin_ntt`);
* so the program's inverse transform of a spectrum is the vendored `invNTT` (`inverseNtt_spectrum`, by
  `Ops.inverseNtt_nttScheme`).
-/

namespace GordieHowe.MLDSA44.KeyNTT

open GordieHowe.RealizedProgram

instance instFactPrimeModulus_pQ : Fact (Nat.Prime _root_.MLDSA.modulus) := instFactPrimeMlDsaQ

/-- **The vendored NTT is the program's scheme-order transform** at `ζ`. -/
theorem ofFin_ntt (f : _root_.MLDSA.Rq) :
    Ops.ofFin (fun m : Fin 256 => (_root_.MLDSA.Concrete.ntt f).coeffs.get m) =
      Ops.nttScheme 256 _root_.MLDSA.zeta (Ops.ofFin fun j : Fin 256 => f.get j) := by
  funext m
  by_cases hm : m < 256
  · rw [Ops.ofFin_of_lt _ hm]
    refine (MLDSA44.NTTEval.ntt_get f ⟨m, hm⟩).trans ?_
    rw [Ops.nttScheme_apply (k := 8) (by norm_num) _ _ hm]
    have hb : bitRevNat 8 m = _root_.MLDSA.Concrete.bitRev8 ((⟨m, hm⟩ : Fin 256) : ℕ) :=
      (bitRev_val 8 ⟨m, hm⟩).symm.trans (bitRev_eight ⟨m, hm⟩)
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hb]
    erw [Ops.ofFin_of_lt _ j.isLt]
  · rw [Ops.ofFin, dif_neg hm]
    unfold Ops.nttScheme
    rw [if_neg hm]

/-- **The program's inverse transform of a spectrum is the vendored `invNTT`.** -/
theorem inverseNtt_spectrum (fHat : _root_.MLDSA.Tq) {i : ℕ} (hi : i < 256) :
    Ops.inverseNtt 256 _root_.MLDSA.zeta (Ops.ofFin fun m : Fin 256 => fHat.coeffs.get m) i =
      (_root_.MLDSA.Concrete.invNTT fHat).get ⟨i, hi⟩ := by
  conv_lhs => rw [← _root_.MLDSA.Concrete.ntt_invNTT fHat]
  rw [ofFin_ntt, Ops.inverseNtt_nttScheme (k := 8) (by norm_num)
    _root_.MLDSA.Concrete.zeta_isPrimitiveRoot (by decide) _ hi, Ops.ofFin_of_lt _ hi]
  rfl

end GordieHowe.MLDSA44.KeyNTT
