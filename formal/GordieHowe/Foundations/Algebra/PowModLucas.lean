-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.NumberTheory.LucasPrimality
public import GordieHowe.Foundations.Algebra.PowMod

@[expose] public section

/-!
# Lucas certificates by `powMod`

A Lucas certificate of a prime `p` (Mathlib's `lucas_primality`) is a witness `a` with
`a ^ (p − 1) = 1` and `a ^ ((p − 1) / q) ≠ 1` for every prime factor `q` of `p − 1`. Given the
factorization of `p − 1` as a list `fs` of primes (with multiplicity), the arithmetic part of the
certificate is one Boolean test (`lucasCheckB`): the product of `fs` is `p − 1`, and the
exponentiations by `powMod` (`GordieHowe/Foundations/Algebra/PowMod.lean`). The kernel decides it
by `decide +kernel`; the primality of the factors is the caller's (`norm_num` for small factors, a
Lucas certificate of their own for large ones, which together make a Pratt certificate).
-/

namespace GordieHowe

/-- **The arithmetic of a Lucas certificate**: the list `fs` multiplies to `p − 1`,
`a ^ (p − 1) ≡ 1 (mod p)`, and `a ^ ((p − 1) / q) ≢ 1 (mod p)` for every `q` in `fs`, the
exponentiations by `powMod`. -/
def lucasCheckB (p a : ℕ) (fs : List ℕ) : Bool :=
  fs.prod == p - 1 && powMod a (p - 1) p == 1 && fs.all fun q => powMod a ((p - 1) / q) p != 1

/-- **A Lucas certificate proves primality** (`lucas_primality`): every prime factor of
`p − 1 = fs.prod` divides a prime of `fs`, so it is one of them. -/
theorem prime_of_lucasCheckB {p a : ℕ} {fs : List ℕ} (hp : 1 < p) (hfs : ∀ q ∈ fs, q.Prime)
    (h : lucasCheckB p a fs = true) : p.Prime := by
  simp only [lucasCheckB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, bne_iff_ne, ne_eq]
    at h
  obtain ⟨⟨hprod, hpow⟩, hord⟩ := h
  refine lucas_primality p (a : ZMod p) (powMod_eq_one_of_eq hpow) fun q hq hdvd => ?_
  rw [← hprod] at hdvd
  obtain ⟨r, hr, hqr⟩ := (Nat.prime_iff.mp hq).dvd_prod_iff.mp hdvd
  rw [(Nat.prime_dvd_prime_iff_eq hq (hfs r hr)).mp hqr]
  exact powMod_ne_one_of_ne hp (hord r hr)

end GordieHowe
