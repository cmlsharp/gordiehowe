-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.FieldTheory.Finite.Extension
public import Mathlib.Data.Nat.PrimeFin

@[expose] public section

/-!
# Rabin's irreducibility test over a finite field

A polynomial `f` of degree `n ≥ 1` over a finite field `k` with `q` elements is
irreducible when `f ∣ X^(q^n) - X` and `f` is coprime to `X^(q^(n/r)) - X` for
every prime `r ∣ n`. Every irreducible factor `g` of `f` then has degree
dividing `n` (Mathlib's `Irreducible.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X`),
and a proper divisor of `n` divides some `n / r`, which would make `g` a common
factor of `f` and `X^(q^(n/r)) - X`.

`irreducible_of_root_pow_card_pow` restates the test in `AdjoinRoot f`, where
both conditions are identities that a certificate can check: the root is fixed
by the `q^n`-power map, and `root^(q^(n/r)) - root` is a unit.

Candidate for upstreaming next to `Mathlib.FieldTheory.Finite.Extension`.
-/

open Polynomial

/-- A proper divisor `d` of a nonzero `n` divides `n / r` for some prime factor
`r` of `n`: take `r` the least prime factor of `n / d`. -/
theorem Nat.exists_mem_primeFactors_dvd_div {d n : ℕ} (hdn : d ∣ n) (hlt : d < n) (hn : n ≠ 0) :
    ∃ r ∈ n.primeFactors, d ∣ n / r := by
  obtain ⟨m, rfl⟩ := hdn
  have hm1 : m ≠ 1 := by
    rintro rfl
    simp at hlt
  obtain ⟨t, ht⟩ := Nat.minFac_dvd m
  have hr := Nat.minFac_prime hm1
  refine ⟨m.minFac, Nat.mem_primeFactors.mpr ⟨hr, Dvd.dvd.mul_left (Nat.minFac_dvd m) d, hn⟩,
    t, Nat.div_eq_of_eq_mul_left hr.pos ?_⟩
  nth_rw 1 [ht]
  ring

/-- `f` is coprime to `g` when `g` is a unit modulo `f`. -/
theorem AdjoinRoot.isCoprime_of_isUnit_mk {R : Type*} [CommRing R] {f g : R[X]}
    (h : IsUnit (AdjoinRoot.mk f g)) : IsCoprime f g := by
  obtain ⟨v, hv⟩ := h.exists_left_inv
  obtain ⟨u, rfl⟩ := AdjoinRoot.mk_surjective v
  rw [← map_mul, ← sub_eq_zero, ← map_one (AdjoinRoot.mk f), ← map_sub,
    AdjoinRoot.mk_eq_zero] at hv
  obtain ⟨c, hc⟩ := hv
  exact ⟨-c, u, by linear_combination hc⟩

/-- Rabin's irreducibility test. `f` of degree `n ≠ 0` over a finite field `k`
is irreducible if it divides `X^(q^n) - X` and is coprime to `X^(q^(n/r)) - X`
for each prime factor `r` of `n`, where `q = Nat.card k`. -/
theorem Polynomial.irreducible_of_dvd_X_pow_card_pow_sub_X {k : Type*} [Field k] [Finite k]
    {f : k[X]} {n : ℕ} (hdeg : f.natDegree = n) (hn : n ≠ 0) (hdvd : f ∣ X ^ Nat.card k ^ n - X)
    (hcop : ∀ r ∈ n.primeFactors, IsCoprime f (X ^ Nat.card k ^ (n / r) - X)) :
    Irreducible f := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp [← hdeg] at hn
  have hfu : ¬IsUnit f := fun hu => hn (hdeg ▸ natDegree_eq_zero_of_isUnit hu)
  obtain ⟨g, hg, hgf⟩ := WfDvdMonoid.exists_irreducible_factor hfu hf0
  have hgn : g.natDegree ∣ n := hg.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X (hgf.trans hdvd)
  rcases (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hgn).lt_or_eq with hlt | heq
  · obtain ⟨r, hr, hgr⟩ := Nat.exists_mem_primeFactors_dvd_div hgn hlt hn
    exact absurd ((hcop r hr).isUnit_of_dvd' hgf
      ((hg.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X).mp hgr)) hg.not_isUnit
  · exact (associated_of_dvd_of_natDegree_le hgf hf0 (hdeg ▸ heq.ge)).irreducible hg

/-- Rabin's irreducibility test in `AdjoinRoot f`: `f` of degree `n ≠ 0` over a
finite field `k` with `q = Nat.card k` elements is irreducible if
`root f ^ q^n = root f` and `root f ^ q^(n/r) - root f` is a unit for each
prime factor `r` of `n`. -/
theorem Polynomial.irreducible_of_root_pow_card_pow {k : Type*} [Field k] [Finite k]
    {f : k[X]} {n : ℕ} (hdeg : f.natDegree = n) (hn : n ≠ 0)
    (hroot : AdjoinRoot.root f ^ Nat.card k ^ n = AdjoinRoot.root f)
    (hunit : ∀ r ∈ n.primeFactors,
      IsUnit (AdjoinRoot.root f ^ Nat.card k ^ (n / r) - AdjoinRoot.root f)) :
    Irreducible f := by
  refine irreducible_of_dvd_X_pow_card_pow_sub_X hdeg hn ?_ fun r hr => ?_
  · rw [← AdjoinRoot.mk_eq_zero, map_sub, map_pow, AdjoinRoot.mk_X, hroot, sub_self]
  · refine AdjoinRoot.isCoprime_of_isUnit_mk ?_
    rw [map_sub, map_pow, AdjoinRoot.mk_X]
    exact hunit r hr
