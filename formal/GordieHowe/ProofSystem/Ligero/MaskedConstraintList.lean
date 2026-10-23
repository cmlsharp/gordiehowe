-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Ligero.MaskedConstraintFamily
public import GordieHowe.Foundations.ReedSolomon.PolynomialAgreementList
public import GordieHowe.Foundations.ReedSolomon.BerlekampWelch

@[expose] public section

/-!
# Masked constraint testing against a list of high-agreement polynomials

A fixed arbitrary mask oracle can have several high-agreement low-degree
polynomials. Each contributes one affine cancellation event. Outside their
union, every response passing the scalar check agrees on at most the selected
threshold, giving the exact distinct-query falling-factorial bound.
-/
namespace GordieHowe.Ligero.MaskedConstraintList
open Polynomial MaskedConstraintTest
open scoped Classical
variable {F : Type} [Field F] {N n m : ℕ}

namespace FiniteList

/-- The mask candidate list is fixed before the coefficient challenge. -/
def BadChallenge (candidates : Finset F[X])
    (check : F[X] →ₗ[F] F) (g : Fin n → F[X]) (target : Fin n → F)
    (r : Fin n → F) : Prop :=
  ∃ f ∈ candidates, AffineBatching.value (check f) (MaskedConstraintTest.residual check g target) r = 0

/-- The list union costs at most one field-sized affine event per candidate. -/
theorem badChallenge_count [Fintype F] (candidates : Finset F[X])
    (check : F[X] →ₗ[F] F) (g : Fin n → F[X]) (target : Fin n → F)
    (hne : ∃ i, check (g i) ≠ target i) :
    (Finset.univ.filter (BadChallenge candidates check g target)).card * Fintype.card F ≤
      candidates.card * Fintype.card F ^ n := by
  have hr : ∃ i, MaskedConstraintTest.residual check g target i ≠ 0 := by
    simpa [MaskedConstraintTest.residual, sub_ne_zero] using hne
  induction candidates using Finset.induction_on with
  | empty => simp [BadChallenge]
  | @insert f fs hf ih =>
    have hu : Finset.univ.filter (BadChallenge (insert f fs) check g target) =
        (Finset.univ.filter fun r => AffineBatching.value (check f) (MaskedConstraintTest.residual check g target) r = 0) ∪
        Finset.univ.filter (BadChallenge fs check g target) := by
      ext r
      simp [BadChallenge]
    rw [hu, Finset.card_insert_of_notMem hf, Nat.add_mul]
    apply (Nat.mul_le_mul_right _ (Finset.card_union_le _ _)).trans
    rw [Nat.add_mul]
    have h := AffineBatching.card_zeros_mul_card_le (check f) hr
    omega

/-- A valid scalar response cannot shift to any listed mask candidate outside
its affine bad event. This is pure linear algebra, independent of list size. -/
theorem shifted_not_mem (candidates : Finset F[X])
    (check : F[X] →ₗ[F] F) (g : Fin n → F[X]) (target : Fin n → F)
    (r : Fin n → F) (hbad : ¬ BadChallenge candidates check g target r)
    (p : F[X]) (hcheck : check p = ∑ i, r i * target i) :
    p - batch g r ∉ candidates := by
  intro hp
  apply hbad
  refine ⟨p - batch g r, hp, ?_⟩
  simp only [AffineBatching.value, MaskedConstraintTest.residual, map_sub, check_batch, hcheck,
    mul_sub, Finset.sum_sub_distrib]
  ring

/-- Generic finite-list lemma. The completeness premise is discharged by
membership in the constructed high-agreement list in the public wrappers. -/
theorem agreement_le_of_complete (C : GordieHowe.RSCode F N) (u : Fin N → F)
    (a : ℕ) (candidates : Finset F[X])
    (hcomplete : ∀ f, f.natDegree < C.k → a < (MaskedPolynomialTest.agreement C u f).card →
      f ∈ candidates)
    (check : F[X] →ₗ[F] F) (g : Fin n → F[X])
    (hg : ∀ i, (g i).natDegree < C.k) (target : Fin n → F)
    (r : Fin n → F) (hbad : ¬ BadChallenge candidates check g target r)
    (p : F[X]) (hp : p.natDegree < C.k) (hcheck : check p = ∑ i, r i * target i) :
    (MaskedPolynomialTest.agreement C u (p - batch g r)).card ≤ a := by
  by_contra h
  exact shifted_not_mem candidates check g target r hbad p hcheck
    (hcomplete _ (shifted_degree C g hg r p hp) (Nat.lt_of_not_ge h))

/-- The exact count for ordered distinct samples, without a power-ratio loss. -/
theorem query_count_of_complete (C : GordieHowe.RSCode F N) (u : Fin N → F)
    (a : ℕ) (candidates : Finset F[X])
    (hcomplete : ∀ f, f.natDegree < C.k → a < (MaskedPolynomialTest.agreement C u f).card →
      f ∈ candidates)
    (check : F[X] →ₗ[F] F) (g : Fin n → F[X])
    (hg : ∀ i, (g i).natDegree < C.k) (target : Fin n → F)
    (r : Fin n → F) (hbad : ¬ BadChallenge candidates check g target r)
    (p : F[X]) (hp : p.natDegree < C.k) (hcheck : check p = ∑ i, r i * target i) (t : ℕ) :
    (Finset.univ.filter fun q : Fin t ↪ Fin N =>
      ∀ s, u (q s) + (batch g r).eval (C.D (q s)) = p.eval (C.D (q s))).card ≤
        a.descFactorial t := by
  have he := Fintype.card_embedding_filter_mem (t := t)
    (MaskedPolynomialTest.agreement C u (p - batch g r))
  simp only [MaskedPolynomialTest.agreement, Finset.mem_filter, Finset.mem_univ, true_and,
    Polynomial.eval_sub, eq_sub_iff_add_eq] at he
  rw [he]
  apply Nat.descFactorial_le t
  simpa only [MaskedPolynomialTest.agreement, Polynomial.eval_sub, eq_sub_iff_add_eq] using
    agreement_le_of_complete C u a candidates hcomplete check g hg target r hbad p hp hcheck

/-- A family selects one violated check using only the fixed source system. -/
def FamilyBadChallenge (candidates : Finset F[X])
    (check : Fin m → (F[X] →ₗ[F] F)) (g : Fin n → F[X])
    (target : Fin m → Fin n → F) (r : Fin n → F) : Prop :=
  if hfalse : ¬ MaskedConstraintFamily.Claim check g target then
    BadChallenge candidates (check (MaskedConstraintFamily.chosenCheck check g target hfalse)) g
      (target (MaskedConstraintFamily.chosenCheck check g target hfalse)) r
  else False

theorem family_badChallenge_count [Fintype F] (candidates : Finset F[X])
    (check : Fin m → (F[X] →ₗ[F] F)) (g : Fin n → F[X]) (target : Fin m → Fin n → F) :
    (Finset.univ.filter (FamilyBadChallenge candidates check g target)).card * Fintype.card F ≤
      candidates.card * Fintype.card F ^ n := by
  change (Finset.univ.filter (fun r => FamilyBadChallenge candidates check g target r)).card *
    Fintype.card F ≤ candidates.card * Fintype.card F ^ n
  by_cases hfalse : ¬ MaskedConstraintFamily.Claim check g target
  · simpa only [FamilyBadChallenge, dite_eq_left hfalse] using
      badChallenge_count candidates
        (check (MaskedConstraintFamily.chosenCheck check g target hfalse)) g
        (target (MaskedConstraintFamily.chosenCheck check g target hfalse))
        (MaskedConstraintFamily.chosenCheck_violated check g target hfalse)
  · simp [FamilyBadChallenge, hfalse]

theorem family_query_count_of_complete (C : GordieHowe.RSCode F N) (u : Fin N → F)
    (a : ℕ) (candidates : Finset F[X])
    (hcomplete : ∀ f, f.natDegree < C.k → a < (MaskedPolynomialTest.agreement C u f).card →
      f ∈ candidates)
    (check : Fin m → (F[X] →ₗ[F] F)) (g : Fin n → F[X])
    (hg : ∀ i, (g i).natDegree < C.k) (target : Fin m → Fin n → F)
    (hfalse : ¬ MaskedConstraintFamily.Claim check g target)
    (r : Fin n → F) (hbad : ¬ FamilyBadChallenge candidates check g target r)
    (p : F[X]) (hp : p.natDegree < C.k)
    (hcheck : ∀ j, check j p = ∑ i, r i * target j i) (t : ℕ) :
    (Finset.univ.filter fun q : Fin t ↪ Fin N =>
      ∀ s, u (q s) + (batch g r).eval (C.D (q s)) = p.eval (C.D (q s))).card ≤
        a.descFactorial t := by
  have hb : ¬ BadChallenge candidates
      (check (MaskedConstraintFamily.chosenCheck check g target hfalse)) g
      (target (MaskedConstraintFamily.chosenCheck check g target hfalse)) r := by
    simpa only [FamilyBadChallenge, dite_eq_left hfalse] using hbad
  exact query_count_of_complete C u a candidates hcomplete
    (check (MaskedConstraintFamily.chosenCheck check g target hfalse)) g hg
    (target (MaskedConstraintFamily.chosenCheck check g target hfalse)) r hb p hp
    (hcheck (MaskedConstraintFamily.chosenCheck check g target hfalse)) t

/-- **The column count of one check at a pinned mask**: for a mask polynomial `m`, sources `g` and
a response `p`, all of degree `< d`, at distinct points `x`, outside the cancellation event at `m`
(`BadChallenge {m}`), a response passing the scalar check passes the column identity
`m + batch g r = p` on at most `(d − 1).descFactorial t` samples of `t` distinct columns. -/
theorem pinned_query_count {x : Fin N → F} (hx : Function.Injective x) {d : ℕ} {m : F[X]}
    (hm : m.natDegree < d) (check : F[X] →ₗ[F] F) {g : Fin n → F[X]}
    (hg : ∀ i, (g i).natDegree < d) (target : Fin n → F) {r : Fin n → F}
    (hbad : ¬ BadChallenge {m} check g target r) {p : F[X]}
    (hp : p.natDegree < d) (hcheck : check p = ∑ i, r i * target i) (t : ℕ) :
    (Finset.univ.filter fun q : Fin t ↪ Fin N => ∀ s,
      m.eval (x (q s)) + (batch g r).eval (x (q s)) = p.eval (x (q s))).card ≤
      (d - 1).descFactorial t := by
  set f := p - batch g r - m
  have hf : f ≠ 0 := by
    intro h0
    apply shifted_not_mem {m} check g target r hbad p hcheck
    rw [Finset.mem_singleton]
    exact sub_eq_zero.mp h0
  have hd : 0 < d := by omega
  have hdeg : f.natDegree < d := (natDegree_sub_le _ _).trans_lt
    (max_lt ((natDegree_sub_le _ _).trans_lt (max_lt hp (natDegree_batch_lt hd hg r))) hm)
  have hZ : (Finset.univ.filter fun j => f.eval (x j) = 0).card ≤ d - 1 :=
    (RSCode.BerlekampWelch.card_filter_eval_eq_zero_le hx hf).trans (by omega)
  refine le_trans (Finset.card_le_card fun q hq => ?_)
    ((Fintype.card_embedding_filter_mem _).trans_le (Nat.descFactorial_le t hZ))
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
  intro s
  simp only [f, eval_sub, ← hq s]
  ring

/-- **The column count of a family of checks at a pinned mask**: as `pinned_query_count`, for
the check selected from a false family claim (`FamilyBadChallenge {m}`). -/
theorem pinned_family_query_count {m' : ℕ} {x : Fin N → F} (hx : Function.Injective x) {d : ℕ}
    {m : F[X]} (hm : m.natDegree < d) (check : Fin m' → (F[X] →ₗ[F] F)) {g : Fin n → F[X]}
    (hg : ∀ i, (g i).natDegree < d) (target : Fin m' → Fin n → F)
    (hfalse : ¬ MaskedConstraintFamily.Claim check g target) {r : Fin n → F}
    (hbad : ¬ FamilyBadChallenge {m} check g target r) {p : F[X]}
    (hp : p.natDegree < d) (hcheck : ∀ j, check j p = ∑ i, r i * target j i) (t : ℕ) :
    (Finset.univ.filter fun q : Fin t ↪ Fin N => ∀ s,
      m.eval (x (q s)) + (batch g r).eval (x (q s)) = p.eval (x (q s))).card ≤
      (d - 1).descFactorial t := by
  have hb : ¬ BadChallenge {m}
      (check (MaskedConstraintFamily.chosenCheck check g target hfalse)) g
      (target (MaskedConstraintFamily.chosenCheck check g target hfalse)) r := by
    simpa only [FamilyBadChallenge, dite_eq_left hfalse] using hbad
  exact pinned_query_count hx hm _ hg _ hb hp
    (hcheck (MaskedConstraintFamily.chosenCheck check g target hfalse)) t

end FiniteList
/-- Johnson incidence bound, with strict agreement threshold `a`. -/
def listBound (N d a : ℕ) : ℕ := N * (a + 1 - d) / ((a + 1)^2 - N*d)

/-- The least agreement threshold `a` with `d·(N − 1) ≤ a·(a + 1)`: the integer square root of
`d·(N − 1)`, raised by one when it falls short. At this threshold `listBound N d a ≤ N`
(`listBound_le_of_le_mul`). -/
def johnsonAgreement (N d : ℕ) : ℕ :=
  if d * (N - 1) ≤ Nat.sqrt (d * (N - 1)) * (Nat.sqrt (d * (N - 1)) + 1) then
    Nat.sqrt (d * (N - 1))
  else Nat.sqrt (d * (N - 1)) + 1

/-- `johnsonAgreement N d` meets the defining inequality. -/
theorem le_johnsonAgreement_mul (N d : ℕ) :
    d * (N - 1) ≤ johnsonAgreement N d * (johnsonAgreement N d + 1) := by
  unfold johnsonAgreement
  split_ifs with h
  · exact h
  · have := Nat.lt_succ_sqrt (d * (N - 1))
    nlinarith

/-- `johnsonAgreement N d` is the least threshold meeting the defining inequality. -/
theorem johnsonAgreement_le {N d b : ℕ} (hb : d * (N - 1) ≤ b * (b + 1)) :
    johnsonAgreement N d ≤ b := by
  have hs := Nat.sqrt_le (d * (N - 1))
  unfold johnsonAgreement
  split_ifs with h
  · by_contra hlt
    rw [not_le] at hlt
    have : b * (b + 1) < Nat.sqrt (d * (N - 1)) * Nat.sqrt (d * (N - 1)) := by
      nlinarith
    omega
  · by_contra hlt
    rw [not_le] at hlt
    have : b * (b + 1) ≤ Nat.sqrt (d * (N - 1)) * (Nat.sqrt (d * (N - 1)) + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega

/-- `johnsonAgreement N d = a` from the two defining inequalities at `a`. -/
theorem johnsonAgreement_eq {N d a : ℕ} (h : d * (N - 1) ≤ a * (a + 1))
    (hmin : (a - 1) * a < d * (N - 1)) : johnsonAgreement N d = a := by
  have hle := johnsonAgreement_le h
  by_contra hne
  have hlt : johnsonAgreement N d + 1 ≤ a := by omega
  have := le_johnsonAgreement_mul N d
  have : johnsonAgreement N d * (johnsonAgreement N d + 1) ≤ (a - 1) * a :=
    Nat.mul_le_mul (by omega) hlt
  omega

/-- A threshold meeting `d·(N − 1) ≤ a·(a + 1)` has list bound at most `N`. -/
theorem listBound_le_of_le_mul {N d a : ℕ} (hN : 1 ≤ N) (h : d * (N - 1) ≤ a * (a + 1)) :
    listBound N d a ≤ N := by
  unfold listBound
  apply Nat.div_le_of_le_mul
  rw [mul_comm _ N]
  apply Nat.mul_le_mul_left
  have hsq : (a + 1) ^ 2 = a * (a + 1) + (a + 1) := by ring
  have hNd : N * d = d * (N - 1) + d := by
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  omega

variable [Fintype F]

/-- All degree-bounded polynomials agreeing on more than `a` columns. -/
noncomputable def candidates (C : GordieHowe.RSCode F N) (a : ℕ) (u : Fin N → F) : Finset F[X] :=
  PolynomialAgreementList.candidates C.D (C.k-1) a u

theorem candidates_complete (C : GordieHowe.RSCode F N) (a : ℕ) (u : Fin N → F)
    (f : F[X]) (hf : f.natDegree < C.k)
    (ha : a < (MaskedPolynomialTest.agreement C u f).card) : f ∈ candidates C a u := by
  apply (PolynomialAgreementList.mem_candidates C.D (C.k-1) a u f).mpr
  constructor
  · omega
  · simpa only [PolynomialAgreementList.agreements, MaskedPolynomialTest.agreement, eq_comm] using ha

/-- **A bad challenge of the masked constraint test**: `FiniteList.BadChallenge` over the list of
candidate codewords near `u` (`candidates C a u`). -/
def BadChallenge (C : GordieHowe.RSCode F N) (a : ℕ) (u : Fin N → F)
    (check : F[X] →ₗ[F] F) (g : Fin n → F[X]) (target : Fin n → F) (r : Fin n → F) : Prop :=
  FiniteList.BadChallenge (candidates C a u) check g target r

/-- **A bad challenge of a family of masked constraint tests**: `FiniteList.FamilyBadChallenge`
over the candidate codewords near `u` (`candidates C a u`). -/
def FamilyBadChallenge (C : GordieHowe.RSCode F N) (a : ℕ) (u : Fin N → F)
    (check : Fin m → (F[X] →ₗ[F] F)) (g : Fin n → F[X])
    (target : Fin m → Fin n → F) (r : Fin n → F) : Prop :=
  FiniteList.FamilyBadChallenge (candidates C a u) check g target r

/-- The candidate list bound follows from polynomial root intersections and
incidence counting. `hA` and `hJ` are only fixed numerical parameter facts. -/
theorem candidates_card_le (C : GordieHowe.RSCode F N) (a : ℕ) (u : Fin N → F)
    (hA : a+1 ≤ N) (hJ : N*(C.k-1) < (a+1)^2) :
    (candidates C a u).card ≤ listBound N (C.k-1) a := by
  exact PolynomialAgreementList.card_candidates_le C.D C.D_injective (C.k-1) a u hA hJ

/-- The first challenge costs at most `listBound/|F|`, uniformly over the
arbitrary committed mask oracle. -/
theorem badChallenge_count (C : GordieHowe.RSCode F N) (a : ℕ) (u : Fin N → F)
    (check : F[X] →ₗ[F] F) (g : Fin n → F[X]) (target : Fin n → F)
    (hne : ∃ i, check (g i) ≠ target i)
    (hA : a+1 ≤ N) (hJ : N*(C.k-1) < (a+1)^2) :
    (Finset.univ.filter (BadChallenge C a u check g target)).card * Fintype.card F ≤
      listBound N (C.k-1) a * Fintype.card F ^ n :=
  (FiniteList.badChallenge_count (candidates C a u) check g target hne).trans
    (Nat.mul_le_mul_right _ (candidates_card_le C a u hA hJ))

theorem family_badChallenge_count (C : GordieHowe.RSCode F N) (a : ℕ) (u : Fin N → F)
    (check : Fin m → (F[X] →ₗ[F] F)) (g : Fin n → F[X]) (target : Fin m → Fin n → F)
    (hA : a+1 ≤ N) (hJ : N*(C.k-1) < (a+1)^2) :
    (Finset.univ.filter (FamilyBadChallenge C a u check g target)).card * Fintype.card F ≤
      listBound N (C.k-1) a * Fintype.card F ^ n :=
  (FiniteList.family_badChallenge_count (candidates C a u) check g target).trans
    (Nat.mul_le_mul_right _ (candidates_card_le C a u hA hJ))

/-- An arbitrary valid response outside the list cancellation event has at
most the exact falling-factorial number of accepting distinct query tuples. -/
theorem query_count (C : GordieHowe.RSCode F N) (a : ℕ) (u : Fin N → F)
    (check : F[X] →ₗ[F] F) (g : Fin n → F[X])
    (hg : ∀ i, (g i).natDegree < C.k) (target : Fin n → F)
    (r : Fin n → F) (hbad : ¬ BadChallenge C a u check g target r)
    (p : F[X]) (hp : p.natDegree < C.k) (hcheck : check p = ∑ i, r i * target i) (t : ℕ) :
    (Finset.univ.filter fun q : Fin t ↪ Fin N =>
      ∀ s, u (q s) + (batch g r).eval (C.D (q s)) = p.eval (C.D (q s))).card ≤
        a.descFactorial t :=
  FiniteList.query_count_of_complete C u a (candidates C a u) (candidates_complete C a u)
    check g hg target r hbad p hp hcheck t

/-- Selecting one violated source functional avoids an extra factor for the
number of scalar checks, even though all use the same response and mask. -/
theorem family_query_count (C : GordieHowe.RSCode F N) (a : ℕ) (u : Fin N → F)
    (check : Fin m → (F[X] →ₗ[F] F)) (g : Fin n → F[X])
    (hg : ∀ i, (g i).natDegree < C.k) (target : Fin m → Fin n → F)
    (hfalse : ¬ MaskedConstraintFamily.Claim check g target)
    (r : Fin n → F) (hbad : ¬ FamilyBadChallenge C a u check g target r)
    (p : F[X]) (hp : p.natDegree < C.k)
    (hcheck : ∀ j, check j p = ∑ i, r i * target j i) (t : ℕ) :
    (Finset.univ.filter fun q : Fin t ↪ Fin N =>
      ∀ s, u (q s) + (batch g r).eval (C.D (q s)) = p.eval (C.D (q s))).card ≤
        a.descFactorial t :=
  FiniteList.family_query_count_of_complete C u a (candidates C a u) (candidates_complete C a u)
    check g hg target hfalse r hbad p hp hcheck t

end GordieHowe.Ligero.MaskedConstraintList
