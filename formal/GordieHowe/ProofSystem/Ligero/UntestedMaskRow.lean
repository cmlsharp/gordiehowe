-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Ligero.Tableau
public import GordieHowe.ProofSystem.Ligero.MaskedConstraintList
public import GordieHowe.Headline

@[expose] public section

/-!
# The constraint test of a Ligero tableau against a list of mask polynomials

The arbitrary-mask list argument on given rows `fs` (the rows pinned by the commit phase of
`GordieHowe.Ligero.AgreementThreshold`): all mask candidates, the polynomials of degree `≤ 2k − 2` agreeing with a
mask row on more than `a` columns, are fixed before the test's challenge. Paper `lem:untested-masks`
holds for each test: the linear test (`linearBad`, `linear_bad_count`, `linear_query_count`) and
the quadratic test (`quadBad`, `quad_bad_count`, `quad_query_count`). Ligero uses the test it
selects, the linear test when a linear claim fails and the quadratic test otherwise
(`constraintBad`, `constraint_bad_count`); outside its cancellation event, a valid response passes
the selected family's column identity on at most `a.descFactorial t` query tuples
(`selected_query_count`).
One violated constraint family and one functional are chosen before the challenge, so neither the
number of constraints nor the two masks multiplies the list cost. `Parameters` holds the list
hypotheses on `a` and the list size `l`.
-/

namespace GordieHowe.Ligero.UntestedMaskRow
open IOP

open Polynomial Tableau
open scoped Classical NNReal
section

variable {F : Type} [Field F] [Fintype F] {N R nL nQ nrep : ℕ}
  (C : GordieHowe.RSCode F N) (P : Tableau.Parameters (R := R) (nQ := nQ) C)
  (L : LinearSystem (nL := nL) C P) (hrate : 2 * C.k - 1 ≤ N) (a : ℕ)

/-- Numerical list parameters: these constrain only the fixed code and the
chosen agreement threshold, never a prover's mask or response. -/
structure Parameters (C : GordieHowe.RSCode F N) (a l : ℕ) : Prop where
  agreement_le : a + 1 ≤ N
  johnson : N * (2 * C.k - 2) < (a + 1) ^ 2
  list_le : MaskedConstraintList.listBound N (2 * C.k - 2) a ≤ l

/-- **The Johnson hypothesis bounds the degree**: an agreement threshold `a` with `a + 1 ≤ N`
and `N · d < (a + 1)²` has `d < N`. If `d ≥ a + 1`, then `(a + 1)² ≤ N · (a + 1) ≤ N · d`. -/
theorem rate_of_johnson {N d a : ℕ} (ha : a + 1 ≤ N) (hj : N * d < (a + 1) ^ 2) : d < N := by
  by_contra h
  have h1 : (a + 1) ^ 2 ≤ N * (a + 1) := by
    rw [sq]
    exact Nat.mul_le_mul_right _ ha
  have h2 : N * (a + 1) ≤ N * d := Nat.mul_le_mul_left _ (by omega)
  omega

omit [Fintype F] in
/-- The list hypotheses give the rate condition `2k − 1 ≤ N` that the mask code
`MaskedPolynomialTest.maskCode` needs (`rate_of_johnson` at degree `2k − 2`). -/
theorem Parameters.rate_le {C : GordieHowe.RSCode F N} {a l : ℕ} (B : Parameters C a l) :
    2 * C.k - 1 ≤ N := by
  have := rate_of_johnson B.agreement_le B.johnson
  omega

/-- **The linear test's list event on the rows `fs`** at the mask row `u`: the list cancellation
event of the linear family (`MaskedConstraintList.BadChallenge`) at the linear challenge `r`. -/
def linearBad (fs : Fin (R + 1) → F[X]) (u : Fin N → F) (r : Fin nL → F) : Prop :=
  MaskedConstraintList.BadChallenge (MaskedPolynomialTest.maskCode C hrate) a u
    (dotCheck C P) (dotPolynomials C P L fs) L.target r

/-- **The quadratic test's list event on the rows `fs`** at the mask row `u`: the list
cancellation event of the quadratic family (`MaskedConstraintList.FamilyBadChallenge`) at the
quadratic challenge `r`. -/
def quadBad (fs : Fin (R + 1) → F[X]) (u : Fin N → F) (r : Fin nQ → F) : Prop :=
  MaskedConstraintList.FamilyBadChallenge (MaskedPolynomialTest.maskCode C hrate) a u
    (quadCheck C P) (quadPolynomials C P fs) (fun _ _ => 0) r

/-- **The selected list event on the rows `fs`**: the list cancellation event of the linear
family when the linear checks fail on `fs`, else of the quadratic family. -/
def constraintBad (fs : Fin (R + 1) → F[X]) (u : Aux F N)
    (r : (Fin nL → F) × (Fin nQ → F)) : Prop :=
  if ¬ ∀ l, dotCheck C P (dotPolynomials C P L fs l) = L.target l then
    linearBad C P L hrate a fs u.1 r.1
  else quadBad C P hrate a fs u.2 r.2

/-- **Paper `lem:untested-masks` for the linear test, the column count**: for rows `fs` of degree
`< k`, a mask row `u` and a linear challenge `r` outside the linear list event, every response `w` of degree `< 2k − 1` that passes the linear test's algebraic check
passes its column check on at most `a.descFactorial t` query tuples. -/
@[headline]
theorem linear_query_count {l : ℕ} (B : Parameters C a l) (fs : Fin (R + 1) → F[X])
    (hfs : ∀ row, (fs row).natDegree < C.k) (u : Fin N → F) (r : Fin nL → F)
    (hbad : ¬ linearBad C P L B.rate_le a fs u r) (w : F[X])
    (hw : w.natDegree < 2 * C.k - 1) (hcheck : dotCheck C P w = ∑ l, r l * L.target l) (t : ℕ) :
    (Finset.univ.filter fun q : Query N t => ∀ s, u (q s) +
      (MaskedConstraintTest.batch (dotPolynomials C P L fs) r).eval (C.D (q s)) =
        w.eval (C.D (q s))).card ≤ a.descFactorial t :=
  MaskedConstraintList.query_count (MaskedPolynomialTest.maskCode C B.rate_le) a u (dotCheck C P)
    (dotPolynomials C P L fs) (dot_degree C P L _ hfs) L.target r hbad w hw hcheck t

/-- **Paper `lem:untested-masks` for the quadratic test, the column count**: for rows `fs` of
degree `< k` on which some product constraint fails, a mask row `u` and a quadratic challenge `r`
outside the quadratic list event, every response `w` of degree `< 2k − 1` that passes the
quadratic test's algebraic check passes its column check on at most `a.descFactorial t` query
tuples. -/
@[headline]
theorem quad_query_count {l : ℕ} (B : Parameters C a l) (fs : Fin (R + 1) → F[X])
    (hfs : ∀ row, (fs row).natDegree < C.k) (u : Fin N → F)
    (hfalse : ¬ MaskedConstraintFamily.Claim (quadCheck C P) (quadPolynomials C P fs)
      (fun _ _ => 0))
    (r : Fin nQ → F) (hbad : ¬ quadBad C P B.rate_le a fs u r) (w : F[X])
    (hw : w.natDegree < 2 * C.k - 1) (hcheck : ∀ j, quadCheck C P j w = 0) (t : ℕ) :
    (Finset.univ.filter fun q : Query N t => ∀ s, u (q s) +
      (MaskedConstraintTest.batch (quadPolynomials C P fs) r).eval (C.D (q s)) =
        w.eval (C.D (q s))).card ≤ a.descFactorial t :=
  MaskedConstraintList.family_query_count (MaskedPolynomialTest.maskCode C B.rate_le) a u
    (quadCheck C P) (quadPolynomials C P fs) (quad_degree C P _ hfs) (fun _ _ => 0) hfalse r hbad w
    hw (by simpa using hcheck) t

/-- **The selected column count on given rows**: for rows `fs` of degree `< k` on which the
constraints fail, outside the selected list event, a valid response passes the selected family's
column identity on at most `a.descFactorial t` query tuples (`linear_query_count` when a linear
claim fails, `quad_query_count` otherwise). -/
theorem selected_query_count {l : ℕ} (B : Parameters C a l) (fs : Fin (R + 1) → F[X])
    (hfs : ∀ row, (fs row).natDegree < C.k)
    (u : Aux F N) (hfalse : ¬ Holds C P L fs) (r : Challenge F R nL nQ nrep)
    (hbad : ¬ constraintBad C P L B.rate_le a fs u r.2)
    (p : Response F C.k nrep) (hp : Valid C P L r p) (t : ℕ) :
    (Finset.univ.filter (selectedAccept C P L fs u r p (t := t))).card ≤ a.descFactorial t := by
  change (Finset.univ.filter fun q => selectedAccept C P L fs u r p q).card ≤ _
  by_cases hd : ¬ ∀ l, dotCheck C P (dotPolynomials C P L fs l) = L.target l
  · simp only [selectedAccept, ite_eq_left hd]
    exact linear_query_count C P L a B fs hfs u.1 r.2.1
      (by simpa only [constraintBad, ite_eq_left hd] using hbad) (p.dot C)
      (Response.natDegree_dot_lt C B.rate_le p) hp.1 t
  · simp only [selectedAccept, ite_eq_right hd]
    exact quad_query_count C P a B fs hfs u.2 (fun hq => hfalse ⟨not_not.mp hd, hq⟩) r.2.2
      (by simpa only [constraintBad, ite_eq_right hd] using hbad) (p.quad C)
      (Response.natDegree_quad_lt C B.rate_le p) hp.2 t

theorem count_left {A B : Type} [Fintype A] [Fintype B] (p : A → Prop) :
    (Finset.univ.filter fun r : A × B => p r.1).card =
      (Finset.univ.filter p).card * Fintype.card B := by
  have he : (Finset.univ.filter fun r : A × B => p r.1) =
      (Finset.univ.filter p).product Finset.univ := by ext r; simp
  rw [he]
  exact (Finset.card_product _ _).trans (by rw [Finset.card_univ])

theorem count_right {A B : Type} [Fintype A] [Fintype B] (p : B → Prop) :
    (Finset.univ.filter fun r : A × B => p r.2).card =
      Fintype.card A * (Finset.univ.filter p).card := by
  have he : (Finset.univ.filter fun r : A × B => p r.2) =
      Finset.univ.product (Finset.univ.filter p) := by ext r; simp
  rw [he]
  exact (Finset.card_product _ _).trans (by rw [Finset.card_univ])

omit [Fintype F] in
/-- Under the rate condition `2k − 1 ≤ N`, the Johnson-optimal threshold
`MaskedConstraintList.johnsonAgreement N (2k − 2)` with list size `N` satisfies the list-test
hypotheses. -/
theorem Parameters.of_johnsonAgreement (hrate : 2 * C.k - 1 ≤ N) :
    Parameters C (MaskedConstraintList.johnsonAgreement N (2 * C.k - 2)) N := by
  have hk := C.k_pos
  set d := 2 * C.k - 2
  set a := MaskedConstraintList.johnsonAgreement N d
  have hm : d * (N - 1) ≤ a * (a + 1) := MaskedConstraintList.le_johnsonAgreement_mul N d
  have hda : d ≤ a := by
    by_contra h
    rw [not_le] at h
    have h1 : a * (a + 1) ≤ (d - 1) * d := Nat.mul_le_mul (by omega) (by omega)
    have h2 : (d - 1) * d < d * (N - 1) := by
      rw [mul_comm]
      exact Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
    omega
  have hsq : (a + 1) ^ 2 = a * (a + 1) + (a + 1) := by ring
  have hNd : N * d = d * (N - 1) + d := by
    obtain ⟨n, hn⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    rw [hn, Nat.add_sub_cancel]
    ring
  refine ⟨?_, ?_, MaskedConstraintList.listBound_le_of_le_mul (by omega) hm⟩
  · have : a ≤ N - 1 := MaskedConstraintList.johnsonAgreement_le
      (by rw [mul_comm]; exact Nat.mul_le_mul_left _ (by omega))
    omega
  · show N * d < (a + 1) ^ 2
    omega

variable {l : ℕ} (B : Parameters C a l)

omit [Fintype F] in
theorem mask_degree_sub_one :
    (MaskedPolynomialTest.maskCode C hrate).k - 1 = 2 * C.k - 2 := by
  simp only [MaskedPolynomialTest.maskCode]
  omega

include B in
/-- **Paper `lem:untested-masks` for the linear test, the bad challenges**: for rows `fs` on which
some linear claim fails and every mask row `u`, the linear list event holds on at most an `l / |F|`
fraction of the linear challenges. -/
@[headline]
theorem linear_bad_count (fs : Fin (R + 1) → F[X]) (u : Fin N → F)
    (hfalse : ∃ l, dotCheck C P (dotPolynomials C P L fs l) ≠ L.target l) :
    (Finset.univ.filter (linearBad C P L B.rate_le a fs u)).card * Fintype.card F ≤
      l * Fintype.card (Fin nL → F) := by
  have hrate := B.rate_le
  have hj : N * ((MaskedPolynomialTest.maskCode C hrate).k - 1) < (a + 1) ^ 2 := by
    rw [mask_degree_sub_one]; exact B.johnson
  have hl : MaskedConstraintList.listBound N ((MaskedPolynomialTest.maskCode C hrate).k - 1) a ≤ l := by
    rw [mask_degree_sub_one]; exact B.list_le
  have h := MaskedConstraintList.badChallenge_count (MaskedPolynomialTest.maskCode C hrate) a
    u (dotCheck C P) (dotPolynomials C P L fs) L.target hfalse B.agreement_le hj
  rw [Fintype.card_fun, Fintype.card_fin]
  exact h.trans (Nat.mul_le_mul_right _ hl)

include B in
/-- **Paper `lem:untested-masks` for the quadratic test, the bad challenges**: for all rows `fs`
and every mask row `u`, the quadratic list event holds on at most an `l / |F|` fraction of the
quadratic challenges (it is empty when every product constraint holds). -/
@[headline]
theorem quad_bad_count (fs : Fin (R + 1) → F[X]) (u : Fin N → F) :
    (Finset.univ.filter (quadBad C P B.rate_le a fs u)).card * Fintype.card F ≤
      l * Fintype.card (Fin nQ → F) := by
  have hrate := B.rate_le
  have hj : N * ((MaskedPolynomialTest.maskCode C hrate).k - 1) < (a + 1) ^ 2 := by
    rw [mask_degree_sub_one]; exact B.johnson
  have hl : MaskedConstraintList.listBound N ((MaskedPolynomialTest.maskCode C hrate).k - 1) a ≤ l := by
    rw [mask_degree_sub_one]; exact B.list_le
  have h := MaskedConstraintList.family_badChallenge_count
    (MaskedPolynomialTest.maskCode C hrate) a u (quadCheck C P) (quadPolynomials C P fs)
    (fun _ _ => 0) B.agreement_le hj
  rw [Fintype.card_fun, Fintype.card_fin]
  exact h.trans (Nat.mul_le_mul_right _ hl)

include B in
/-- **The selected list event on given rows** holds on at most an `l / |F|` fraction of the
constraint challenges, for all rows `fs` and masks `u`: the linear test's event
(`linear_bad_count`) when a linear claim fails, the quadratic test's (`quad_bad_count`)
otherwise. -/
theorem constraint_bad_count (fs : Fin (R + 1) → F[X]) (u : Aux F N) :
    (Finset.univ.filter (constraintBad C P L B.rate_le a fs u)).card * Fintype.card F ≤
      l * Fintype.card ((Fin nL → F) × (Fin nQ → F)) := by
  have hrate := B.rate_le
  change (Finset.univ.filter fun r => constraintBad C P L hrate a fs u r).card * _ ≤ _
  by_cases hd : ¬ ∀ l, dotCheck C P (dotPolynomials C P L fs l) = L.target l
  · simp only [constraintBad, ite_eq_left hd]
    rw [count_left, Fintype.card_prod]
    have h := Nat.mul_le_mul_right (Fintype.card (Fin nQ → F))
      (linear_bad_count C P L a B fs u.1 (not_forall.mp hd))
    linarith
  · simp only [constraintBad, ite_eq_right hd]
    rw [count_right, Fintype.card_prod]
    have h := Nat.mul_le_mul_left (Fintype.card (Fin nL → F)) (quad_bad_count C P a B fs u.2)
    linarith

end
end GordieHowe.Ligero.UntestedMaskRow
