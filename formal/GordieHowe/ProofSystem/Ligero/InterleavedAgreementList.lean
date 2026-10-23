-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Ligero.AgreementThreshold

@[expose] public section

/-!
# The agreement list of an interleaved Reed–Solomon code

For a matrix `U` of `R` rows over the `N` columns of the code `C` and a threshold `A`, the
**agreement list** (`list`) is the set of tuples of `R` polynomials of degree `< k` that agree
with `U` on a common set of at least `A` columns (`agreeCols`, `mem_list_iff`): the agreement list
of DKT26 eq. (3) for the interleaved code `C^R`, whose codewords are the tuples of codewords of
`C`. Two distinct tuples differ in some row, and in that row their polynomials agree on at most
`k − 1` columns, so their common agreement sets share at most `k − 1` columns. The pairwise
Johnson argument (`PolynomialAgreementList.incidence_bound`, `PolynomialAgreementList.cardinal_bound`,
DKT26 App. B.1; GRS Thm. 7.3.3, Exercise 7.5) then bounds the list by
`N (A − d) / (A² − N d)` with `d = k − 1`, when `A ≤ N` and `A² > N d` (`GordieHowe.Ligero.InterleavedAgreementList.card_le`). This is
the bound of `lem:johnson` (DKT26 eq. (67), second term) applied to the interleaved code. Above the
unique-decoding radius, `2A > N + (k − 1)`, two members would share at least `2A − N ≥ k` columns,
so the list has at most one member (`GordieHowe.Ligero.InterleavedAgreementList.card_le_one`); `listSize` is the list size of both cases.

The list is a finite set: each member is the tuple of rows interpolated on `k` of its agreement
columns (`GordieHowe.Ligero.AgreementThreshold.interpolatedRows`), so the list is a filter of the image of the `k`-tuples of
distinct columns. It is not computed by any extractor; Ligero in Longfellow's order of challenges
(`GordieHowe.Ligero.LongfellowOrder`) uses it in its state function only.
-/

namespace GordieHowe.Ligero.InterleavedAgreementList

open Polynomial
open scoped Classical

variable {F : Type} [Field F] {N R : ℕ} (C : GordieHowe.RSCode F N)

/-- **The common agreement set of a matrix with a tuple of polynomials**: the columns `j` at which
every row `i` of `U` equals the value of `fs i` at the column's point. -/
noncomputable def agreeCols (U : RSCode.Matrix F R N) (fs : Fin R → F[X]) :
    Finset (Fin N) :=
  Finset.univ.filter fun j => ∀ i, (fs i).eval (C.D j) = U i j

variable {C}

theorem mem_agreeCols {U : RSCode.Matrix F R N} {fs : Fin R → F[X]} {j : Fin N} :
    j ∈ agreeCols C U fs ↔ ∀ i, (fs i).eval (C.D j) = U i j := by
  simp [agreeCols]

/-- Rows that agree with polynomials on a set `D` agree with them on a superset of `D`'s columns:
`D` lies in the common agreement set. -/
theorem subset_agreeCols {U : RSCode.Matrix F R N} {D : Finset (Fin N)}
    {fs : Fin R → F[X]} (h : RSCode.RowsAgreeOn C U D fs) :
    D ⊆ agreeCols C U fs :=
  fun j hj => mem_agreeCols.mpr fun i => h.agree i j hj

/-- Polynomials agree with the rows on their common agreement set. -/
theorem rowsAgreeOn_agreeCols {U : RSCode.Matrix F R N} {fs : Fin R → F[X]}
    (hfs : ∀ i, (fs i).natDegree < C.k) :
    RSCode.RowsAgreeOn C U (agreeCols C U fs) fs :=
  ⟨hfs, fun i _ hj => mem_agreeCols.mp hj i⟩

variable (C)

/-- **The agreement list of the interleaved code** at threshold `A`: the tuples of rows
interpolated on `k` distinct columns (`AgreementThreshold.interpolatedRows`) whose common agreement set
with `U` has at least `A` columns. For `k ≤ A` these are exactly the tuples of polynomials of
degree `< k` agreeing with `U` on at least `A` common columns (`mem_list_iff`). Not computed by
any extractor. -/
noncomputable def list (U : RSCode.Matrix F R N) (A : ℕ) :
    Finset (Fin R → F[X]) :=
  (Finset.univ.image fun cols : Fin C.k ↪ Fin N => AgreementThreshold.interpolatedRows C U cols).filter
    fun fs => A ≤ (agreeCols C U fs).card

variable {C}

/-- Every member of the agreement list has rows of degree `< k`. -/
theorem natDegree_lt_of_mem_list {U : RSCode.Matrix F R N} {A : ℕ}
    {fs : Fin R → F[X]} (h : fs ∈ list C U A) (i : Fin R) :
    (fs i).natDegree < C.k := by
  obtain ⟨cols, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp h).1
  exact AgreementThreshold.natDegree_interpolatedRows_lt U cols i

/-- Every member of the agreement list agrees with the rows on at least `A` common columns. -/
theorem le_card_agreeCols_of_mem_list {U : RSCode.Matrix F R N} {A : ℕ}
    {fs : Fin R → F[X]} (h : fs ∈ list C U A) : A ≤ (agreeCols C U fs).card :=
  (Finset.mem_filter.mp h).2

/-- **Tuples agreeing with the rows on at least `A ≥ k` columns are in the agreement list**: the
tuple is the tuple of rows interpolated on the first `k` of those columns
(`AgreementThreshold.interpolatedRows_eq`). -/
theorem mem_list_of_rowsAgreeOn {U : RSCode.Matrix F R N} {A : ℕ} (hkA : C.k ≤ A)
    {D : Finset (Fin N)} {fs : Fin R → F[X]} (hfs : RSCode.RowsAgreeOn C U D fs)
    (hD : A ≤ D.card) : fs ∈ list C U A := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨AgreementThreshold.firstColumns D (hkA.trans hD),
    Finset.mem_univ _, AgreementThreshold.interpolatedRows_eq hfs (AgreementThreshold.firstColumns_mem _ _)⟩, ?_⟩
  exact hD.trans (Finset.card_le_card (subset_agreeCols hfs))

/-- **The agreement list at `A ≥ k`** is the set of tuples of polynomials of degree `< k` agreeing
with the rows on at least `A` common columns (DKT26 eq. (3), for the interleaved code). -/
theorem mem_list_iff {U : RSCode.Matrix F R N} {A : ℕ} (hkA : C.k ≤ A)
    {fs : Fin R → F[X]} :
    fs ∈ list C U A ↔ (∀ i, (fs i).natDegree < C.k) ∧ A ≤ (agreeCols C U fs).card :=
  ⟨fun h => ⟨natDegree_lt_of_mem_list h, le_card_agreeCols_of_mem_list h⟩,
    fun h => mem_list_of_rowsAgreeOn hkA (rowsAgreeOn_agreeCols h.1) h.2⟩

/-- **Distinct members of the agreement list share at most `k − 1` common agreement columns**: they
differ in some row, whose two polynomials of degree `< k` agree on at most `k − 1` columns
(`PolynomialAgreementList.agreement_inter_le`). -/
theorem card_agreeCols_inter_le {U : RSCode.Matrix F R N} {fs gs : Fin R → F[X]}
    (hf : ∀ i, (fs i).natDegree < C.k) (hg : ∀ i, (gs i).natDegree < C.k) (hne : fs ≠ gs) :
    (agreeCols C U fs ∩ agreeCols C U gs).card ≤ C.k - 1 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  refine (Finset.card_le_card fun j hj => ?_).trans
    (PolynomialAgreementList.agreement_inter_le C.D C.D_injective (U i)
      (Nat.le_sub_one_of_lt (hf i)) (Nat.le_sub_one_of_lt (hg i)) hi)
  obtain ⟨hjf, hjg⟩ := Finset.mem_inter.mp hj
  simp only [PolynomialAgreementList.agreements, Finset.mem_inter, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact ⟨mem_agreeCols.mp hjf i, mem_agreeCols.mp hjg i⟩

/-- **The Johnson list bound** `N (A − d) / (A² − N d)` (natural division) for agreement on at
least `A` of `N` positions with codewords any two of which agree on at most `d` positions
(`lem:johnson`; DKT26 eq. (67), second term; GRS Thm. 7.3.3). -/
def bound (N d A : ℕ) : ℕ := N * (A - d) / (A ^ 2 - N * d)

/-- **The Johnson bound for the interleaved code** (`lem:johnson` for `C^R`, DKT26 App. B.1):
for `A ≤ N` and `A² > N (k − 1)`, at most `N (A − (k − 1)) / (A² − N (k − 1))` tuples of polynomials
of degree `< k` agree with the rows on at least `A` common columns. Each member keeps `A` of its
agreement columns; distinct members share at most `k − 1` of them (`card_agreeCols_inter_le`), and
the incidence count (`PolynomialAgreementList.incidence_bound`,
`PolynomialAgreementList.cardinal_bound`) gives the bound. -/
theorem card_le (U : RSCode.Matrix F R N) {A : ℕ} (hAN : A ≤ N)
    (hJ : N * (C.k - 1) < A ^ 2) : (list C U A).card ≤ bound N (C.k - 1) A := by
  let I := {fs // fs ∈ list C U A}
  choose B hsub hcard using fun fs : I =>
    Finset.exists_subset_card_eq (le_card_agreeCols_of_mem_list fs.2)
  have hinter : ∀ fs ∈ (Finset.univ : Finset I), ∀ gs ∈ (Finset.univ : Finset I),
      fs ≠ gs → (B fs ∩ B gs).card ≤ C.k - 1 := fun fs _ gs _ hne =>
    (Finset.card_le_card (Finset.inter_subset_inter (hsub fs) (hsub gs))).trans
      (card_agreeCols_inter_le (natDegree_lt_of_mem_list fs.2) (natDegree_lt_of_mem_list gs.2)
        fun h => hne (Subtype.ext h))
  have hc := PolynomialAgreementList.incidence_bound Finset.univ B A (C.k - 1)
    (fun fs _ => hcard fs) hinter
  simpa only [Finset.card_univ, I, Fintype.card_coe, bound] using
    PolynomialAgreementList.cardinal_bound hAN hJ hc

/-- **At most one member above the unique-decoding radius**: when `2A > N + (k − 1)`, two members
of the agreement list would share at least `2A − N ≥ k` common agreement columns, more than
`card_agreeCols_inter_le` allows. -/
theorem card_le_one (U : RSCode.Matrix F R N) {A : ℕ} (hA : N + (C.k - 1) < 2 * A) :
    (list C U A).card ≤ 1 := by
  refine Finset.card_le_one.mpr fun fs hf gs hg => ?_
  by_contra hne
  have hi := card_agreeCols_inter_le (U := U) (natDegree_lt_of_mem_list hf)
    (natDegree_lt_of_mem_list hg) hne
  have hu := Finset.card_union_add_card_inter (agreeCols C U fs) (agreeCols C U gs)
  have hN : (agreeCols C U fs ∪ agreeCols C U gs).card ≤ N :=
    (Finset.card_le_univ _).trans_eq (Fintype.card_fin N)
  have := le_card_agreeCols_of_mem_list hf
  have := le_card_agreeCols_of_mem_list hg
  omega

/-- **The list size of the interleaved code** at agreement threshold `A`, block length `N` and
degree bound `d = k − 1`: one above the unique-decoding radius (`2A > N + d`,
`card_le_one`), the Johnson bound `bound N d A` otherwise (`card_le`). -/
def listSize (N d A : ℕ) : ℕ := if N + d < 2 * A then 1 else bound N d A

/-- **The list parameters of the interleaved code** at the numbers `N` (the block length), `d`
(the degree bound `k − 1`), `A` (the agreement threshold) and `L` (the list size), parameter facts:
`A ≤ N`, the Johnson condition `A² > N d`, and the list size `listSize N d A` at most `L`. -/
structure Parameters (N d A L : ℕ) : Prop where
  /-- The threshold is at most the block length. -/
  A_le : A ≤ N
  /-- The Johnson condition `A² > N d`. -/
  johnson : N * d < A ^ 2
  /-- The list size is at most `L`. -/
  listSize_le : listSize N d A ≤ L

/-- **The agreement list has at most `L` members** under the list parameters: at most one above
the unique-decoding radius (`card_le_one`), at most the Johnson bound otherwise
(`card_le`). -/
theorem card_list_le_of_parameters (U : RSCode.Matrix F R N) {A L : ℕ}
    (hP : Parameters N (C.k - 1) A L) : (list C U A).card ≤ L := by
  refine le_trans ?_ hP.listSize_le
  unfold listSize
  split_ifs with h
  · exact card_le_one U h
  · exact card_le U hP.A_le hP.johnson

/-! ### The data rows of a tableau -/

/-- **A member of the agreement list restricted to the rows after the first** is a member of the
agreement list of those rows, at a threshold `A ≥ k`: the common agreement set of the restricted
tuple with the restricted rows contains that of the tuple with all rows. In a Ligero tableau, row
`0` is the low-degree mask row and the others are the data rows. -/
theorem succ_mem_list {U : RSCode.Matrix F (R + 1) N} {A : ℕ} (hkA : C.k ≤ A)
    {fs : Fin (R + 1) → F[X]} (h : fs ∈ list C U A) :
    (fun i => fs i.succ) ∈ list C (fun i => U i.succ) A := by
  refine (mem_list_iff hkA).mpr ⟨fun i => natDegree_lt_of_mem_list h i.succ, ?_⟩
  refine (le_card_agreeCols_of_mem_list h).trans (Finset.card_le_card fun j hj => ?_)
  exact mem_agreeCols.mpr fun i => mem_agreeCols.mp hj i.succ

end GordieHowe.Ligero.InterleavedAgreementList
