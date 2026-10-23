-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.CharP.Basic
public import GordieHowe.Applications.Params
public import GordieHowe.Foundations.Probability.ChallengeEvent
public import GordieHowe.Foundations.ToMathlib.List
public import GordieHowe.Language.Realizations.FractionTree

@[expose] public section

/-!
# Range checks and the combined lookup argument

This file fixes the convention for gadgets that emit lookup needles.  A
needle-emitting gadget returns a `Check K`: its verdict and the list of field
values it wants looked up in `[0, T)`.  Circuits combine checks with
`Check.and`, which conjoins verdicts and concatenates needles, so the needle
count of a circuit is a `simp` lemma about list lengths, independent of the
witness values.

The range argument itself is the log-derivative identity (the paper's `lem:logup`) in
cross-multiplied form. Its soundness statement is a disjunction: every needle lies in the table, or
`α` is a root of `badPoly`, a polynomial defined from the needles and the histograms alone, of
degree at most `#needles + T - 1`.

Soundness of the log-derivative identity needs the needle count below the characteristic; that
enters as the hypothesis `hchar`.
-/

namespace GordieHowe

open Polynomial

/-- A gadget verdict together with the lookup needles the gadget emits. -/
structure Check (K : Type*) where
  ok : Bool
  needles : List K

namespace Check

variable {K : Type*}

def pass : Check K := ⟨true, []⟩

def assert (b : Bool) : Check K := ⟨b, []⟩

def and (a b : Check K) : Check K := ⟨a.ok && b.ok, a.needles ++ b.needles⟩

def all (l : List (Check K)) : Check K := l.foldr and pass

@[simp] theorem and_ok (a b : Check K) : (a.and b).ok = (a.ok && b.ok) := rfl
@[simp] theorem and_needles (a b : Check K) : (a.and b).needles = a.needles ++ b.needles := rfl
@[simp] theorem pass_ok : (pass : Check K).ok = true := rfl
@[simp] theorem pass_needles : (pass : Check K).needles = [] := rfl
@[simp] theorem assert_ok (b : Bool) : (assert b : Check K).ok = b := rfl
@[simp] theorem assert_needles (b : Bool) : (assert b : Check K).needles = [] := rfl

theorem all_ok (l : List (Check K)) : (all l).ok = l.all (·.ok) := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    change (c.ok && (all l).ok) = (c.ok && l.all (·.ok))
    rw [ih]

theorem all_needles (l : List (Check K)) : (all l).needles = l.flatMap (·.needles) := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    change c.needles ++ (all l).needles = c.needles ++ l.flatMap (·.needles)
    rw [ih]

end Check

namespace Range

variable {K : Type*} [Field K] [DecidableEq K]

/-- `Σ_l limbs[l] · B^l`, least significant limb first. -/
def reconstruct (B : ℕ) (limbs : List K) : K :=
  (limbs.zipIdx.map fun (l, i) => l * (B : K) ^ i).sum

omit [DecidableEq K] in
/-- Reconstruction separates the least significant limb from the remaining limbs. -/
theorem reconstruct_cons (B : ℕ) (v : K) (lo : List K) : reconstruct B (v :: lo) = v + (B : K) * reconstruct B lo := by
  simp only [reconstruct, List.zipIdx_cons', List.map_cons, List.map_map,
    Function.comp_def, List.sum_cons, pow_zero, mul_one, Prod.map_fst, Prod.map_snd, id_eq, pow_succ]
  rw [← List.sum_map_mul_left]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro x hx
  ring

/-- **The base-`B` digits of `m`**: the `k` least significant digits, least significant first
(the honest digit generator of `lib/gordiehowe/compiler/range.h`, `digits`). -/
-- spec-side
def digitsOf (B k m : ℕ) (j : Fin k) : ℕ := m / B ^ (j : ℕ) % B

omit [DecidableEq K] in
/-- The `k` least significant base-`B` digits of `m` reconstruct `m % B ^ k`. -/
theorem reconstruct_digitsOf (B k m : ℕ) :
    reconstruct B (List.ofFn fun j => (digitsOf B k m j : K)) = ((m % B ^ k : ℕ) : K) := by
  induction k generalizing m with
  | zero => simp [reconstruct, Nat.mod_one]
  | succ k ih =>
    have hdig : ∀ j : Fin k, digitsOf B (k + 1) m j.succ = digitsOf B k (m / B) j := by
      intro j
      simp only [digitsOf, Fin.val_succ, pow_succ', Nat.div_div_eq_div_mul]
    rw [List.ofFn_succ, reconstruct_cons]
    simp only [hdig, ih]
    rw [pow_succ', Nat.mod_mul]
    simp [digitsOf]

/-- `v` is the cast of a natural number below `T`.  This is exactly what a
lookup of `v` in the table `[0, T)` establishes, and it is the form in which
every range gadget states its conclusion: if each needle is the cast of a
natural below `T`, then the checked wire is the cast of a natural below its
bound.  The natural is existentially quantified, so no extra data is carried. -/
def IsNatBelow (T : ℕ) (v : K) : Prop := ∃ n < T, (n : K) = v

/-- **The natural below `T` that `v` is the cast of**, the first one found by a search over
`[0, T)` (`T` casts and comparisons), or `0` if there is none. -/
-- spec-side
def natBelow (T : ℕ) (v : K) : ℕ :=
  ((List.range T).find? fun n : ℕ => (n : K) = v).getD 0

/-- On a value that is the cast of a natural below `T`, `natBelow` returns such a natural. -/
theorem natBelow_spec {T : ℕ} {v : K} (h : IsNatBelow T v) :
    natBelow T v < T ∧ ((natBelow T v : ℕ) : K) = v := by
  obtain ⟨n, hn, hc⟩ := h
  have hsome : ((List.range T).find? fun m : ℕ => decide ((m : K) = v)).isSome :=
    List.find?_isSome.2 ⟨n, List.mem_range.2 hn, by simpa using hc⟩
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 hsome
  have hmem := List.mem_of_find?_eq_some hm
  have hp := List.find?_some hm
  simp only [natBelow, hm, Option.getD_some]
  exact ⟨List.mem_range.1 hmem, by simpa using hp⟩

omit [DecidableEq K] in
theorem reconstruct_isNatBelow {B k : ℕ} {lo : List K} (hlen : lo.length = k)
    (hlo : ∀ v ∈ lo, IsNatBelow B v) :
    IsNatBelow (B ^ k) (reconstruct B lo) := by
  subst k
  induction lo with
  | nil => exact ⟨0, by simp, by simp [reconstruct]⟩
  | cons v lo ih =>
    obtain ⟨a, ha, rfl⟩ := hlo v (by simp)
    obtain ⟨b, hb, hbcast⟩ := ih (fun w hw => hlo w (by simp [hw]))
    refine ⟨a + B * b, ?_, ?_⟩
    · simp only [List.length_cons, pow_succ]
      have hstep := Nat.mul_le_mul_left B (Nat.succ_le_of_lt hb)
      nlinarith
    · rw [reconstruct_cons, ← hbcast]
      simp only [Nat.cast_add, Nat.cast_mul]

/-! ### The combined lookup argument -/

/-- Balanced fraction tree used by `logup_range_check`: each leaf is `(1,d)`
and each internal node cross-multiplies its two children. The empty-list
value `(0,1)` is a total extension; the C++ builder requires nonempty input. -/
def fracTree (d : List K) : K × K := FractionTree.balanced d

omit [DecidableEq K] in
/-- The balanced construction has exactly the sequential accumulator's value,
including at zero denominators. The fold is a helper of the proofs. -/
theorem fracTree_eq_fold (d : List K) :
    fracTree d = d.foldl (fun (n, den) di => (n * di + den, den * di)) (0, 1) := by
  exact FractionTree.balanced_eq_fold d

/- The fraction update commutes for every starting numerator and denominator.
   This makes the sequential representation independent of needle order,
   including when some denominators are zero. -/

omit [DecidableEq K] in
/-- The fraction accumulator represents the sum of inverse denominators when
all its input denominators are nonzero. -/
theorem fracTree_fst_eq_sum_inv_mul (d : List K)
    (hnz : ∀ x ∈ d, x ≠ 0) :
    (fracTree d).1 = (d.map (fun x => x⁻¹)).sum * (fracTree d).2 := by
  have haux : ∀ (l : List K) (s n den : K),
      n = s * den →
      (∀ x ∈ l, x ≠ 0) →
      let r := l.foldl (fun (n, den) x => (n * x + den, den * x)) (n, den)
      r.1 = (s + (l.map (fun x => x⁻¹)).sum) * r.2 := by
    intro l
    induction l with
    | nil =>
        intro s n den hn _
        simpa using hn
    | cons x l ih =>
        intro s n den hn hnonzero
        have hx : x ≠ 0 := hnonzero x (by simp)
        have hstep : n * x + den = (s + x⁻¹) * (den * x) := by
          rw [hn]
          have hinv : x⁻¹ * (den * x) = den := by
            rw [mul_comm den x, ← mul_assoc, inv_mul_cancel₀ hx, one_mul]
          calc
            s * den * x + den = s * (den * x) + den := by ring
            _ = s * (den * x) + x⁻¹ * (den * x) := by rw [hinv]
            _ = (s + x⁻¹) * (den * x) := by ring
        have htail : ∀ y ∈ l, y ≠ 0 := by
          intro y hy
          exact hnonzero y (by simp [hy])
        change
          (l.foldl (fun (n, den) x => (n * x + den, den * x))
            (n * x + den, den * x)).1 =
          (s + (x⁻¹ + (l.map fun x => x⁻¹).sum)) *
            (l.foldl (fun (n, den) x => (n * x + den, den * x))
              (n * x + den, den * x)).2
        simpa only [add_assoc] using
          ih (s + x⁻¹) (n * x + den) (den * x) hstep htail
  rw [fracTree_eq_fold]
  simpa only [zero_add] using haux d 0 0 1 (by simp) hnz

/-- An injective finite table counts a list by summing its multiplicities. -/
theorem sum_count_mul_eq_sum_map {T : ℕ} (embed : Fin T → K)
    (hinj : Function.Injective embed) (needles : List K)
    (hin : ∀ v ∈ needles, ∃ j : Fin T, embed j = v) (f : K → K) :
    (∑ j : Fin T, (needles.count (embed j) : K) * f (embed j)) =
      (needles.map f).sum := by
  induction needles with
  | nil => simp
  | cons v needles ih =>
      obtain ⟨j, hj⟩ := hin v (by simp)
      have htail : ∀ w ∈ needles, ∃ j : Fin T, embed j = w := by
        intro w hw
        exact hin w (by simp [hw])
      rw [List.map_cons, List.sum_cons, ← hj]
      simp only [List.count_cons, Nat.cast_add, add_mul]
      rw [Finset.sum_add_distrib, ih htail]
      simp [hinj.eq_iff, add_comm]

/-- The weights the verifier computes and passes as public wires,
`tableWeights j = (α - j)⁻¹`. The verifier draws `α` outside the table's values
(`LookupChallenge`), so every operand is nonzero; at a table point Lean's total inverse would
return `0`, and GordieHowe's range lowering (`lib/gordiehowe/compiler/range.h`, `range.weights`)
refuses such an `α`. -/
def logupTcoef (T : ℕ) (α : K) (j : Fin T) : K := (α - j)⁻¹

/-- The range argument: one fraction tree over the needles against the static
histogram on `[0, T)` and the masked histogram on `[0, Sdyn)`, at the public
weights. -/
def rangeArgument {T Sdyn : ℕ} (hSdyn : Sdyn ≤ T) (needles : List K) (tableWeights : Fin T → K)
    (mComm : Fin T → K) (mMask : Fin Sdyn → K) (α : K) : Bool :=
  let (num, den) := fracTree (needles.map fun v => α - v)
  let commSum := ∑ j, mComm j * tableWeights j
  let maskSum := ∑ j, mMask j * tableWeights (Fin.castLE hSdyn j)
  decide (num = (commSum + maskSum) * den)

theorem rangeArgument_eq_true_iff {T Sdyn : ℕ} (hSdyn : Sdyn ≤ T) {needles : List K}
    {tableWeights : Fin T → K} {mComm : Fin T → K} {mMask : Fin Sdyn → K} {α : K} :
    rangeArgument hSdyn needles tableWeights mComm mMask α = true ↔
      (fracTree (needles.map fun v => α - v)).1
        = (∑ j, mComm j * tableWeights j + ∑ j, mMask j * tableWeights (Fin.castLE hSdyn j))
          * (fracTree (needles.map fun v => α - v)).2 := by
  simp [rangeArgument]

/-- The combined histogram: the masked part extended by zero outside its support. -/
def combined {T Sdyn : ℕ} (mComm : Fin T → K) (mMask : Fin Sdyn → K) (j : Fin T) : K :=
  mComm j + if h : j < Sdyn then mMask ⟨j, h⟩ else 0

/-- Numerator of `Σ_i 1/(X - v_i)` over the common denominator `∏_i (X - v_i)`. -/
noncomputable def needleCount (needles : List K) : K[X] :=
  (needles.map fun v => ((needles.erase v).map fun w => Polynomial.X - C w).prod).sum

noncomputable def needleDen (needles : List K) : K[X] :=
  (needles.map fun v => Polynomial.X - C v).prod

/-- `needleCount` is the formal derivative of the common needle denominator. -/
theorem needleNum_eq_derivative (needles : List K) :
    needleCount needles = (needleDen needles).derivative := by
  unfold needleCount needleDen
  change (Multiset.map (fun v =>
      (Multiset.map (fun w => Polynomial.X - C w) (needles.erase v : Multiset K)).prod)
      (needles : Multiset K)).sum =
    derivative (Multiset.map (fun w => Polynomial.X - C w) (needles : Multiset K)).prod
  rw [derivative_prod]
  simp only [derivative_X_sub_C, mul_one, Multiset.coe_erase]

/-- The fraction tree on `α - v` evaluates the derivative and the product of
the corresponding linear factors. -/
theorem fracTree_eq_eval (needles : List K) (α : K) :
    fracTree (needles.map fun v => α - v) =
      ((needleCount needles).eval α, (needleDen needles).eval α) := by
  rw [needleNum_eq_derivative]
  have haux : ∀ (l : List K) (P : K[X]),
      l.foldl (fun (n, den) v => (n * (α - v) + den, den * (α - v)))
          (P.derivative.eval α, P.eval α) =
        (((P * needleDen l).derivative).eval α, (P * needleDen l).eval α) := by
    intro l
    induction l with
    | nil =>
        intro P
        simp [needleDen]
    | cons v l ih =>
        intro P
        rw [List.foldl_cons]
        have hstep :
            (P.derivative.eval α * (α - v) + P.eval α, P.eval α * (α - v)) =
              ((P * (Polynomial.X - C v)).derivative.eval α,
                (P * (Polynomial.X - C v)).eval α) := by
          simp only [derivative_mul, derivative_X_sub_C, eval_add, eval_mul,
            eval_sub, eval_X, eval_C, mul_one]
        change l.foldl (fun (n, den) v => (n * (α - v) + den, den * (α - v)))
            (P.derivative.eval α * (α - v) + P.eval α, P.eval α * (α - v)) = _
        rw [hstep, ih]
        simp only [needleDen, List.map_cons, List.prod_cons]
        ring_nf
  simpa [fracTree_eq_fold, needleDen, List.foldl_map] using haux needles (1 : K[X])

omit [DecidableEq K] in
/-- The common needle denominator has one linear factor per needle. -/
theorem needleDen_natDegree (needles : List K) :
    (needleDen needles).natDegree = needles.length := by
  unfold needleDen
  change (Multiset.map (fun v => Polynomial.X - C v) (needles : Multiset K)).prod.natDegree = _
  rw [natDegree_multiset_prod_X_sub_C_eq_card]
  rfl

omit [DecidableEq K] in
/-- The needle denominator is monic. -/
theorem needleDen_monic (needles : List K) : (needleDen needles).Monic := by
  unfold needleDen
  change (Multiset.map (fun v => Polynomial.X - C v) (needles : Multiset K)).prod.Monic
  exact monic_multisetProd_X_sub_C _

/-- The multiplicity of a value in the denominator is its needle count. -/
theorem needleDen_rootMultiplicity (needles : List K) (v : K) :
    (needleDen needles).rootMultiplicity v = needles.count v := by
  rw [← count_roots, ← Multiset.coe_count]
  unfold needleDen
  change ((Multiset.map (fun w => Polynomial.X - C w) (needles : Multiset K)).prod.roots).count v = _
  rw [roots_multiset_prod_X_sub_C]

omit [DecidableEq K] in
/-- Below the characteristic, a nonempty needle denominator has nonzero derivative. -/
theorem needleDen_derivative_ne_zero {p : ℕ} [CharP K p] (needles : List K)
    (hne : needles ≠ []) (hchar : needles.length < p) :
    (needleDen needles).derivative ≠ 0 := by
  have hlen : 0 < needles.length := List.length_pos_of_ne_nil hne
  have hp : 0 < p := hlen.trans hchar
  have hcast : (needles.length : K) ≠ 0 := by
    intro hz
    have := CharP.natCast_injOn_Iio K p hchar hp (by simpa using hz)
    omega
  intro hd
  have hc := congrArg (fun q : K[X] => q.coeff (needles.length - 1)) hd
  rw [coeff_derivative, coeff_zero] at hc
  have hsucc : needles.length - 1 + 1 = needles.length := Nat.sub_add_cancel hlen
  have hcoeff : (needleDen needles).coeff needles.length = 1 := by
    rw [← needleDen_natDegree needles]
    exact (needleDen_monic needles).coeff_natDegree
  rw [hsucc, hcoeff, one_mul] at hc
  apply hcast
  rw [← hsucc, Nat.cast_add, Nat.cast_one]
  exact hc

/-- Differentiating the needle denominator removes at least one degree. -/
theorem needleNum_natDegree_le (needles : List K) :
    (needleCount needles).natDegree ≤ needles.length - 1 := by
  rw [needleNum_eq_derivative]
  exact (natDegree_derivative_le _).trans_eq (by rw [needleDen_natDegree])

/-- Numerator of `Σ_j m_j/(X - j)` over `∏_{j<T} (X - j)`. -/
noncomputable def tableCount {T : ℕ} (m : Fin T → K) : K[X] :=
  ∑ j, C (m j) * ∏ k ∈ Finset.univ.erase j, (Polynomial.X - C (k : K))

noncomputable def tableDen (T : ℕ) : K[X] :=
  ∏ k : Fin T, (Polynomial.X - C (k : K))

omit [DecidableEq K] in
/-- The table denominator has one linear factor per table entry. -/
theorem tableDen_natDegree (T : ℕ) : (tableDen T : K[X]).natDegree = T := by
  simpa [tableDen] using
    (natDegree_finsetProd_X_sub_C_eq_card (Finset.univ : Finset (Fin T)) (fun k => (k : K)))

omit [DecidableEq K] in
/-- Away from the table, its denominator evaluates to a nonzero product. -/
theorem tableDen_eval_ne_zero {T : ℕ} {v : K} (hv : ∀ j : Fin T, v ≠ j) :
    (tableDen T : K[X]).eval v ≠ 0 := by
  rw [tableDen, eval_prod, Finset.prod_ne_zero_iff]
  intro j hj
  simpa only [eval_sub, eval_X, eval_C, sub_ne_zero] using hv j

omit [DecidableEq K] in
/-- Away from the table, the table numerator evaluates to the weighted sum
with weights `(α - j)⁻¹`, multiplied by the table denominator. -/
theorem tableNum_eval {T : ℕ} (m : Fin T → K) {α : K} (hα : ∀ j : Fin T, α ≠ j) :
    (tableCount m).eval α =
      (∑ j, m j * (α - (j : K))⁻¹) * (tableDen T : K[X]).eval α := by
  unfold tableCount tableDen
  rw [eval_finsetSum, eval_prod, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [eval_mul, eval_C, eval_prod, eval_sub, eval_X]
  rw [← Finset.mul_prod_erase Finset.univ (fun k : Fin T => α - (k : K))
    (Finset.mem_univ j)]
  conv_rhs =>
    rw [mul_assoc (m j) (α - (j : K))⁻¹,
      ← mul_assoc (α - (j : K))⁻¹ (α - (j : K)),
      inv_mul_cancel₀ (sub_ne_zero.mpr (hα j)), one_mul]

omit [DecidableEq K] in
/-- Extending the masked histogram by zero makes its weighted sum split into
the committed and masked weighted sums. -/
theorem combined_weighted_sum {T Sdyn : ℕ} (hSdyn : Sdyn ≤ T)
    (mComm : Fin T → K) (mMask : Fin Sdyn → K) (w : Fin T → K) :
    (∑ j, combined mComm mMask j * w j) =
      (∑ j, mComm j * w j) + ∑ j, mMask j * w (Fin.castLE hSdyn j) := by
  simp only [combined, add_mul, Finset.sum_add_distrib]
  congr 1
  have hmul :
      (∑ j : Fin T, (if h : j < Sdyn then mMask ⟨j, h⟩ else 0) * w j) =
        ∑ j : Fin T, if h : j < Sdyn then mMask ⟨j, h⟩ * w j else 0 := by
    apply Finset.sum_congr rfl
    intro j hj
    split <;> simp
  rw [hmul]
  have hfilter :
      (∑ j : Fin T, if h : j < Sdyn then mMask ⟨j, h⟩ * w j else 0) =
        ∑ j ∈ Finset.univ.filter (fun j : Fin T => j < Sdyn),
          if h : j < Sdyn then mMask ⟨j, h⟩ * w j else 0 := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases h : (j : ℕ) < Sdyn <;> simp [h]
  rw [hfilter]
  refine Finset.sum_bij
      (s := Finset.univ.filter (fun j : Fin T => j < Sdyn))
      (t := Finset.univ)
      (f := fun j => if h : j < Sdyn then mMask ⟨j, h⟩ * w j else 0)
      (g := fun j => mMask j * w (Fin.castLE hSdyn j))
      (fun (j : Fin T) hj => (⟨j, (Finset.mem_filter.mp hj).2⟩ : Fin Sdyn)) ?_ ?_ ?_ ?_
  · simp
  · intro a₁ ha₁ a₂ ha₂ heq
    exact Fin.ext (Fin.mk.inj heq)
  · intro b hb
    refine ⟨Fin.castLE hSdyn b, ?_, ?_⟩
    · simp
    · rfl
  · intro a ha
    simp [(Finset.mem_filter.mp ha).2]

omit [DecidableEq K] in
/-- Every summand of the table numerator omits one table factor. -/
theorem tableNum_natDegree_le {T : ℕ} (m : Fin T → K) :
    (tableCount m).natDegree ≤ T - 1 := by
  unfold tableCount
  refine natDegree_sum_le_of_forall_le Finset.univ _ ?_
  intro j hj
  calc
    (C (m j) * ∏ k ∈ Finset.univ.erase j, (Polynomial.X - C (k : K))).natDegree
        ≤ (C (m j)).natDegree +
          (∏ k ∈ Finset.univ.erase j, (Polynomial.X - C (k : K))).natDegree :=
      natDegree_mul_le
    _ ≤ 0 + (T - 1) := by
      gcongr
      · exact (natDegree_C _).le
      · rw [natDegree_finsetProd_X_sub_C_eq_card]
        simp
    _ = T - 1 := by omega

/-- The identity `Num/Den = Σ_j m_j/(X - j)` cross-multiplied: its two sides
differ by this polynomial, defined from the needles and histograms alone. -/
noncomputable def badPoly {T Sdyn : ℕ} (needles : List K) (mComm : Fin T → K)
    (mMask : Fin Sdyn → K) : K[X] :=
  needleCount needles * tableDen T - needleDen needles * tableCount (combined mComm mMask)

/-- If a needle is outside the table and the needle count is below the
characteristic, the log-derivative identity cannot hold as a polynomial
identity.  The proof compares the multiplicity of the outside needle on both
sides: differentiation lowers it by one, while the table denominator does not
vanish there. -/
theorem badPoly_ne_zero_of_outside {p : ℕ} [CharP K p] {T Sdyn : ℕ}
    {needles : List K} {mComm : Fin T → K} {mMask : Fin Sdyn → K} {v : K}
    (hchar : needles.length < p) (hmem : v ∈ needles)
    (hout : ¬ IsNatBelow T v) : badPoly needles mComm mMask ≠ 0 := by
  have hv : ∀ j : Fin T, v ≠ j := by
    intro j hvj
    apply hout
    exact ⟨j, j.isLt, hvj.symm⟩
  have hcountpos : 0 < needles.count v := List.count_pos_iff.mpr hmem
  have hcountlt : needles.count v < p :=
    List.count_le_length.trans_lt hchar
  have hp : 0 < p := hcountpos.trans hcountlt
  have hcountcast : (needles.count v : K) ≠ 0 := by
    intro hz
    have := CharP.natCast_injOn_Iio K p hcountlt hp (by simpa using hz)
    omega
  have hD : needleDen needles ≠ 0 := (needleDen_monic needles).ne_zero
  have hDroot : (needleDen needles).IsRoot v := by
    apply (rootMultiplicity_pos hD).mp
    rw [needleDen_rootMultiplicity]
    exact hcountpos
  have hrootcast : ((needleDen needles).rootMultiplicity v : K) ≠ 0 := by
    rw [needleDen_rootMultiplicity]
    exact hcountcast
  have hderivrm : (needleDen needles).derivative.rootMultiplicity v =
      needles.count v - 1 := by
    rw [derivative_rootMultiplicity_of_root_of_mem_nonZeroDivisors hDroot
      (mem_nonZeroDivisors_of_ne_zero hrootcast), needleDen_rootMultiplicity]
  have hderiv : (needleDen needles).derivative ≠ 0 :=
    needleDen_derivative_ne_zero needles (List.ne_nil_of_mem hmem) hchar
  have hTDeval : (tableDen T : K[X]).eval v ≠ 0 := tableDen_eval_ne_zero hv
  have hTD : (tableDen T : K[X]) ≠ 0 := by
    intro hzero
    exact hTDeval (by rw [hzero, eval_zero])
  have hTDrm : (tableDen T : K[X]).rootMultiplicity v = 0 := by
    apply rootMultiplicity_eq_zero
    simpa only [IsRoot] using hTDeval
  intro hbad
  have heq : (needleDen needles).derivative * tableDen T =
      needleDen needles * tableCount (combined mComm mMask) := by
    apply sub_eq_zero.mp
    simpa only [badPoly, needleNum_eq_derivative] using hbad
  have hleft : (needleDen needles).derivative * tableDen T ≠ 0 := mul_ne_zero hderiv hTD
  have hright : needleDen needles * tableCount (combined mComm mMask) ≠ 0 := by
    rw [← heq]
    exact hleft
  have hrm := congrArg (fun q : K[X] => q.rootMultiplicity v) heq
  rw [rootMultiplicity_mul hleft, rootMultiplicity_mul hright, hderivrm, hTDrm,
    needleDen_rootMultiplicity] at hrm
  omega

theorem badPoly_natDegree_le {T Sdyn : ℕ} (needles : List K) (mComm : Fin T → K)
    (mMask : Fin Sdyn → K) :
    (badPoly needles mComm mMask).natDegree ≤ needles.length + T - 1 := by
  cases needles with
  | nil =>
      simpa [badPoly, needleCount, needleDen, tableDen] using
        (tableNum_natDegree_le (combined mComm mMask))
  | cons v needles =>
      cases T with
      | zero =>
          simpa [badPoly, tableCount, tableDen] using
            (needleNum_natDegree_le (v :: needles))
      | succ T =>
          unfold badPoly
          refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
          · calc
              (needleCount (v :: needles) * tableDen (T + 1)).natDegree
                  ≤ (needleCount (v :: needles)).natDegree +
                    (tableDen (T + 1)).natDegree := natDegree_mul_le
              _ ≤ ((v :: needles).length - 1) + (T + 1) := by
                rw [tableDen_natDegree]
                exact Nat.add_le_add_right (needleNum_natDegree_le (v :: needles)) (T + 1)
              _ ≤ (v :: needles).length + (T + 1) - 1 := by
                simp only [List.length_cons]
                omega
          · calc
              (needleDen (v :: needles) * tableCount (combined mComm mMask)).natDegree
                  ≤ (needleDen (v :: needles)).natDegree +
                    (tableCount (combined mComm mMask)).natDegree := natDegree_mul_le
              _ ≤ (v :: needles).length + ((T + 1) - 1) := by
                rw [needleDen_natDegree]
                exact Nat.add_le_add_left (tableNum_natDegree_le _) (v :: needles).length
              _ ≤ (v :: needles).length + (T + 1) - 1 := by
                simp only [List.length_cons]
                omega

/-- The lookup event in `α`. -/
noncomputable def lookupEvent {T Sdyn : ℕ} (needles : List K) (mComm : Fin T → K)
    (mMask : Fin Sdyn → K) : ChallengeEvent K :=
  ⟨badPoly needles mComm mMask, needles.length + T - 1, badPoly_natDegree_le needles mComm mMask⟩

/-- **The values of the table `[0, T)`** in `K`. -/
def tableValues (T : ℕ) : Finset K := Finset.univ.image fun j : Fin T => (j : K)

theorem mem_tableValues {T : ℕ} {x : K} : x ∈ tableValues T ↔ ∃ j : Fin T, (j : K) = x := by
  simp [tableValues]

/-- A table point is a table value. -/
theorem natCast_mem_tableValues {T : ℕ} (j : Fin T) : (j : K) ∈ tableValues T :=
  mem_tableValues.mpr ⟨j, rfl⟩

/-- Outside the table values, `α` differs from every table point. -/
theorem ne_of_notMem_tableValues {T : ℕ} {α : K} (hα : α ∉ tableValues T) (j : Fin T) :
    α ≠ j := fun h => hα (h ▸ natCast_mem_tableValues j)

theorem card_tableValues_le (T : ℕ) : (tableValues (K := K) T).card ≤ T :=
  Finset.card_image_le.trans (by simp)

/-- A table that embeds into the field has `T` values. -/
theorem card_tableValues {T : ℕ} (hinj : Function.Injective (fun j : Fin T => (j : K))) :
    (tableValues (K := K) T).card = T := by
  rw [tableValues, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

/-- A smaller table's values are among a larger table's. -/
theorem tableValues_mono {T T' : ℕ} (h : T ≤ T') : tableValues (K := K) T ⊆ tableValues T' := by
  intro x hx
  obtain ⟨j, rfl⟩ := mem_tableValues.mp hx
  exact mem_tableValues.mpr ⟨Fin.castLE h j, rfl⟩

/-- **Below the characteristic, `T` is not a value of the table `[0, T)`.** -/
theorem natCast_notMem_tableValues_of_lt_char {p : ℕ} [CharP K p] {T : ℕ} (hT : T < p) :
    (T : K) ∉ tableValues T := fun h => by
  obtain ⟨j, hj⟩ := mem_tableValues.mp h
  exact (Nat.ne_of_lt j.isLt) (CharP.natCast_injOn_Iio K p (j.isLt.trans hT) hT hj)

/-- **The values the lookup challenge avoids** for tables within `[0, T)`: the values of `[0, T)`
when `T` itself is not one of them (every configuration: `T` below the characteristic,
`excluded_of_lt_char`); otherwise none, a total extension in which `T` is always outside, so the
challenge type has the element `T`. Irreducible, so that unification never evaluates the
membership test on an abstract field; its facts go through the lemmas below. -/
@[irreducible] def excluded (K : Type*) [Field K] [DecidableEq K] (T : ℕ) : Finset K :=
  if (T : K) ∈ tableValues T then ∅ else tableValues T

/-- `T` is never a value the lookup challenge avoids. -/
theorem natCast_notMem_excluded (T : ℕ) : (T : K) ∉ excluded K T := by
  unfold excluded
  split_ifs with h
  · exact Finset.notMem_empty _
  · exact h

/-- When `T` is not a table value, the values the lookup challenge avoids are the table's. -/
theorem excluded_of_natCast_notMem {T : ℕ} (h : (T : K) ∉ tableValues T) :
    excluded K T = tableValues T := by
  simp [excluded, h]

/-- Below the characteristic, the values the lookup challenge avoids are the table's. -/
theorem excluded_of_lt_char {p : ℕ} [CharP K p] {T : ℕ} (hT : T < p) :
    excluded K T = tableValues T :=
  excluded_of_natCast_notMem (natCast_notMem_tableValues_of_lt_char hT)

/-- Below the characteristic, the lookup challenge avoids `T` values. -/
theorem card_excluded_of_lt_char {p : ℕ} [CharP K p] {T : ℕ} (hT : T < p) :
    (excluded K T).card = T := by
  rw [excluded_of_lt_char hT, card_tableValues fun i j h =>
    Fin.ext (CharP.natCast_injOn_Iio K p (i.isLt.trans hT) (j.isLt.trans hT) h)]

/-- The lookup challenge avoids at most `T` values. -/
theorem card_excluded_le (T : ℕ) : (excluded K T).card ≤ T := by
  unfold excluded
  split_ifs
  · exact Nat.zero_le T
  · exact card_tableValues_le T

/-- **The lookup challenge** for tables within `[0, T)`: an element of `K` outside the values it
avoids (`excluded`). The verifier draws it uniformly; the C++ rejection-samples the field's `sample`
off the table values. -/
abbrev LookupChallenge (K : Type*) [Field K] [DecidableEq K] (T : ℕ) :=
  {x : K // x ∉ excluded K T}

/-- The lookup challenge `T`, outside every table within `[0, T)`. -/
instance (T : ℕ) : Inhabited (LookupChallenge K T) := ⟨⟨T, natCast_notMem_excluded T⟩⟩

/-- Every needle lies in the table `[0, T)`. -/
def InTable (T : ℕ) (needles : List K) : Prop := ∀ v ∈ needles, IsNatBelow T v

/-- **Paper `lem:logup-point`, part (1), at the range tables**: range argument soundness. With the
weights the verifier computes and `α` outside the table, if the gadget accepts then every needle
lies in `[0, T)` or `α` is a root of the nonzero `badPoly` (`lookupEvent`): the identity is
`G(α) = 0` for `G = badPoly`, nonzero of degree at most `#needles + T - 1` when a needle is outside
the table.

The verifier draws `α` uniformly outside a set `U` containing the table values, so the event is
charged in the round-by-round layer at `(#needles + T - 1) / (|K| - |U|)`
(`ChallengeEvent.probUniform_badAt_le_compl`). There is no hypothesis about the weights: they are
the verifier's own computation, substituted.

`hchar` is a parameter condition (the circuit's needle count, a `simp` lemma, against
`char`); `hSdyn` is a parameter condition; `hα` holds for every challenge the verifier draws. -/
theorem rangeArgument_sound {p : ℕ} [CharP K p] {T Sdyn : ℕ} {needles : List K}
    {mComm : Fin T → K} {mMask : Fin Sdyn → K} {α : K}
    (hchar : needles.length < p) (hSdyn : Sdyn ≤ T) (hα : α ∉ tableValues T)
    (h : rangeArgument hSdyn needles (logupTcoef T α) mComm mMask α = true) :
    InTable T needles ∨ (lookupEvent needles mComm mMask).BadAt α := by
  by_cases hin : InTable T needles
  · exact Or.inl hin
  right
  rw [InTable] at hin
  push Not at hin
  obtain ⟨v, hmem, hout⟩ := hin
  change badPoly needles mComm mMask ≠ 0 ∧ (badPoly needles mComm mMask).eval α = 0
  refine ⟨badPoly_ne_zero_of_outside hchar hmem hout, ?_⟩
  have hfrac := (rangeArgument_eq_true_iff hSdyn).mp h
  rw [fracTree_eq_eval] at hfrac
  have hsum := combined_weighted_sum hSdyn mComm mMask (logupTcoef T α)
  have htableNum := tableNum_eval (combined mComm mMask) (ne_of_notMem_tableValues hα)
  simp only [logupTcoef] at hsum hfrac
  rw [badPoly, eval_sub, eval_mul, eval_mul, htableNum, hfrac, ← hsum]
  ring

/-- **Completeness.**  With the combined histogram equal to the needle counts,
the identity holds at every `α` outside the table: every challenge the verifier draws. -/
theorem rangeArgument_complete {T Sdyn : ℕ} (hSdyn : Sdyn ≤ T) {needles : List K}
    {mComm : Fin T → K} {mMask : Fin Sdyn → K} {α : K}
    (hinj : Function.Injective (fun j : Fin T => (j : K)))
    (hα : α ∉ tableValues T)
    (hin : InTable T needles)
    (hhist : ∀ j : Fin T, combined mComm mMask j = needles.count (j : K)) :
    rangeArgument hSdyn needles (logupTcoef T α) mComm mMask α = true := by
  apply (rangeArgument_eq_true_iff hSdyn).2
  have hden : ∀ d ∈ needles.map (fun v => α - v), d ≠ 0 := by
    intro d hd
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hd
    obtain ⟨j, hj, hjv⟩ := hin v hv
    rw [← hjv]
    exact sub_ne_zero.mpr (ne_of_notMem_tableValues hα ⟨j, hj⟩)
  rw [fracTree_fst_eq_sum_inv_mul _ hden]
  apply congrArg (fun c : K => c * (fracTree (needles.map fun v => α - v)).2)
  rw [← combined_weighted_sum hSdyn mComm mMask (logupTcoef T α)]
  simp only [hhist, logupTcoef]
  have hsum := sum_count_mul_eq_sum_map (fun j : Fin T => (j : K)) hinj needles
    (fun v hv => by
      obtain ⟨j, hj, hjv⟩ := hin v hv
      exact ⟨⟨j, hj⟩, hjv⟩)
    (fun v => (α - v)⁻¹)
  simpa only [List.map_map, Function.comp_def] using hsum.symm

/-- The honest histogram of a needle list over a finite lookup table. -/
-- spec-side
def histogram {T : ℕ} (needles : List K) (j : Fin T) : K :=
  (needles.count (j : K) : ℕ)

end Range

end GordieHowe
