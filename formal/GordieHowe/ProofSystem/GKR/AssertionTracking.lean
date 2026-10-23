-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.GKR.ClaimEvaluation
public import GordieHowe.ProofSystem.GKR.LayerProtocol

@[expose] public section

/-!
# Prefix-local tracking of GKR assertion evaluations

A fixed assertion table is specialized one coordinate at a time. Each bad
event depends only on the previous challenges and the fresh scalar, so the
counting bound applies to adaptive, prover-interleaved challenge streams.
-/
namespace GordieHowe.GKR.AssertionTracking
open IOP
open ClaimEvaluation
open LayerPolynomial (Cube boolValue Vars)
open scoped Classical
section
variable {F : Type} [Field F] {d : ℕ}

/-- Assertion table after the first n hand-zero challenges. -/
def table (w : Cube d → F) (r : Fin d → F) : ℕ → Cube d → F
  | 0 => w
  | n+1 => if h : n < d then collapse (table w r n) ⟨n,h⟩ (r ⟨n,h⟩) else table w r n

theorem table_step (w : Cube d → F) (r : Fin d → F) (i : Fin d) :
    table w r (i.val+1) = collapse (table w r i.val) i (r i) := by
  simp [table, i.isLt]

/-- No future challenge is used to construct a prefix table. -/
theorem table_prefix (w : Cube d → F) (r s : Fin d → F) (n : ℕ)
    (h : ∀ i, i.val < n → r i = s i) : table w r n = table w s n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [table]
    by_cases hn : n < d
    · simp only [dite_eq_left hn]
      rw [ih (fun i hi => h i (by omega)), h ⟨n,hn⟩ (by simp)]
    · simp only [dite_eq_right hn]
      exact ih (fun i hi => h i (by omega))

def prefixPoint (r : Fin d → F) (n : ℕ) (b : Cube d) : Fin d → F :=
  fun j => if j.val < n then r j else boolValue (b j)

theorem prefixPoint_bit (r : Fin d → F) (b : Cube d) (i : Fin d) (v : Bool) :
    prefixPoint r i.val (Function.update b i v) =
      Function.update (prefixPoint r i.val b) i (boolValue v) := by
  funext j
  by_cases hj : j = i
  · subst j; simp [prefixPoint]
  · simp [prefixPoint, Function.update_of_ne hj]

theorem prefixPoint_step (r : Fin d → F) (b : Cube d) (i : Fin d) :
    prefixPoint r (i.val+1) b = Function.update (prefixPoint r i.val b) i (r i) := by
  funext j
  by_cases hj : j = i
  · subst j; simp [prefixPoint]
  · have hv : j.val ≠ i.val := fun h => hj (Fin.ext h)
    have ht : j.val < i.val+1 ↔ j.val < i.val := by omega
    simp only [prefixPoint, Function.update_of_ne hj, ht]

/-- Prefix tables evaluate the original MLE at precisely the installed prefix. -/
theorem table_eq_value (w : Cube d → F) (r : Fin d → F) (n : ℕ) (hn : n ≤ d) (b : Cube d) :
    table w r n b = value w (prefixPoint r n b) := by
  induction n generalizing b with
  | zero =>
    change w b = value w (fun j => boolValue (b j))
    rw [← ClaimEvaluation.eval_mle, ClaimEvaluation.mle_boolean]
  | succ n ih =>
    have hnd : n < d := by omega
    let i : Fin d := ⟨n,hnd⟩
    rw [show n+1=i.val+1 from rfl, table_step]
    simp only [collapse]
    rw [ih (by omega), ih (by omega)]
    rw [prefixPoint_bit r b i false, prefixPoint_bit r b i true, prefixPoint_step r b i]
    exact (value_update w (prefixPoint r n b) i (r i)).symm

theorem table_final (w : Cube d → F) (r : Fin d → F) (b : Cube d) :
    table w r d b = value w r := by
  rw [table_eq_value w r d le_rfl]
  have hp : prefixPoint r d b = r := by funext j; simp [prefixPoint,j.isLt]
  rw [hp]

/-- A currently nonzero assertion table disappears at the fresh challenge. -/
def Bad (w : Cube d → F) (r : Fin d → F) (i : Fin d) (x : F) : Prop :=
  (∃ b, table w r i.val b ≠ 0) ∧ ∀ b, collapse (table w r i.val) i x b = 0

theorem bad_prefix (w : Cube d → F) (r s : Fin d → F) (i : Fin d)
    (h : ∀ j, j.val < i.val → r j = s j) (x : F) : Bad w r i x ↔ Bad w s i x := by
  simp only [Bad, table_prefix w r s i.val h]

theorem bad_count [Fintype F] (w : Cube d → F) (r : Fin d → F) (i : Fin d) :
    (Finset.univ.filter fun x => Bad w r i x).card ≤ 1 := by
  by_cases h : ∃ b, table w r i.val b ≠ 0
  · simpa only [Bad, h, true_and] using collapse_count (table w r i.val) h i
  · simp [Bad,h]

/-- Replacing the fresh challenge cannot change its already-fixed prefix. -/
theorem bad_update (w : Cube d → F) (r : Fin d → F) (i : Fin d) (x : F) :
    Bad w (Function.update r i x) i x ↔ Bad w r i x := by
  apply bad_prefix
  intro j hj
  have hji : j ≠ i := by intro h; subst j; omega
  exact Function.update_of_ne hji _ _

theorem bad_count_nnreal [Fintype F] (w : Cube d → F) (r : Fin d → F) (i : Fin d) :
    ((Finset.univ.filter fun x => Bad w (Function.update r i x) i x).card : NNReal) ≤
      (1 / Fintype.card F : NNReal) * Fintype.card F := by
  have hc : (Fintype.card F : NNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [div_mul_cancel₀ _ hc]
  simp only [bad_update]
  exact_mod_cast bad_count w r i

/-- Outside prefix-local collapse events, zero final evaluation certifies all
original assertions. No joint uniformity of the challenge vector is used. -/
theorem zero_of_no_bad (w : Cube d → F) (r : Fin d → F)
    (hgood : ∀ i, ¬ Bad w r i (r i)) (hfinal : value w r = 0) : ∀ b, w b = 0 := by
  by_contra h
  push Not at h
  have hp : ∀ n, n ≤ d → ∃ b, table w r n b ≠ 0 := by
    intro n hn
    induction n with
    | zero => exact h
    | succ n ih =>
      have hnd : n < d := by omega
      let i : Fin d := ⟨n,hnd⟩
      have hprev := ih (by omega)
      have hnxt : ¬ ∀ b, collapse (table w r n) i (r i) b = 0 :=
        fun he => hgood i ⟨hprev,he⟩
      push Not at hnxt
      simpa only [show n+1=i.val+1 from rfl, table_step] using hnxt
  obtain ⟨b,hb⟩ := hp d le_rfl
  exact hb ((table_final w r b).trans hfinal)

/-- Integer-indexed output or assertion tables use the same tracker. -/
theorem indexed_zero_of_no_bad (w : Fin (2^d) → F) (r : Fin d → F)
    (hgood : ∀ i, ¬ Bad (fun b => w ((binaryLabelEquiv d).symm b)) r i (r i))
    (hfinal : evalTable w r = 0) : ∀ i, w i = 0 := by
  rw [evalTable_eq_value] at hfinal
  have h := zero_of_no_bad _ r hgood hfinal
  intro i
  simpa using h (binaryLabelEquiv d i)

/-- Removing hand-one rounds from the actual interleaved schedule leaves the
little-endian coordinate order used by the prefix tracker. -/
theorem hand_zero_schedule :
    (LayerSumcheck.schedule d).filterMap (fun v => if v.1 then none else some v.2) =
      List.finRange d := by
  simp [LayerSumcheck.schedule, List.filterMap_flatMap]

theorem paired_length {α : Type} (l : List α) :
    (l.flatMap fun a => [(false,a),(true,a)]).length = 2*l.length := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Nat.mul_add, Nat.add_comm]; omega

theorem paired_get_zero {α : Type} (l : List α) (n : ℕ) (hn : n < l.length) :
    (l.flatMap fun a => [(false,a),(true,a)]).get
      ⟨2*n, by rw [paired_length]; omega⟩ = (false, l.get ⟨n,hn⟩) := by
  induction l generalizing n with
  | nil => simp at hn
  | cons a l ih =>
    cases n with
    | zero => rfl
    | succ n => simpa [List.flatMap_cons, Nat.mul_add] using ih n (by simpa using hn)

/-- The false-hand challenge at bit i is exactly scalar round 2*i. -/
def zeroRound (i : Fin d) : Fin (LayerSumcheck.schedule d).length :=
  ⟨2*i.val, by rw [LayerSumcheck.schedule_length]; omega⟩

@[simp] theorem zeroRound_val (i : Fin d) : (zeroRound i).val = 2*i.val := rfl

@[simp] theorem schedule_get_zeroRound (i : Fin d) :
    (LayerSumcheck.schedule d).get (zeroRound i) = (false,i) := by
  have h := paired_get_zero (List.finRange d) i.val (by simp)
  simpa [LayerSumcheck.schedule, zeroRound] using h

theorem zeroRound_strictMono : StrictMono (zeroRound (d := d)) := by
  intro i j hij
  change 2*i.val < 2*j.val
  exact Nat.mul_lt_mul_of_pos_left hij (by decide)

end
end GordieHowe.GKR.AssertionTracking
