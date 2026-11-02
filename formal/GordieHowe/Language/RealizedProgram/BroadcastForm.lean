-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.Interval

@[expose] public section

/-!
# GordieHowe: a polynomial broadcast in any form, on the integers

`NamedOp.applyInt_polyBroadcast` (`GordieHowe/Language/RealizedProgram/Interval.lean`) reads a
`polyBroadcast t K .coefficients` operator on the integers. This file reads the operator in any
form (`ConvForm`: coefficients, or a spectrum in scheme or natural order), its polynomials read
through `NamedOp.formPoly`, as `NamedOp.applyInt_negacyclicConv` reads a negacyclic convolution:

* `NamedOp.pbPolyForm`: the polynomial of row block `r`, in its form;
* `NamedOp.pbEntryForm`: a matrix entry, the negacyclic coefficient of that polynomial;
* `NamedOp.block_polyBroadcast_form`, `NamedOp.apply_polyBroadcast_form`,
  `NamedOp.applyInt_polyBroadcast_form`: the operator, in the field and on the integers, as sums
  over its matrix entries.

At the form `.coefficients` these are `pbPoly`, `pbEntry` and the lemmas of `Interval.lean`
(`pbEntryForm_coefficients`).
-/

namespace GordieHowe.RealizedProgram

namespace NamedOp

variable (ir : RealizedProgram) {I : Interp}

/-- **The polynomial of row block `r` of a `polyBroadcast t K form` operator** in field `f`, in
its form (`formPoly`): the `n = |t| / K` coordinates of block `r` of `t`, read as coefficients or
as a spectrum. -/
def pbPolyForm {f : ℕ} (leaf : ir.Valuation I) (t K r : ℕ) (form : ConvForm) : ℕ → (I f).K :=
  formPoly f ((ir.value t).size / K)
    (fun s => castElt (leaf t (r * ((ir.value t).size / K) + s))) form

/-- **A `polyBroadcast t K form` matrix entry**: column `k` of row `j` is the negacyclic
coefficient `C_k(j mod n)` of polynomial `⌊j / n⌋` in its form, below `K n` rows, and `0` past
them. -/
def pbEntryForm {f : ℕ} (leaf : ir.Valuation I) (t K : ℕ) (form : ConvForm) (j k : ℕ) : (I f).K :=
  if j < K * ((ir.value t).size / K) then
    Ops.negCoef ((ir.value t).size / K)
      (pbPolyForm ir leaf t K (j / ((ir.value t).size / K)) form) (j % ((ir.value t).size / K)) k
  else 0

/-- **At the form `.coefficients`** the entry is `pbEntry`. -/
theorem pbEntryForm_coefficients {f : ℕ} (leaf : ir.Valuation I) (t K j k : ℕ) :
    pbEntryForm (f := f) ir leaf t K .coefficients j k = pbEntry ir leaf t K j k := rfl

/-- **A `polyBroadcast` operator in any form on one block** is the sum of its matrix entries
against the operand. -/
theorem block_polyBroadcast_form {f : ℕ} (leaf : ir.Valuation I) (t K : ℕ) (form : ConvForm)
    (y : ℕ → (I f).K) (j : ℕ) :
    block ir f leaf (.polyBroadcast t K form) y j =
      ∑ k : Fin ((ir.value t).size / K), pbEntryForm ir leaf t K form j k * y k := by
  simp only [block, pbEntryForm, pbPolyForm]
  split_ifs with hj
  · have hn0 : 0 < (ir.value t).size / K := by
      rcases Nat.eq_zero_or_pos ((ir.value t).size / K) with h | h
      · rw [h, Nat.mul_zero] at hj
        omega
      · exact h
    rw [Ops.negacyclic_eq_sum _ _ _ (Nat.mod_lt _ hn0), Fin.sum_univ_eq_sum_range
      (fun k => Ops.negCoef ((ir.value t).size / K)
        (formPoly f ((ir.value t).size / K) (fun s => castElt (leaf t
          (j / ((ir.value t).size / K) * ((ir.value t).size / K) + s))) form)
          (j % ((ir.value t).size / K)) k * y k) ((ir.value t).size / K)]
    rfl
  · simp

/-- **A `polyBroadcast` operator's column `k`** is its matrix entry. -/
theorem block_polyBroadcast_form_unit {f : ℕ} (leaf : ir.Valuation I) (t K : ℕ) (form : ConvForm)
    (j : ℕ) (k : Fin ((ir.value t).size / K)) :
    block ir f leaf (.polyBroadcast t K form) (fun s => if s = k then 1 else 0) j =
      pbEntryForm ir leaf t K form j k := by
  rw [block_polyBroadcast_form, Finset.sum_eq_single k]
  · simp
  · intro k' _ hk'
    have : (k' : ℕ) ≠ k := fun h => hk' (Fin.ext h)
    simp [this]
  · simp

/-- **A `polyBroadcast` operator in any form along the last axis**: output coordinate `j` is the
sum of the entries of row `j mod rows` against block `j / rows` of the operand. -/
theorem apply_polyBroadcast_form {f : ℕ} (leaf : ir.Valuation I) (t K : ℕ) (form : ConvForm)
    (x : ℕ → (I f).K) (j : ℕ) :
    apply ir f leaf (.polyBroadcast t K form) x j =
      ∑ k : Fin ((ir.value t).size / K),
        pbEntryForm ir leaf t K form (j % rows ir (.polyBroadcast t K form)) k *
          x (j / rows ir (.polyBroadcast t K form) * cols ir (.polyBroadcast t K form) + k) := by
  unfold apply
  rw [block_polyBroadcast_form]

/-- **A `polyBroadcast` operator in any form on the integers** (`applyInt`): output coordinate `j`
is the sum of the integer readings (`FieldInterp.coefInt`) of the entries of row `j mod rows`
against block `j / rows` of the operand. -/
theorem applyInt_polyBroadcast_form {f : ℕ} (leaf : ir.Valuation I) (t K : ℕ) (form : ConvForm)
    (x : ℕ → ℤ) (j : ℕ) :
    applyInt ir f leaf (.polyBroadcast t K form) x j =
      ∑ k : Fin ((ir.value t).size / K),
        (I f).coefInt (pbEntryForm ir leaf t K form (j % rows ir (.polyBroadcast t K form)) k) *
          x (j / rows ir (.polyBroadcast t K form) * cols ir (.polyBroadcast t K form) + k) := by
  unfold applyInt
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [block_polyBroadcast_form_unit ir leaf t K form _ (k : Fin ((ir.value t).size / K))]

/-- **Coordinate `k` of row block `r` of a `polyBroadcast` operator on one operand block**, on the
integers: for `t` of `K` polynomials of `n` coefficients, output coordinate `r n + k` is the sum of
the integer readings of the negacyclic coefficients `C_s(k)` of polynomial `r` in its form against
the operand's first block. -/
theorem applyInt_polyBroadcast_block {f : ℕ} (leaf : ir.Valuation I) (t K n : ℕ) (form : ConvForm)
    (x : ℕ → ℤ) (hsz : (ir.value t).size = K * n) {r k : ℕ} (hr : r < K) (hk : k < n) :
    applyInt ir f leaf (.polyBroadcast t K form) x (r * n + k) =
      ∑ s : Fin n, (I f).coefInt (Ops.negCoef n
        (formPoly f n (fun s => castElt (leaf t (r * n + s))) form) k s) * x s := by
  have hK : 0 < K := by omega
  have hn0 : 0 < n := by omega
  have hn : (ir.value t).size / K = n := by rw [hsz, Nat.mul_div_cancel_left _ hK]
  have hJ : r * n + k < K * n := by
    calc r * n + k < r * n + n := by omega
      _ = (r + 1) * n := by ring
      _ ≤ K * n := Nat.mul_le_mul_right _ hr
  have hdiv : (r * n + k) / n = r := by
    rw [Nat.mul_comm, Nat.mul_add_div hn0, Nat.div_eq_of_lt hk, Nat.add_zero]
  have hmod : (r * n + k) % n = k := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hk]
  rw [applyInt_polyBroadcast_form]
  simp only [rows, cols]
  rw [Fin.sum_univ_eq_sum_range (fun s => (I f).coefInt (pbEntryForm ir leaf t K form
      ((r * n + k) % (ir.value t).size) s) *
      x ((r * n + k) / (ir.value t).size * ((ir.value t).size / K) + s)) ((ir.value t).size / K),
    Fin.sum_univ_eq_sum_range (fun s => (I f).coefInt (Ops.negCoef n
      (formPoly f n (fun s => castElt (leaf t (r * n + s))) form) k s) * x s) n, hn]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [hsz, Nat.mod_eq_of_lt hJ, Nat.div_eq_of_lt hJ, Nat.zero_mul, Nat.zero_add]
  congr 2
  unfold pbEntryForm pbPolyForm
  rw [hn, if_pos hJ, hdiv, hmod]

end NamedOp

end GordieHowe.RealizedProgram
