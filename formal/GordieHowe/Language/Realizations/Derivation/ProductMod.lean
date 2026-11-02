-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Derivation.Rules
public import GordieHowe.Language.Realizations.Derivation.Ntt
public import GordieHowe.Language.RealizedProgram.SpectralSound
public import GordieHoweNative.Language.Realizations.Derivation.ProductMod

@[expose] public section

/-!
# GordieHowe: derivations, the product form of `mod_q`

The rule `productMod ks` (`GordieHowe.RealizedProgram.productModFact`, the C++ checker's
`product_mod` in `lib/gordiehowe/compiler/derivation_check.h`) concludes the derivation's predicate
`mod_m P N`, a `mod_q` in the product form (`ModForm.product`, `ModForm.spectralProduct`,
`GordieHowe/Language/Realizations/ProductForm.lean`) with quotient `Q` and lower end `qlo`, from

* premise `ks[0]`: `nat d Q N_Q`;
* then for `P` and for `N` in turn, the side's interval: for a side without kernel parts, one
  `ivl` premise of the side; for a side with kernel parts, per row (`rowsAt`) and per summand in
  order, a kernel part `s · K(x)` as a `kernel` fact of its spectra and an `ivl` fact of its
  operand `x`, an expression part as an `ivl` fact of the part; the side's interval is the hull over
  the rows of the sum of the parts' intervals, a kernel part's `centred(s) · negIvl(n, H, X)`
  (`negIvl`, the C++ `int_interval::negacyclic`).

With `[Plo, Phi]` and `[Nlo, Nhi]` those intervals, `C = m qlo`, `d0 = Plo − Nlo − C`,
`a0 = max(d0, 0)`, `b0 = max(−d0, 0)`, its side conditions are the C++'s:
`(Phi − Plo) + a0 < p` (the certificate `leftSpan`) and `(Nhi − Nlo) + b0 + m (N_Q − 1) < p`
(`rightSpan`), with `2 < m < p` (the C++ reads `2 ≤ m`), the lengths of `P`, `N` and `Q` equal, and the program's
structural check of the form (`productOkB`: the rows of `n` coordinates, every kernel a
negacyclic convolution or a polynomial broadcast by a value of blocks of `n` coordinates in the
form's transform (`NamedOp.kernel?_spec`), and the transform's root valid, `rootOkB`). It also checks `(Phi − Nlo) / m − qlo ≤ qmax`.

**Soundness** (`productModFact_sound`): the predicate's placed equation (`RealizedAt.product`) is,
in the spectral form, the equation in the spectrum row by row; the transform is linear, a kernel
part's transform is `s · h ⊙ T(x)` (the convolution theorem at the form's root and the inverse
transform's inverse, `Ops.nttNatural_inverseNttNatural`, `Ops.nttScheme_inverseNtt`), and the
transform is injective, so `P − N = m qlo + m Q` in the field coordinate by coordinate
(`productPlaced_coeff`). Then `P − Plo + a0` and `N − Nlo + m Q + b0` lie in `[0, p)` and agree
modulo `p`, so they are equal: `D = P − N = m (qlo + Q)` over the integers, and `Q ≤ qmax`
(`ProductQuotWith`). The converse direction of the placed equation (`productPlaced_of_coeff`) is
the honest prover's.

The definitions are in `GordieHoweNative/Language/Realizations/Derivation/ProductMod.lean`
(the compiled library `GordieHoweNative`); this module has their lemmas.
-/

namespace GordieHowe.RealizedProgram

open Export

/-! ## The negacyclic interval -/

/-- **A sum over `range n` of `u` up to `j` and `v` past it** is `(j + 1) u + (n − 1 − j) v`. -/
theorem sum_range_ite_le (n j : ℕ) (hj : j < n) (u v : ℤ) :
    ∑ k ∈ Finset.range n, (if k ≤ j then u else v) = ((j + 1 : ℕ) : ℤ) * u +
      ((n - 1 - j : ℕ) : ℤ) * v := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [Finset.sum_range_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hlt | rfl
    · rw [ih hlt, if_neg (by omega)]
      have : n + 1 - 1 - j = (n - 1 - j) + 1 := by omega
      rw [this]
      push_cast
      ring
    · rw [if_pos le_rfl]
      have h0 : ∀ k ∈ Finset.range j, (if k ≤ j then u else v) = u := fun k hk => by
        rw [if_pos (by simp at hk; omega)]
      rw [Finset.sum_congr rfl h0, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have : j + 1 - 1 - j = 0 := by omega
      rw [this]
      push_cast
      ring

/-- **A coefficient of a negacyclic product lies in `negIvl`**: coordinate `j < n` of the integer
negacyclic product of `h` (coefficients in `H`) and `x` (in `X`). -/
theorem negIvl_mem {n : ℕ} {H Xi : Ivl} {h x : ℕ → ℤ} (hh : ∀ s < n, h s ∈ H)
    (hx : ∀ s < n, x s ∈ Xi) {j : ℕ} (hj : j < n) :
    ∑ k ∈ Finset.range n, Ops.negCoef n h j k * x k ∈ negIvl n H Xi := by
  set a := (H.mul Xi).lo
  set b := (H.mul Xi).hi
  -- each term is a product of the ends' intervals, added up to `j` and subtracted after
  have hterm : ∀ k ∈ Finset.range n, (if k ≤ j then a else -b) ≤ Ops.negCoef n h j k * x k ∧
      Ops.negCoef n h j k * x k ≤ (if k ≤ j then b else -a) := by
    intro k hk
    have hk' : k < n := Finset.mem_range.1 hk
    rw [Ops.negCoef_eq]
    by_cases hkj : k ≤ j
    · rw [if_pos (show k ≤ j ∧ j - k < n from ⟨hkj, by omega⟩),
        if_neg (show ¬ (k ≤ j + n ∧ j + n - k < n) by omega), sub_zero, if_pos hkj, if_pos hkj]
      exact Ivl.mul_mem (hh _ (by omega)) (hx k hk')
    · rw [if_neg (show ¬ (k ≤ j ∧ j - k < n) by omega),
        if_pos (show k ≤ j + n ∧ j + n - k < n from ⟨by omega, by omega⟩), zero_sub, if_neg hkj,
        if_neg hkj, neg_mul]
      have := Ivl.mul_mem (hh (j + n - k) (by omega)) (hx k hk')
      exact ⟨neg_le_neg this.2, neg_le_neg this.1⟩
  have hlo := Finset.sum_le_sum fun k hk => (hterm k hk).1
  have hhi := Finset.sum_le_sum fun k hk => (hterm k hk).2
  rw [sum_range_ite_le n j hj] at hlo hhi
  have hab : a ≤ b := by
    have := Ivl.mul_mem (hh 0 (by omega)) (hx 0 (by omega))
    exact this.1.trans this.2
  have hj1 : ((j + 1 : ℕ) : ℤ) ≤ n := by exact_mod_cast hj
  have hn1 : ((n - 1 - j : ℕ) : ℤ) = n - 1 - j := by omega
  have hn1' : ((n - 1 : ℕ) : ℤ) = n - 1 := by omega
  have hj0 : (0 : ℤ) ≤ j := by positivity
  constructor
  · refine le_trans ?_ hlo
    simp only [negIvl, hn1, hn1']
    push_cast
    rcases le_total 0 (a + b) with hs | hs
    · exact (min_le_right _ _).trans (by nlinarith)
    · exact (min_le_left _ _).trans (by nlinarith)
  · refine hhi.trans ?_
    simp only [negIvl, hn1, hn1']
    push_cast
    rcases le_total 0 (a + b) with hs | hs
    · exact (by nlinarith : _ ≤ (n : ℤ) * b).trans (le_max_left _ _)
    · exact (by nlinarith : _ ≤ b - ((n : ℤ) - 1) * a).trans (le_max_right _ _)

/-! ## The transforms -/

namespace Ops

variable {K : Type*} [Field K]

/-- **The natural-order transform is linear**: `T(x + a y) = T x + a T y`. -/
theorem nttNatural_add_smul (n : ℕ) (ψ a : K) (x y : ℕ → K) (k : ℕ) :
    nttNatural n ψ (fun i => a * x i + y i) k = a * nttNatural n ψ x k + nttNatural n ψ y k := by
  unfold nttNatural ofFin
  split_ifs
  · simp only [DFT.negSpectrum, toFin_apply, add_mul, Finset.sum_add_distrib, Finset.mul_sum,
      mul_assoc]
  · simp

/-- **The transform in either order is linear**: `T(x + a y) = T x + a T y`. -/
theorem nttOf_add_smul (nat : Bool) (n : ℕ) (ψ a : K) (x y : ℕ → K) (k : ℕ) :
    nttOf nat n ψ (fun i => a * x i + y i) k = a * nttOf nat n ψ x k + nttOf nat n ψ y k := by
  unfold nttOf
  cases nat
  · simp only [Bool.false_eq_true, ↓reduceIte, nttScheme]
    split_ifs
    · exact nttNatural_add_smul _ _ _ _ _ _
    · simp
  · exact nttNatural_add_smul _ _ _ _ _ _

/-- **The natural-order transform of `0` is `0`.** -/
theorem nttNatural_zero (n : ℕ) (ψ : K) (k : ℕ) : nttNatural n ψ (fun _ => 0) k = 0 := by
  unfold nttNatural ofFin
  split_ifs <;> simp [DFT.negSpectrum]

/-- **The transform of `0` is `0`.** -/
theorem nttOf_zero (nat : Bool) (n : ℕ) (ψ : K) (k : ℕ) : nttOf nat n ψ (fun _ => 0) k = 0 := by
  unfold nttOf
  cases nat <;> simp [nttScheme, nttNatural_zero]

/-- **The transform commutes with scalars.** -/
theorem nttOf_smul (nat : Bool) (n : ℕ) (ψ a : K) (x : ℕ → K) (k : ℕ) :
    nttOf nat n ψ (fun i => a * x i) k = a * nttOf nat n ψ x k := by
  have h := nttOf_add_smul nat n ψ a x (fun _ => 0) k
  simp only [add_zero, nttOf_zero] at h
  exact h

theorem nttOf_add (nat : Bool) (n : ℕ) (ψ : K) (x y : ℕ → K) (k : ℕ) :
    nttOf nat n ψ (fun i => x i + y i) k = nttOf nat n ψ x k + nttOf nat n ψ y k := by
  have h := nttOf_add_smul nat n ψ 1 x y k
  simp only [one_mul] at h
  exact h

/-- **The transform of a difference** is the difference of the transforms. -/
theorem nttOf_sub (nat : Bool) (n : ℕ) (ψ : K) (x y : ℕ → K) (k : ℕ) :
    nttOf nat n ψ (fun i => x i - y i) k = nttOf nat n ψ x k - nttOf nat n ψ y k := by
  have h := nttOf_add_smul nat n ψ (-1) y x k
  simp only [neg_one_mul] at h
  have e : (fun i => x i - y i) = fun i => -y i + x i := funext fun i => by ring
  rw [e, h]
  ring

/-- **The transform of a list's sum** is the sum of the transforms. -/
theorem nttOf_listSum {α : Type*} (nat : Bool) (n : ℕ) (ψ : K) (l : List α) (f : α → ℕ → K)
    (k : ℕ) : nttOf nat n ψ (fun i => (l.map fun t => f t i).sum) k =
      (l.map fun t => nttOf nat n ψ (f t) k).sum := by
  induction l with
  | nil => simpa using nttOf_zero nat n ψ k
  | cons t l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [nttOf_add, ih]

/-- **The transform reads the first `n` coordinates only.** -/
theorem nttOf_congr {nat : Bool} {n : ℕ} {ψ : K} {x y : ℕ → K} (h : ∀ i < n, x i = y i) (k : ℕ) :
    nttOf nat n ψ x k = nttOf nat n ψ y k := by
  unfold nttOf
  have hn : nttNatural n ψ x = nttNatural n ψ y := by
    funext m
    unfold nttNatural
    have : toFin n x = toFin n y := funext fun i => h i i.isLt
    rw [this]
  cases nat
  · simp only [Bool.false_eq_true, ↓reduceIte, nttScheme, hn]
  · simp only [↓reduceIte, hn]

/-- **The natural-order transform of a negacyclic product** is the product of the transforms, at a
root `ψ` with `ψ^n = −1` (`DFT.negSpectrum_negacyclicConvCoeff`). -/
theorem nttNatural_negacyclic {n : ℕ} {ψ : K} (hψ : ψ ^ n = -1) (g x : ℕ → K) {k : ℕ}
    (hk : k < n) :
    nttNatural n ψ (negacyclic n g x) k = nttNatural n ψ g k * nttNatural n ψ x k := by
  simp only [nttNatural, ofFin_of_lt _ hk]
  rw [toFin_negacyclic, DFT.negSpectrum_negacyclicConvCoeff hψ]
  rfl

end Ops

/-! ## The structure of a product form -/

/-- **The transform form of natural order `nat` at the root `psi`.** -/
def formOf (nat : Bool) (psi : ℕ) : ConvForm := if nat then .nttNatural psi else .ntt psi

/-- **The meaning of a kernel operator** (`NamedOp.kernel?`), a negacyclic convolution and a
polynomial broadcast alike: for a kernel of value `v` holding `K` blocks of `n` coordinates, the
operator reads `n` coordinates and writes `K n` per block, and output coordinate `b n + i`
(`b < K`, `i < n`) is coordinate `i` of the negacyclic product of the operand with block `b` of `v`
in the kernel's form. A negacyclic convolution is the case `K = 1`. -/
theorem NamedOp.kernel?_spec (ir : RealizedProgram) {I : Interp} {op : NamedOp} {v K psi : ℕ}
    {nat : Bool} (h : op.kernel? = some (v, K, psi, nat)) {n : ℕ}
    (hsz : (ir.value v).size = K * n) (hK : 0 < K) :
    NamedOp.rows ir op = K * n ∧ NamedOp.cols ir op = n ∧
      ∀ (f : ℕ) (leaf : ∀ v : ℕ, ℕ → (I (ir.valueField v)).K) (x : ℕ → (I f).K) {b i : ℕ},
        b < K → i < n → NamedOp.block ir f leaf op x (b * n + i) =
          Ops.negacyclic n (NamedOp.formPoly f n (fun s => castElt (leaf v (b * n + s)))
            (formOf nat psi)) x i := by
  unfold NamedOp.kernel? at h
  have hdiv : K * n / K = n := Nat.mul_div_cancel_left n hK
  split at h <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  all_goals first
    | (rw [Nat.one_mul] at hsz
       refine ⟨by simp [NamedOp.rows, hsz], by simp [NamedOp.cols, hsz], fun f leaf x b i hb hi => ?_⟩
       obtain rfl : b = 0 := by omega
       simp [NamedOp.block, hsz, formOf])
    | (refine ⟨by simp [NamedOp.rows, hsz], by simp [NamedOp.cols, hsz, hdiv],
         fun f leaf x b i hb hi => ?_⟩
       have hn : 0 < n := by omega
       have hlt : b * n + i < (b + 1) * n := by nlinarith
       have hd : (b * n + i) / n = b := by
         rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hi, Nat.zero_add]
       have hm : (b * n + i) % n = i := by
         rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
       simp only [NamedOp.block, hsz, hdiv, hd, hm]
       rw [if_pos (lt_of_lt_of_le hlt (Nat.mul_le_mul_right n hb))]
       simp [formOf])

/-! ## Evaluation through rows and summands -/

section Eval

variable {ir : RealizedProgram} {I : Interp}

/-- **An expression that is no concatenation is its own one row.** -/
theorem rowsAt_of_not_concat {n : ℕ} (e : Expr) (h : ∀ a b, e ≠ .concat a b) :
    ir.rowsAt n e = [e] := by
  cases e <;> first | rfl | exact absurd rfl (h _ _)

/-- **An expression that is no sum is its own one summand.** -/
theorem summands_of_not_add (e : Expr) (h : ∀ a b, e ≠ .add a b) : e.summands = [e] := by
  cases e <;> first | rfl | exact absurd rfl (h _ _)

/-- **A side whose rows have `n` coordinates has `n` times as many coordinates as rows.** -/
theorem exprLen_eq_rowsAt {n : ℕ} :
    ∀ {e : Expr}, (∀ r ∈ ir.rowsAt n e, ir.exprLen r = n) →
      ir.exprLen e = (ir.rowsAt n e).length * n
  | .concat a b, h => by
    simp only [rowsAt] at h ⊢
    split_ifs with hlt
    · rw [List.length_append, Nat.add_mul, exprLen_concat,
        exprLen_eq_rowsAt fun r hr => h r (by simp only [if_pos hlt]; exact List.mem_append_left _ hr),
        exprLen_eq_rowsAt fun r hr => h r (by simp only [if_pos hlt]; exact List.mem_append_right _ hr)]
    · have := h (.concat a b) (by simp [if_neg hlt])
      simp [this]
  | .leaf _, h | .add _ _, h | .sub _ _, h | .scale _ _, h | .mul _ _, h | .reindex _ _, h
  | .linear _ _, h | .prod _ _, h | .mux _ _ _, h | .apply _ _, h | .ref _, h
  | .logic _ _ _, h => by
    rw [rowsAt_of_not_concat _ (fun a b h' => by cases h')] at h ⊢
    rw [List.length_singleton, one_mul]
    exact h _ (List.mem_singleton_self _)

/-- **Coordinate `r n + i` of a side is coordinate `i` of its row `r`**, its rows of `n`
coordinates (in the field). -/
theorem evalWith_rowsAt (rd : ir.Valuation I) (d : ℕ) {n : ℕ} :
    ∀ {e : Expr}, (∀ r ∈ ir.rowsAt n e, ir.exprLen r = n) → ∀ {r i : ℕ},
      r < (ir.rowsAt n e).length → i < n →
      ir.evalWith rd d e (r * n + i) = ir.evalWith rd d ((ir.rowsAt n e).getD r default) i
  | .concat a b, h, r, i, hr, hi => by
    simp only [rowsAt] at h hr ⊢
    split_ifs at h hr ⊢ with hlt
    · have ha : ∀ r ∈ ir.rowsAt n a, ir.exprLen r = n := fun r hr => h r (List.mem_append_left _ hr)
      have hb : ∀ r ∈ ir.rowsAt n b, ir.exprLen r = n := fun r hr => h r (List.mem_append_right _ hr)
      have hla := exprLen_eq_rowsAt ha
      simp only [evalWith, evalE_concat]
      rw [List.length_append] at hr
      by_cases hra : r < (ir.rowsAt n a).length
      · have hlt' : r * n + i < ir.exprLen a := by
          rw [hla]
          nlinarith
        rw [if_pos hlt', List.getD_append _ _ _ _ hra]
        exact evalWith_rowsAt rd d ha hra hi
      · have hge : ¬ r * n + i < ir.exprLen a := by
          rw [hla]
          push_neg
          nlinarith
        rw [if_neg hge, List.getD_append_right _ _ _ _ (by omega)]
        have hrb : r - (ir.rowsAt n a).length < (ir.rowsAt n b).length := by omega
        have heq : r * n + i - ir.exprLen a = (r - (ir.rowsAt n a).length) * n + i := by
          rw [hla, Nat.sub_mul]
          have : (ir.rowsAt n a).length * n ≤ r * n := Nat.mul_le_mul_right _ (by omega)
          omega
        rw [heq]
        exact evalWith_rowsAt rd d hb hrb hi
    · simp only [List.length_singleton, Nat.lt_one_iff] at hr
      subst hr
      simp
  | .leaf _, _, r, i, hr, hi | .add _ _, _, r, i, hr, hi | .sub _ _, _, r, i, hr, hi
  | .scale _ _, _, r, i, hr, hi | .mul _ _, _, r, i, hr, hi | .reindex _ _, _, r, i, hr, hi
  | .linear _ _, _, r, i, hr, hi | .prod _ _, _, r, i, hr, hi | .mux _ _ _, _, r, i, hr, hi
  | .apply _ _, _, r, i, hr, hi | .ref _, _, r, i, hr, hi | .logic _ _ _, _, r, i, hr, hi => by
    rw [rowsAt_of_not_concat _ (fun a b h' => by cases h')] at hr ⊢
    simp only [List.length_singleton, Nat.lt_one_iff] at hr
    subst hr
    simp

/-- **Coordinate `r n + i` of a side is coordinate `i` of its row `r`**, on the integers. -/
theorem evalIntWith_rowsAt (rd : ir.Valuation I) (d : ℕ) {n : ℕ} :
    ∀ {e : Expr}, (∀ r ∈ ir.rowsAt n e, ir.exprLen r = n) → ∀ {r i : ℕ},
      r < (ir.rowsAt n e).length → i < n →
      ir.evalIntWith rd d e (r * n + i) = ir.evalIntWith rd d ((ir.rowsAt n e).getD r default) i
  | .concat a b, h, r, i, hr, hi => by
    simp only [rowsAt] at h hr ⊢
    split_ifs at h hr ⊢ with hlt
    · have ha : ∀ r ∈ ir.rowsAt n a, ir.exprLen r = n := fun r hr => h r (List.mem_append_left _ hr)
      have hb : ∀ r ∈ ir.rowsAt n b, ir.exprLen r = n := fun r hr => h r (List.mem_append_right _ hr)
      have hla := exprLen_eq_rowsAt ha
      rw [evalIntWith_concat]
      rw [List.length_append] at hr
      by_cases hra : r < (ir.rowsAt n a).length
      · have hlt' : r * n + i < ir.exprLen a := by
          rw [hla]
          nlinarith
        rw [if_pos hlt', List.getD_append _ _ _ _ hra]
        exact evalIntWith_rowsAt rd d ha hra hi
      · have hge : ¬ r * n + i < ir.exprLen a := by
          rw [hla]
          push_neg
          nlinarith
        rw [if_neg hge, List.getD_append_right _ _ _ _ (by omega)]
        have hrb : r - (ir.rowsAt n a).length < (ir.rowsAt n b).length := by omega
        have heq : r * n + i - ir.exprLen a = (r - (ir.rowsAt n a).length) * n + i := by
          rw [hla, Nat.sub_mul]
          have : (ir.rowsAt n a).length * n ≤ r * n := Nat.mul_le_mul_right _ (by omega)
          omega
        rw [heq]
        exact evalIntWith_rowsAt rd d hb hrb hi
    · simp only [List.length_singleton, Nat.lt_one_iff] at hr
      subst hr
      simp
  | .leaf _, _, r, i, hr, hi | .add _ _, _, r, i, hr, hi | .sub _ _, _, r, i, hr, hi
  | .scale _ _, _, r, i, hr, hi | .mul _ _, _, r, i, hr, hi | .reindex _ _, _, r, i, hr, hi
  | .linear _ _, _, r, i, hr, hi | .prod _ _, _, r, i, hr, hi | .mux _ _ _, _, r, i, hr, hi
  | .apply _ _, _, r, i, hr, hi | .ref _, _, r, i, hr, hi | .logic _ _ _, _, r, i, hr, hi => by
    rw [rowsAt_of_not_concat _ (fun a b h' => by cases h')] at hr ⊢
    simp only [List.length_singleton, Nat.lt_one_iff] at hr
    subst hr
    simp

/-- **An add tree is the sum of its summands** (in the field). -/
theorem evalWith_summands (rd : ir.Valuation I) (d : ℕ) :
    ∀ (e : Expr) (i : ℕ), ir.evalWith rd d e i = (e.summands.map fun t => ir.evalWith rd d t i).sum
  | .add a b, i => by
    rw [Expr.summands, List.map_append, List.sum_append, ← evalWith_summands rd d a i,
      ← evalWith_summands rd d b i]
    simp only [evalWith, evalE_add]
  | .leaf _, _ | .sub _ _, _ | .scale _ _, _ | .mul _ _, _ | .reindex _ _, _ | .concat _ _, _
  | .linear _ _, _ | .prod _ _, _ | .mux _ _ _, _ | .apply _ _, _ | .ref _, _
  | .logic _ _ _, _ => by
    rw [summands_of_not_add _ (fun a b h' => by cases h')]
    simp

/-- **An add tree is the sum of its summands**, on the integers. -/
theorem evalIntWith_summands (rd : ir.Valuation I) (d : ℕ) :
    ∀ (e : Expr) (i : ℕ),
      ir.evalIntWith rd d e i = (e.summands.map fun t => ir.evalIntWith rd d t i).sum
  | .add a b, i => by
    rw [Expr.summands, List.map_append, List.sum_append, ← evalIntWith_summands rd d a i,
      ← evalIntWith_summands rd d b i, evalIntWith_add]
  | .leaf _, _ | .sub _ _, _ | .scale _ _, _ | .mul _ _, _ | .reindex _ _, _ | .concat _ _, _
  | .linear _ _, _ | .prod _ _, _ | .mux _ _ _, _ | .apply _ _, _ | .ref _, _
  | .logic _ _ _, _ => by
    rw [summands_of_not_add _ (fun a b h' => by cases h')]
    simp

/-- **A sum over a list split by a partial classification**: the unclassified terms' sum plus the
classified terms' sum, each classified term's value its class's. -/
theorem list_sum_split {α β M : Type*} [AddCommMonoid M] (l : List α) (c : α → Option β)
    (f : α → M) (g : β → M) (h : ∀ a ∈ l, ∀ b, c a = some b → f a = g b) :
    (l.map f).sum = ((l.filter fun a => (c a).isNone).map f).sum + ((l.filterMap c).map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ih' := ih fun a' ha' b hb => h a' (List.mem_cons_of_mem _ ha') b hb
    cases hc : c a with
    | none =>
      simp only [List.map_cons, List.sum_cons, List.filter_cons, hc, Option.isNone_none,
        ↓reduceIte, List.filterMap_cons, ih']
      rw [add_assoc]
    | some b =>
      simp only [List.map_cons, List.sum_cons, List.filter_cons, hc, Option.isNone_some,
        Bool.false_eq_true, ↓reduceIte, List.filterMap_cons, ih', h a List.mem_cons_self b hc]
      abel

end Eval

/-! ## A kernel part in the field -/

section Kernel

variable {ir : RealizedProgram} {I : Interp}

/-- **The kernel part of a summand's core**: its scale, its kernel (`NamedOp.kernel?`) of its value,
blocks, root and order, a block below its blocks; the core is the operator on the operand (one
block, block `0`) or a view of one block of it (`blockOf?`). -/
theorem kernelCore?_spec {c : ℕ} {t : Expr} {κ : KernelPart} (h : ir.kernelCore? c t = some κ) :
    κ.scale = c ∧ κ.op.kernel? = some (κ.value, κ.blocks, κ.psi, κ.natural) ∧
      κ.block < κ.blocks ∧
      ((t = .apply κ.op κ.operand ∧ κ.blocks = 1 ∧ κ.block = 0) ∨
        ∃ idx : IndexMap, t = .reindex idx (.apply κ.op κ.operand) ∧
          ∀ i < (ir.value κ.value).size / κ.blocks,
            idx.entry i = κ.block * ((ir.value κ.value).size / κ.blocks) + i) := by
  unfold kernelCore? at h
  split at h
  · rename_i op x
    split at h
    · rename_i v K psi nat hk
      split_ifs at h with hK
      cases h
      exact ⟨rfl, hk, by simp [hK], .inl ⟨rfl, hK, rfl⟩⟩
    · cases h
  · rename_i idx op x
    split at h
    · rename_i v K psi nat hk
      split at h
      · rename_i b hb
        split_ifs at h with hbK
        cases h
        refine ⟨rfl, hk, hbK, .inr ⟨idx, rfl, fun i hi => ?_⟩⟩
        unfold blockOf? at hb
        split at hb
        · rename_i s' c'
          split_ifs at hb with hc
          have hb' := Option.some.inj hb
          obtain ⟨hcn, hn, hs⟩ := hc
          subst hcn
          rw [IndexMap.entry_step_one hi, ← hb', Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hs)]
        · cases hb
      · cases h
    · cases h
  · cases h

/-- **A summand's core reads its operator at the block**: below the block length, coordinate `i`
of the core is coordinate `b n + i` of the operator on the operand, for any reading `g` of
expressions through views. -/
theorem kernelCore?_read {α : Type*} (g : Expr → ℕ → α)
    (hg : ∀ idx e i, g (.reindex idx e) i = g e (idx.entry i)) {c : ℕ} {t : Expr} {κ : KernelPart}
    (h : ir.kernelCore? c t = some κ) {i : ℕ} (hi : i < (ir.value κ.value).size / κ.blocks) :
    g t i = g (.apply κ.op κ.operand) (κ.block * ((ir.value κ.value).size / κ.blocks) + i) := by
  obtain ⟨-, -, -, hshape⟩ := kernelCore?_spec h
  rcases hshape with ⟨rfl, -, hb⟩ | ⟨idx, rfl, he⟩
  · rw [hb, Nat.zero_mul, Nat.zero_add]
  · rw [hg, he i hi]

/-- **A kernel part's operator in the field** at output `b n + i` of a kernel of `K` blocks of `n`:
the negacyclic product of block `b` of its value in its form (`kernelPoly`) with the operand. -/
theorem evalWith_apply_kernel {rd : ir.Valuation I} {d : ℕ} {κ : KernelPart}
    (hk : κ.op.kernel? = some (κ.value, κ.blocks, κ.psi, κ.natural)) {n : ℕ}
    (hsz : (ir.value κ.value).size = κ.blocks * n) (hb : κ.block < κ.blocks) {i : ℕ} (hi : i < n) :
    ir.evalWith rd d (.apply κ.op κ.operand) (κ.block * n + i) =
      Ops.negacyclic n (ir.kernelPoly rd d κ.value κ.block n κ.psi κ.natural)
        (ir.evalWith rd d κ.operand) i := by
  obtain ⟨hr, hc, hblk⟩ := NamedOp.kernel?_spec ir hk hsz (by omega)
  have hlt : κ.block * n + i < κ.blocks * n := by nlinarith
  simp only [evalWith, evalE_apply, NamedOp.apply, hr, hc, Nat.div_eq_of_lt hlt,
    Nat.mod_eq_of_lt hlt, Nat.zero_mul, Nat.zero_add]
  rw [hblk _ rd _ hb hi]
  rfl

/-- **A kernel part in the field**: below the block length `n`, coordinate `i` is the constant
multiple of the negacyclic product of the kernel's block in its form with the operand. -/
theorem evalWith_kernelPart {rd : ir.Valuation I} {d : ℕ} {t : Expr} {κ : KernelPart}
    (ht : ir.kernelPart? t = some κ) {n : ℕ} (hsz : (ir.value κ.value).size = κ.blocks * n)
    (h1 : (I (ir.domainField d)).decode 1 = 1) {i : ℕ} (hi : i < n) :
    ir.evalWith rd d t i = (I (ir.domainField d)).decode κ.scale *
      Ops.negacyclic n (ir.kernelPoly rd d κ.value κ.block n κ.psi κ.natural)
        (ir.evalWith rd d κ.operand) i := by
  have hcore : ∀ {c : ℕ} {e : Expr}, ir.kernelCore? c e = some κ →
      ir.evalWith rd d e i = Ops.negacyclic n (ir.kernelPoly rd d κ.value κ.block n κ.psi κ.natural)
        (ir.evalWith rd d κ.operand) i := by
    intro c e he
    obtain ⟨-, hk, hb, -⟩ := kernelCore?_spec he
    have hn : (ir.value κ.value).size / κ.blocks = n := by
      rw [hsz, Nat.mul_div_cancel_left n (by omega)]
    rw [kernelCore?_read (ir.evalWith rd d) (fun _ _ _ => rfl) he (hn ▸ hi), hn]
    exact evalWith_apply_kernel hk hsz hb hi
  unfold kernelPart? at ht
  split at ht
  · rename_i c e
    have hc := (kernelCore?_spec ht).1
    simp only [evalWith, evalE_scale_const]
    rw [← hc]
    exact congrArg _ (hcore ht)
  · have hc := (kernelCore?_spec ht).1
    rw [hc, h1, one_mul]
    exact hcore ht


/-- **The root facts of the form's transform** at a valid root (`rootOkB`) in a domain's field. -/
structure RootFacts (K : Type*) [Field K] (n : ℕ) (ψ : K) : Prop where
  /-- `ψ` is a primitive `2n`-th root of unity. -/
  prim : IsPrimitiveRoot ψ (2 * n)
  /-- `n` is invertible. -/
  ne : (n : K) ≠ 0
  /-- `n` is a power of two. -/
  pow2 : n = 2 ^ Nat.log2 n
  /-- `ψ^n = −1`. -/
  neg : ψ ^ n = -1

/-- **The transform of the inverse transform** in the form of natural order `nat`. -/
theorem nttOf_formPoly {K : Type*} [Field K] {n : ℕ} {ψ : K} (hr : RootFacts K n ψ) (nat : Bool)
    (y : ℕ → K) {k : ℕ} (hk : k < n) :
    Ops.nttOf nat n ψ (fun i => if nat then Ops.inverseNttNatural n ψ y i else Ops.inverseNtt n ψ y i) k =
      y k := by
  cases nat
  · simp only [Ops.nttOf, Bool.false_eq_true, ↓reduceIte]
    exact Ops.nttScheme_inverseNtt hr.pow2 hr.prim hr.ne y hk
  · simp only [Ops.nttOf, ↓reduceIte]
    exact Ops.nttNatural_inverseNttNatural hr.prim hr.ne y hk

/-- **The convolution theorem in the form of natural order `nat`.** -/
theorem nttOf_negacyclic {K : Type*} [Field K] {n : ℕ} {ψ : K} (hr : RootFacts K n ψ) (nat : Bool)
    (g x : ℕ → K) {k : ℕ} (hk : k < n) :
    Ops.nttOf nat n ψ (Ops.negacyclic n g x) k = Ops.nttOf nat n ψ g k * Ops.nttOf nat n ψ x k := by
  cases nat
  · simp only [Ops.nttOf, Bool.false_eq_true, ↓reduceIte]
    exact Ops.nttScheme_negacyclic hr.pow2 hr.neg g x hk
  · simp only [Ops.nttOf, ↓reduceIte]
    exact Ops.nttNatural_negacyclic hr.neg g x hk

/-- **The transform vanishing below `n` is the zero vector below `n`**, at a valid root. -/
theorem eq_zero_of_nttOf {K : Type*} [Field K] {n : ℕ} {ψ : K} (hr : RootFacts K n ψ) (nat : Bool)
    {x : ℕ → K} (h : ∀ k < n, Ops.nttOf nat n ψ x k = 0) {i : ℕ} (hi : i < n) : x i = 0 := by
  cases nat
  · have he := Ops.toFin_eq_of_nttScheme_eq hr.pow2 hr.prim hr.ne (x := x) (y := fun _ => 0)
      fun m hm => by
        have := h m hm
        simp only [Ops.nttOf, Bool.false_eq_true, ↓reduceIte] at this
        rw [this]
        have hz := Ops.nttOf_zero false n ψ m
        simp only [Ops.nttOf, Bool.false_eq_true, ↓reduceIte] at hz
        exact hz.symm
    exact congrFun he ⟨i, hi⟩
  · have he : Ops.toFin n x = Ops.toFin n (fun _ => (0 : K)) := by
      apply DFT.negSpectrum_injective hr.prim hr.ne
      funext k
      have h1 := h k k.isLt
      have h2 := Ops.nttOf_zero true n ψ k
      simp only [Ops.nttOf, ↓reduceIte, Ops.nttNatural, Ops.ofFin_of_lt _ k.isLt] at h1 h2
      rw [h1, h2]
    exact congrFun he ⟨i, hi⟩

/-- **A kernel part's transform** at frequency `k`: `s · h_k · T(x)_k` (`kernelTerm`), at a
valid root, for a kernel of the row's transform. -/
theorem nttOf_kernelPart {rd : ir.Valuation I} {d : ℕ} {t : Expr} {κ : KernelPart}
    (ht : ir.kernelPart? t = some κ) (h1 : (I (ir.domainField d)).decode 1 = 1) {n psi : ℕ}
    {nat : Bool} (hsz : (ir.value κ.value).size = κ.blocks * n) (hpsi : κ.psi = psi)
    (hnat : κ.natural = nat)
    (hr : RootFacts (I (ir.domainField d)).K n ((I (ir.domainField d)).decode psi)) {k : ℕ}
    (hk : k < n) :
    Ops.nttOf nat n ((I (ir.domainField d)).decode psi) (ir.evalWith rd d t) k =
      ir.kernelTerm rd d nat n ((I (ir.domainField d)).decode psi) κ k := by
  subst hpsi hnat
  rw [Ops.nttOf_congr (fun i hi => evalWith_kernelPart ht hsz h1 hi), Ops.nttOf_smul,
    nttOf_negacyclic hr _ _ _ hk]
  unfold kernelTerm
  have hF : Ops.nttOf κ.natural n ((I (ir.domainField d)).decode κ.psi)
      (ir.kernelPoly rd d κ.value κ.block n κ.psi κ.natural) k =
        castElt (rd κ.value (κ.block * n + k)) := by
    rw [← nttOf_formPoly hr κ.natural
      (fun s => (castElt (rd κ.value (κ.block * n + s)) : (I (ir.domainField d)).K)) hk]
    refine Ops.nttOf_congr (K := (I (ir.domainField d)).K) (fun i _ => ?_) k
    cases κ.natural <;> simp [kernelPoly, NamedOp.formPoly]
  rw [hF]
  ring


end Kernel

/-! ## The spectral equation and the coefficients -/

section Spectral

variable {ir : RealizedProgram} {I : Interp}

/-- **A kernel part's value in the field** at block length `n`: its constant multiple of the
negacyclic product of its kernel's block in its form with the operand. -/
noncomputable def kernelVal (rd : ir.Valuation I) (d n : ℕ) (κ : KernelPart) (i : ℕ) :
    (I (ir.domainField d)).K :=
  (I (ir.domainField d)).decode κ.scale *
    Ops.negacyclic n (ir.kernelPoly rd d κ.value κ.block n κ.psi κ.natural)
      (ir.evalWith rd d κ.operand) i

/-- **A row fitting the shape is its expression parts plus its kernel parts** below `n`. -/
theorem evalWith_row_split {rd : ir.Valuation I} {d : ℕ} {p : ℕ} {sh : ProductShape} {row : Expr}
    (hrow : ir.rowOkB p sh row = true) (h1 : (I (ir.domainField d)).decode 1 = 1) {i : ℕ}
    (hi : i < sh.n) :
    ir.evalWith rd d row i = ((ir.rowExprs row).map fun t => ir.evalWith rd d t i).sum +
      ((ir.rowKernels row).map fun κ => kernelVal rd d sh.n κ i).sum := by
  rw [evalWith_summands rd d row i]
  refine list_sum_split (M := (I (ir.domainField d)).K) row.summands ir.kernelPart?
    (fun t => ir.evalWith rd d t i) (fun κ => kernelVal rd d sh.n κ i) fun t ht κ hκ => ?_
  have hκm : κ ∈ ir.rowKernels row := List.mem_filterMap.2 ⟨t, ht, hκ⟩
  have hok := List.all_eq_true.1 (Bool.and_eq_true_iff.1 hrow).2 κ hκm
  simp only [kernelOkB, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨hsz, -⟩, -⟩, -⟩, -⟩ := hok
  exact evalWith_kernelPart hκ hsz h1 hi

/-- **The transform of a row's difference** of a spectral product form, row `r` of a shape
fitting its rows (`rowOkB`) at a valid root: the transform of
`P_r − N_r − (m qlo + m Q_r)` at frequency `k` is the difference of the two sides of the row's
equation in the spectrum (`SpectralRowHolds`). -/
theorem nttOf_rowDiff {rd : ir.Valuation I} {d m : ℕ} {real : ModRealization} {p : ℕ}
    {sh : ProductShape} {r : ℕ} {PR NR : Expr} (hP : ir.rowOkB p sh PR = true)
    (hN : ir.rowOkB p sh NR = true) (h1 : (I (ir.domainField d)).decode 1 = 1)
    (hr : RootFacts (I (ir.domainField d)).K sh.n ((I (ir.domainField d)).decode sh.psi))
    {k : ℕ} (hk : k < sh.n) :
    Ops.nttOf sh.natural sh.n ((I (ir.domainField d)).decode sh.psi)
        (fun i => ir.evalWith rd d PR i - ir.evalWith rd d NR i - ir.quotTerm rd d m real (r * sh.n + i))
        k =
      Ops.nttOf sh.natural sh.n ((I (ir.domainField d)).decode sh.psi)
          (fun i => ((ir.rowExprs PR).map fun t => ir.evalWith rd d t i).sum -
            ((ir.rowExprs NR).map fun t => ir.evalWith rd d t i).sum -
              ir.quotTerm rd d m real (r * sh.n + i)) k -
        (((ir.rowKernels NR).map fun κ =>
            ir.kernelTerm rd d sh.natural sh.n ((I (ir.domainField d)).decode sh.psi) κ k).sum -
          ((ir.rowKernels PR).map fun κ =>
            ir.kernelTerm rd d sh.natural sh.n ((I (ir.domainField d)).decode sh.psi) κ k).sum) := by
  set ψ := (I (ir.domainField d)).decode sh.psi
  have hsplit : ∀ i < sh.n, ir.evalWith rd d PR i - ir.evalWith rd d NR i -
      ir.quotTerm rd d m real (r * sh.n + i) =
      (((ir.rowExprs PR).map fun t => ir.evalWith rd d t i).sum -
        ((ir.rowExprs NR).map fun t => ir.evalWith rd d t i).sum -
          ir.quotTerm rd d m real (r * sh.n + i)) +
        ((ir.rowKernels PR).map fun κ => kernelVal rd d sh.n κ i).sum -
          ((ir.rowKernels NR).map fun κ => kernelVal rd d sh.n κ i).sum := by
    intro i hi
    rw [evalWith_row_split hP h1 hi, evalWith_row_split hN h1 hi]
    ring
  rw [Ops.nttOf_congr hsplit, Ops.nttOf_sub, Ops.nttOf_add, Ops.nttOf_listSum, Ops.nttOf_listSum]
  have hK : ∀ {row : Expr}, ir.rowOkB p sh row = true →
      ((ir.rowKernels row).map fun κ => Ops.nttOf sh.natural sh.n ψ (kernelVal rd d sh.n κ) k).sum =
        ((ir.rowKernels row).map fun κ => ir.kernelTerm rd d sh.natural sh.n ψ κ k).sum := by
    intro row hrow
    refine congrArg List.sum (List.map_congr_left fun κ hκm => ?_)
    obtain ⟨t, ht, hκ⟩ := List.mem_filterMap.1 hκm
    have hok := List.all_eq_true.1 (Bool.and_eq_true_iff.1 hrow).2 κ hκm
    simp only [kernelOkB, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨⟨hsz, hpsi⟩, hnat⟩, -⟩, -⟩ := hok
    rw [← nttOf_kernelPart hκ h1 hsz hpsi hnat hr hk]
    refine Ops.nttOf_congr (fun i hi => ?_) k
    exact (evalWith_kernelPart hκ hsz h1 hi).symm
  rw [hK hP, hK hN]
  ring

/-- **The coefficients of a spectral product form from its placed equation**: under the
structural check (`productOkB`) at a valid root, the equation in the spectrum row by row gives
`P − N = m qlo + m Q` in the field at every coordinate. -/
theorem coeff_of_spectral {rd : ir.Valuation I} {d m : ℕ} {P N : Expr} {real : ModRealization}
    {sh : ProductShape} (hsh : ir.productShape? P N = some sh)
    (hP : sh.rowsP.all (ir.rowOkB (ir.charOf (ir.domainField d)) sh) = true)
    (hN : sh.rowsN.all (ir.rowOkB (ir.charOf (ir.domainField d)) sh) = true)
    (hlen : sh.rowsP.length = sh.rowsN.length) (hlP : ir.exprLen P = sh.rowsP.length * sh.n)
    (h1 : (I (ir.domainField d)).decode 1 = 1)
    (hr : RootFacts (I (ir.domainField d)).K sh.n ((I (ir.domainField d)).decode sh.psi))
    (hrows : ∀ r < sh.rowsP.length, ∀ k < sh.n,
      ir.SpectralRowHolds rd d m real sh r (sh.rowsP.getD r default) (sh.rowsN.getD r default) k) :
    ∀ i < ir.exprLen P, ir.evalWith rd d P i - ir.evalWith rd d N i = ir.quotTerm rd d m real i := by
  have hsP : sh.rowsP = ir.rowsAt sh.n P := by
    unfold productShape? at hsh
    obtain ⟨κ, -, rfl⟩ := Option.map_eq_some_iff.1 hsh
    rfl
  have hsN : sh.rowsN = ir.rowsAt sh.n N := by
    unfold productShape? at hsh
    obtain ⟨κ, -, rfl⟩ := Option.map_eq_some_iff.1 hsh
    rfl
  have hn0 : 0 < sh.n := by
    rcases Nat.eq_zero_or_pos sh.n with h0 | h0
    · exact absurd (by rw [h0, Nat.cast_zero]) hr.ne
    · exact h0
  have hrowLen : ∀ {rows : List Expr}, rows.all (ir.rowOkB (ir.charOf (ir.domainField d)) sh) = true →
      ∀ row ∈ rows, ir.exprLen row = sh.n := fun hall row hrow => by
    have := List.all_eq_true.1 hall row hrow
    simp only [rowOkB, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1
  intro i hi
  have hr' : i / sh.n < sh.rowsP.length := by
    rw [hlP] at hi
    exact Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hi)
  have hk : i % sh.n < sh.n := Nat.mod_lt _ hn0
  have hi' : i = i / sh.n * sh.n + i % sh.n := by rw [Nat.mul_comm]; exact (Nat.div_add_mod i sh.n).symm
  obtain ⟨r, hrdef⟩ : ∃ r, r = i / sh.n := ⟨_, rfl⟩
  obtain ⟨k, hkdef⟩ : ∃ k, k = i % sh.n := ⟨_, rfl⟩
  rw [← hrdef] at hr' hi'
  rw [← hkdef] at hk hi'
  have hrN : r < sh.rowsN.length := hlen ▸ hr'
  have hPR : ir.evalWith rd d P i = ir.evalWith rd d (sh.rowsP.getD r default) k := by
    rw [hi', hsP]
    exact evalWith_rowsAt rd d (hsP ▸ hrowLen hP) (hsP ▸ hr') hk
  have hNR : ir.evalWith rd d N i = ir.evalWith rd d (sh.rowsN.getD r default) k := by
    rw [hi', hsN]
    exact evalWith_rowsAt rd d (hsN ▸ hrowLen hN) (hsN ▸ hrN) hk
  have hPok : ir.rowOkB (ir.charOf (ir.domainField d)) sh (sh.rowsP.getD r default) = true := by
    rw [List.getD_eq_getElem _ _ hr']
    exact List.all_eq_true.1 hP _ (List.getElem_mem hr')
  have hNok : ir.rowOkB (ir.charOf (ir.domainField d)) sh (sh.rowsN.getD r default) = true := by
    rw [List.getD_eq_getElem _ _ hrN]
    exact List.all_eq_true.1 hN _ (List.getElem_mem hrN)
  have hzero := eq_zero_of_nttOf hr sh.natural (x := fun i' =>
      ir.evalWith rd d (sh.rowsP.getD r default) i' - ir.evalWith rd d (sh.rowsN.getD r default) i' -
        ir.quotTerm rd d m real (r * sh.n + i'))
    (fun k' hk' => by
      rw [nttOf_rowDiff hPok hNok h1 hr hk', hrows r hr' k' hk', sub_self]) hk
  have hz : ir.evalWith rd d (sh.rowsP.getD r default) k - ir.evalWith rd d (sh.rowsN.getD r default) k -
      ir.quotTerm rd d m real (r * sh.n + k) = 0 := hzero
  have hq : ir.quotTerm rd d m real i = ir.quotTerm rd d m real (r * sh.n + k) := by rw [← hi']
  rw [hPR, hNR, hq]
  linear_combination hz

/-- **The placed equation of a spectral product form from its coefficients** (the honest
prover's direction): under the structural check at a valid root, `P − N = m qlo + m Q` in the
field gives every row's equation in the spectrum. -/
theorem spectral_of_coeff {rd : ir.Valuation I} {d m : ℕ} {P N : Expr} {real : ModRealization}
    {sh : ProductShape} (hsh : ir.productShape? P N = some sh)
    (hP : sh.rowsP.all (ir.rowOkB (ir.charOf (ir.domainField d)) sh) = true)
    (hN : sh.rowsN.all (ir.rowOkB (ir.charOf (ir.domainField d)) sh) = true)
    (hlen : sh.rowsP.length = sh.rowsN.length) (hlP : ir.exprLen P = sh.rowsP.length * sh.n)
    (h1 : (I (ir.domainField d)).decode 1 = 1)
    (hr : RootFacts (I (ir.domainField d)).K sh.n ((I (ir.domainField d)).decode sh.psi))
    (hc : ∀ i < ir.exprLen P,
      ir.evalWith rd d P i - ir.evalWith rd d N i = ir.quotTerm rd d m real i) :
    ∀ r < sh.rowsP.length, ∀ k < sh.n,
      ir.SpectralRowHolds rd d m real sh r (sh.rowsP.getD r default) (sh.rowsN.getD r default) k := by
  have hsP : sh.rowsP = ir.rowsAt sh.n P := by
    unfold productShape? at hsh
    obtain ⟨κ, -, rfl⟩ := Option.map_eq_some_iff.1 hsh
    rfl
  have hsN : sh.rowsN = ir.rowsAt sh.n N := by
    unfold productShape? at hsh
    obtain ⟨κ, -, rfl⟩ := Option.map_eq_some_iff.1 hsh
    rfl
  have hrowLen : ∀ {rows : List Expr}, rows.all (ir.rowOkB (ir.charOf (ir.domainField d)) sh) = true →
      ∀ row ∈ rows, ir.exprLen row = sh.n := fun hall row hrow => by
    have := List.all_eq_true.1 hall row hrow
    simp only [rowOkB, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1
  intro r hr' k hk
  have hrN : r < sh.rowsN.length := hlen ▸ hr'
  have hPok : ir.rowOkB (ir.charOf (ir.domainField d)) sh (sh.rowsP.getD r default) = true := by
    rw [List.getD_eq_getElem _ _ hr']
    exact List.all_eq_true.1 hP _ (List.getElem_mem hr')
  have hNok : ir.rowOkB (ir.charOf (ir.domainField d)) sh (sh.rowsN.getD r default) = true := by
    rw [List.getD_eq_getElem _ _ hrN]
    exact List.all_eq_true.1 hN _ (List.getElem_mem hrN)
  have hrow0 : ∀ i < sh.n, ir.evalWith rd d (sh.rowsP.getD r default) i -
      ir.evalWith rd d (sh.rowsN.getD r default) i - ir.quotTerm rd d m real (r * sh.n + i) = 0 := by
    intro i hi
    have hPR : ir.evalWith rd d P (r * sh.n + i) = ir.evalWith rd d (sh.rowsP.getD r default) i := by
      rw [hsP]
      exact evalWith_rowsAt rd d (hsP ▸ hrowLen hP) (hsP ▸ hr') hi
    have hNR : ir.evalWith rd d N (r * sh.n + i) = ir.evalWith rd d (sh.rowsN.getD r default) i := by
      rw [hsN]
      exact evalWith_rowsAt rd d (hsN ▸ hrowLen hN) (hsN ▸ hrN) hi
    have hlt : r * sh.n + i < ir.exprLen P := by
      rw [hlP]
      nlinarith
    rw [← hPR, ← hNR, hc _ hlt, sub_self]
  have h := nttOf_rowDiff (rd := rd) (m := m) (real := real) (r := r) hPok hNok h1 hr hk
  rw [Ops.nttOf_congr hrow0, Ops.nttOf_zero] at h
  unfold SpectralRowHolds
  linear_combination -h

end Spectral

/-! ## Soundness -/

section Sound

variable {ir : RealizedProgram} {I : Interp} {primeNodes : ℕ → List String}

/-- **The facts of a side's interval**: every coordinate's integer reading lies in `J` and casts
to its value. -/
def SideFacts (rd : ir.Valuation I) (d : ℕ) (e : Expr) (J : Ivl) (L : ℕ) : Prop :=
  ∀ i < L, ir.evalIntWith rd d e i ∈ J ∧
    ((ir.evalIntWith rd d e i : ℤ) : (I (ir.domainField d)).K) = ir.evalWith rd d e i

/-- **`wholeIvl` is sound**: its interval fact gives the side's facts. -/
theorem wholeIvl_sound {rd : ir.Valuation I} {fs : List Fact} (hfs : ∀ f ∈ fs, f.HoldsWith ir rd)
    {d : ℕ} {e : Expr} {ks rest : List ℕ} {J : Ivl} (h : wholeIvl fs d e ks = some (J, rest)) :
    SideFacts rd d e J (ir.exprLen e) ∧ rest = ks.tail := by
  unfold wholeIvl at h
  split at h
  · rename_i k ks'
    split at h
    · rename_i d' x lo hi hk
      split_ifs at h with hc
      cases h
      obtain ⟨rfl, hx⟩ := hc
      obtain rfl := Expr.eq_of_beq hx
      have hH : Fact.HoldsWith ir rd (.ivl d' x lo hi) := hfs _ (List.mem_of_getElem? hk)
      exact ⟨fun i hi => ⟨⟨(hH i hi).1, (hH i hi).2.1⟩, (hH i hi).2.2⟩, rfl⟩
    · cases h
  · cases h

/-- **The integer reading of a constant multiple's natural**: `centred(c)` casts to `decode c`. -/
theorem cast_centered_eq_decode {f : ℕ} (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
    (hf : f < ir.fields.length) {c : ℕ} (hc : c < ir.charOf f) :
    (((I f).centered c : ℤ) : (I f).K) = (I f).decode c := by
  have hchar := charP_field hI hf
  rw [FieldInterp.centered_eq, hI.characteristic f hf, centeredZ_cast,
    hL.decode_natCast f hf c hc]

/-- **A kernel part's operator on the integers** at output `b n + i` of a kernel of `K` blocks of
`n`, its block's coefficients `z` small integers casting to the polynomial in its form:
`Σ_j C_j(i) x_j`, `C` the negacyclic coefficients of `z`, `x` the operand's integer readings. -/
theorem evalIntWith_apply_kernel (hI : I.Registered ir) {rd : ir.Valuation I} {d : ℕ}
    (hd : ir.domainField d < ir.fields.length) {κ : KernelPart}
    (hk : κ.op.kernel? = some (κ.value, κ.blocks, κ.psi, κ.natural)) {n : ℕ}
    (hsz : (ir.value κ.value).size = κ.blocks * n) (hb : κ.block < κ.blocks)
    (h2 : 2 < ir.charOf (ir.domainField d)) (htn : ∀ k < ir.charOf (ir.domainField d),
      (I (ir.domainField d)).toNat (k : (I (ir.domainField d)).K) = k)
    {z : ℕ → ℤ}
    (hz : ∀ s < n, 2 * |z s| < ir.charOf (ir.domainField d) ∧
      ir.kernelPoly rd d κ.value κ.block n κ.psi κ.natural s = (z s : (I (ir.domainField d)).K))
    {i : ℕ} (hi : i < n) :
    ir.evalIntWith rd d (.apply κ.op κ.operand) (κ.block * n + i) =
      ∑ j ∈ Finset.range n, Ops.negCoef n z i j * ir.evalIntWith rd d κ.operand j := by
  have hchar := charP_field hI hd
  have hp := hI.characteristic _ hd
  obtain ⟨hr, hc, hblk⟩ := NamedOp.kernel?_spec ir hk hsz (by omega)
  have hlt : κ.block * n + i < κ.blocks * n := by nlinarith
  rw [evalIntWith_apply]
  unfold NamedOp.applyInt
  rw [Fin.sum_univ_eq_sum_range (fun t => (I (ir.domainField d)).coefInt
      (NamedOp.block ir (ir.domainField d) rd κ.op (fun s => if s = t then 1 else 0)
        ((κ.block * n + i) % NamedOp.rows ir κ.op)) *
      ir.evalIntWith rd d κ.operand
        ((κ.block * n + i) / NamedOp.rows ir κ.op * NamedOp.cols ir κ.op + t))]
  rw [hc, hr, Nat.mod_eq_of_lt hlt, Nat.div_eq_of_lt hlt]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.1 hj
  rw [hblk _ rd _ hb hi, Ops.negacyclic_eq_sum_negCoef _ _ _ hi, sum_mul_unit _ _ hj',
    Nat.zero_mul, Nat.zero_add]
  have hpoly : NamedOp.formPoly (ir.domainField d) n (fun s => castElt (rd κ.value (κ.block * n + s)))
      (formOf κ.natural κ.psi) = ir.kernelPoly rd d κ.value κ.block n κ.psi κ.natural := by
    funext s
    rfl
  rw [hpoly, FieldInterp.coefInt_negCoef hp hchar htn
    (by have := h2; unfold charOf at this; omega) _ hz]

/-- **A kernel part on the integers**, its kernel block's coefficients `z` small integers casting
to the polynomial: below the block length `n`, its integer reading is
`centred(s) · Σ_j C_j(i) x_j`, `C` the negacyclic coefficients of `z`, `x` the operand's
integer readings. -/
theorem evalIntWith_kernelPart (hI : I.Registered ir) {rd : ir.Valuation I} {d : ℕ}
    (hd : ir.domainField d < ir.fields.length) {t : Expr} {κ : KernelPart}
    (ht : ir.kernelPart? t = some κ) {n : ℕ} (hsz : (ir.value κ.value).size = κ.blocks * n)
    (h2 : 2 < ir.charOf (ir.domainField d)) (htn : ∀ k < ir.charOf (ir.domainField d),
      (I (ir.domainField d)).toNat (k : (I (ir.domainField d)).K) = k)
    {z : ℕ → ℤ}
    (hz : ∀ s < n, 2 * |z s| < ir.charOf (ir.domainField d) ∧
      ir.kernelPoly rd d κ.value κ.block n κ.psi κ.natural s = (z s : (I (ir.domainField d)).K))
    {i : ℕ} (hi : i < n) :
    ir.evalIntWith rd d t i = (I (ir.domainField d)).centered κ.scale *
      ∑ j ∈ Finset.range n, Ops.negCoef n z i j * ir.evalIntWith rd d κ.operand j := by
  have hp := hI.characteristic _ hd
  have hcore : ∀ {c : ℕ} {e : Expr}, ir.kernelCore? c e = some κ →
      ir.evalIntWith rd d e i =
        ∑ j ∈ Finset.range n, Ops.negCoef n z i j * ir.evalIntWith rd d κ.operand j := by
    intro c e he
    obtain ⟨-, hk, hb, -⟩ := kernelCore?_spec he
    have hn : (ir.value κ.value).size / κ.blocks = n := by
      rw [hsz, Nat.mul_div_cancel_left n (by omega)]
    rw [kernelCore?_read (ir.evalIntWith rd d) (fun _ _ _ => rfl) he (hn ▸ hi), hn]
    exact evalIntWith_apply_kernel hI hd hk hsz hb h2 htn hz hi
  unfold kernelPart? at ht
  split at ht
  · rename_i c e
    have hc := (kernelCore?_spec ht).1
    rw [evalIntWith_scale_const, ← hc, hcore ht]
  · have hc := (kernelCore?_spec ht).1
    rw [hc, hcore ht, FieldInterp.centered_eq, hp]
    unfold centeredZ
    rw [if_pos (by omega)]
    push_cast
    ring

/-- **An interval of `x` bounds every expression reading within `x`** (`readsWithinB`). -/
theorem ivl_of_readsWithinB {rd : ir.Valuation I} {d : ℕ} {x y : Expr} {lo hi : ℤ}
    (h : ir.readsWithinB x y = true) (hx : Fact.HoldsWith ir rd (.ivl d x lo hi)) :
    Fact.HoldsWith ir rd (.ivl d y lo hi) := by
  unfold readsWithinB at h
  rcases Bool.or_eq_true_iff.1 h with h | h
  · rw [Expr.eq_of_beq h]
    exact hx
  · split at h
    · rename_i idx z
      simp only [Bool.and_eq_true] at h
      obtain ⟨hz, hr⟩ := h
      obtain rfl := Expr.eq_of_beq hz
      intro i hi
      rw [exprLen_reindex] at hi
      have := hx _ (IndexMap.entry_lt_of_inRange hr hi)
      simpa only [evalIntWith_reindex, evalWith, evalE_reindex] using this
    · cases h

/-- **`kernelIvl` is sound**: a kernel part fitting the shape, its kernel fact and operand
interval holding, has its integer readings in the interval, casting to its values. -/
theorem kernelIvl_sound (hwf : ir.WellFormed) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
    {rd : ir.Valuation I} {fs : List Fact} (hfs : ∀ f ∈ fs, f.HoldsWith ir rd) {d : ℕ}
    (hd : d < ir.domains.length) (h2 : 2 < ir.charOf (ir.domainField d)) {sh : ProductShape}
    {t : Expr} {κ : KernelPart} (ht : ir.kernelPart? t = some κ)
    (hok : ir.kernelOkB (ir.charOf (ir.domainField d)) sh κ = true) {k k' : ℕ} {J : Ivl}
    (hJ : ir.kernelIvl fs d (ir.charOf (ir.domainField d)) sh κ k k' = some J) :
    SideFacts rd d t J sh.n := by
  have hdF := domainField_lt hwf hd
  have hp := hI.characteristic _ hdF
  have htn := hL.toNat_natCast _ hdF
  have hdec := hL.decode_natCast _ hdF
  simp only [kernelOkB, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨hsz, hpsi⟩, hnat⟩, hlen⟩, hsc⟩ := hok
  unfold kernelIvl at hJ
  split at hJ
  · rename_i d1 v b n psi o hl hh d2 x xl xh hk hk'
    split_ifs at hJ with hc
    cases hJ
    obtain ⟨hd1, hd2, rfl, rfl, rfl, rfl, rfl, hx, hl2, hh2⟩ := hc
    rw [← abs_eq_max_neg] at hl2 hh2
    subst d1 d2
    have hK : Fact.HoldsWith ir rd (.kernel d κ.value κ.block sh.n sh.psi sh.natural hl hh) :=
      hfs _ (List.mem_of_getElem? hk)
    have hX : Fact.HoldsWith ir rd (.ivl d κ.operand xl xh) :=
      ivl_of_readsWithinB hx (hfs _ (List.mem_of_getElem? hk'))
    rw [← hpsi, ← hnat] at hK
    -- the kernel block's coefficients as integers
    have hz : ∀ s < sh.n, 2 * |(I (ir.domainField d)).coefInt
        (ir.kernelPoly rd d κ.value κ.block sh.n κ.psi κ.natural s)| <
          ir.charOf (ir.domainField d) ∧
        ir.kernelPoly rd d κ.value κ.block sh.n κ.psi κ.natural s =
          ((I (ir.domainField d)).coefInt
            (ir.kernelPoly rd d κ.value κ.block sh.n κ.psi κ.natural s) : ℤ) := by
      intro s hs
      obtain ⟨h1, h2', h3⟩ := hK s hs
      refine ⟨?_, h3.symm⟩
      have hb : |(I (ir.domainField d)).coefInt
          (ir.kernelPoly rd d κ.value κ.block sh.n κ.psi κ.natural s)| ≤ max |hl| |hh| := by
        rw [abs_le]
        constructor
        · have := neg_abs_le hl
          have := le_max_left |hl| |hh|
          linarith
        · have := le_abs_self hh
          have := le_max_right |hl| |hh|
          linarith
      rcases le_total |hl| |hh| with hm | hm
      · rw [max_eq_right hm] at hb
        linarith
      · rw [max_eq_left hm] at hb
        linarith
    intro i hi
    have hint := evalIntWith_kernelPart hI hdF ht hsz h2 htn hz hi
    have hxm : ∀ j < sh.n, ir.evalIntWith rd d κ.operand j ∈ (⟨xl, xh⟩ : Ivl) :=
      fun j hj => ⟨(hX j (by omega)).1, (hX j (by omega)).2.1⟩
    have hhm : ∀ s < sh.n, (I (ir.domainField d)).coefInt
        (ir.kernelPoly rd d κ.value κ.block sh.n κ.psi κ.natural s) ∈ (⟨hl, hh⟩ : Ivl) :=
      fun s hs => ⟨(hK s hs).1, (hK s hs).2.1⟩
    have hneg' := negIvl_mem hhm hxm hi
    refine ⟨?_, ?_⟩
    · rw [hint, FieldInterp.centered_eq, hp]
      exact Ivl.smul_mem _ hneg'
    · rw [hint, evalWith_kernelPart ht hsz
        (by rw [hdec 1 (by have := h2; unfold charOf at this; omega), Nat.cast_one]) hi]
      push_cast
      rw [cast_centered_eq_decode hI hL hdF hsc, Ops.negacyclic_eq_sum_negCoef _ _ _ hi]
      congr 1
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' := Finset.mem_range.1 hj
      rw [(hX j (by omega)).2.2]
      congr 1
      have hm := Ops.negCoef_map (Int.castAddHom (I (ir.domainField d)).K)
        sh.n (fun s => (I (ir.domainField d)).coefInt
          (ir.kernelPoly rd d κ.value κ.block sh.n κ.psi κ.natural s)) i j
      simp only [Int.coe_castAddHom] at hm
      rw [hm]
      unfold Ops.negCoef
      congr 1 <;> refine Finset.sum_congr rfl fun s hs => ?_ <;> split_ifs <;>
        simp only [← (hz s (Finset.mem_range.1 hs)).2]
  · cases hJ

/-- **`rowIvl` at a kernel part** reads two premises. -/
theorem rowIvl_cons_some {fs : List Fact} {d p : ℕ} {sh : ProductShape} {t : Expr}
    {ts : List Expr} {ks rest : List ℕ} {J : Ivl} {κ : KernelPart} (hκ : ir.kernelPart? t = some κ)
    (h : ir.rowIvl fs d p sh (t :: ts) ks = some (J, rest)) :
    ∃ k k' ks' J₁ J₂, ks = k :: k' :: ks' ∧ ir.kernelIvl fs d p sh κ k k' = some J₁ ∧
      ir.rowIvl fs d p sh ts ks' = some (J₂, rest) ∧ J = J₁.add J₂ := by
  unfold rowIvl at h
  rw [hκ] at h
  match ks, h with
  | k :: k' :: ks', h =>
    simp only at h
    obtain ⟨J₁, hJ₁, hr⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨⟨J₂, r₂⟩, hr₂, hrr⟩ := Option.map_eq_some_iff.1 hr
    simp only [Prod.mk.injEq] at hrr
    obtain ⟨rfl, rfl⟩ := hrr
    exact ⟨k, k', ks', J₁, J₂, rfl, hJ₁, hr₂, rfl⟩
  | [], h => simp at h
  | [_], h => simp at h

/-- **`rowIvl` at an expression part** reads one `ivl` premise. -/
theorem rowIvl_cons_none {fs : List Fact} {d p : ℕ} {sh : ProductShape} {t : Expr}
    {ts : List Expr} {ks rest : List ℕ} {J : Ivl} (hκ : ir.kernelPart? t = none)
    (h : ir.rowIvl fs d p sh (t :: ts) ks = some (J, rest)) :
    ∃ k ks' lo hi J₂, ks = k :: ks' ∧ fs[k]? = some (.ivl d t lo hi) ∧ sh.n ≤ ir.exprLen t ∧
      ir.rowIvl fs d p sh ts ks' = some (J₂, rest) ∧ J = (⟨lo, hi⟩ : Ivl).add J₂ := by
  unfold rowIvl at h
  rw [hκ] at h
  match ks, h with
  | k :: ks', h =>
    simp only at h
    split at h
    next d' x lo hi hk =>
      split_ifs at h with hc
      obtain ⟨⟨J₂, r₂⟩, hr₂, hrr⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at hrr
      obtain ⟨rfl, rfl⟩ := hrr
      obtain ⟨rfl, hx, hlen⟩ := hc
      obtain rfl := Expr.eq_of_beq hx
      exact ⟨k, ks', lo, hi, J₂, rfl, hk, hlen, hr₂, rfl⟩
    next => cases h
  | [], h => simp at h

/-- **`rowIvl` is sound**: the summands' integer readings' sum lies in the interval and casts to
their values' sum, below the block length. -/
theorem rowIvl_sound (hwf : ir.WellFormed) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
    {rd : ir.Valuation I} {fs : List Fact} (hfs : ∀ f ∈ fs, f.HoldsWith ir rd) {d : ℕ}
    (hd : d < ir.domains.length) (h2 : 2 < ir.charOf (ir.domainField d)) {sh : ProductShape} :
    ∀ {ts : List Expr} {ks rest : List ℕ} {J : Ivl},
      (∀ t ∈ ts, ∀ κ, ir.kernelPart? t = some κ →
        ir.kernelOkB (ir.charOf (ir.domainField d)) sh κ = true) →
      ir.rowIvl fs d (ir.charOf (ir.domainField d)) sh ts ks = some (J, rest) →
      ∀ i < sh.n, (ts.map fun t => ir.evalIntWith rd d t i).sum ∈ J ∧
        (((ts.map fun t => ir.evalIntWith rd d t i).sum : ℤ) : (I (ir.domainField d)).K) =
          (ts.map fun t => ir.evalWith rd d t i).sum
  | [], ks, rest, J, _, h, i, _ => by
    simp only [rowIvl, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [Ivl.mem_def]
  | t :: ts, ks, rest, J, hok, h, i, hi => by
    have hok' : ∀ t' ∈ ts, ∀ κ', ir.kernelPart? t' = some κ' →
        ir.kernelOkB (ir.charOf (ir.domainField d)) sh κ' = true :=
      fun t' ht' κ' hκ' => hok t' (List.mem_cons_of_mem _ ht') κ' hκ'
    cases hκt : ir.kernelPart? t with
    | some κ =>
      obtain ⟨k, k', ks', J₁, J₂, -, hJ₁, hr₂, rfl⟩ := rowIvl_cons_some hκt h
      have hk := kernelIvl_sound hwf hI hL hfs hd h2 hκt (hok t List.mem_cons_self κ hκt) hJ₁ i hi
      have ht := rowIvl_sound hwf hI hL hfs hd h2 hok' hr₂ i hi
      simp only [List.map_cons, List.sum_cons]
      exact ⟨Ivl.add_mem hk.1 ht.1, by rw [Int.cast_add, hk.2, ht.2]⟩
    | none =>
      obtain ⟨k, ks', lo, hi', J₂, -, hk, hlen, hr₂, rfl⟩ := rowIvl_cons_none hκt h
      have hH : Fact.HoldsWith ir rd (.ivl d t lo hi') := hfs _ (List.mem_of_getElem? hk)
      have ht := rowIvl_sound hwf hI hL hfs hd h2 hok' hr₂ i hi
      obtain ⟨h1, h2', h3⟩ := hH i (by omega)
      simp only [List.map_cons, List.sum_cons]
      exact ⟨Ivl.add_mem ⟨h1, h2'⟩ ht.1, by rw [Int.cast_add, h3, ht.2]⟩

/-- **`rowsIvl` is sound**: every row's integer readings lie in the interval and cast to its
values, below the block length. -/
theorem rowsIvl_sound (hwf : ir.WellFormed) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
    {rd : ir.Valuation I} {fs : List Fact} (hfs : ∀ f ∈ fs, f.HoldsWith ir rd) {d : ℕ}
    (hd : d < ir.domains.length) (h2 : 2 < ir.charOf (ir.domainField d)) {sh : ProductShape} :
    ∀ {rows : List Expr} {ks rest : List ℕ} {J : Ivl},
      (∀ r ∈ rows, ir.rowOkB (ir.charOf (ir.domainField d)) sh r = true) →
      ir.rowsIvl fs d (ir.charOf (ir.domainField d)) sh rows ks = some (J, rest) →
      ∀ r ∈ rows, SideFacts rd d r J sh.n
  | [], _, _, _, _, h => by simp [rowsIvl] at h
  | [r], ks, rest, J, hok, h => by
    intro r' hr'
    simp only [List.mem_singleton] at hr'
    subst hr'
    simp only [rowsIvl] at h
    have hk : ∀ t ∈ r'.summands, ∀ κ, ir.kernelPart? t = some κ →
        ir.kernelOkB (ir.charOf (ir.domainField d)) sh κ = true := fun t ht κ hκ =>
      List.all_eq_true.1 (Bool.and_eq_true_iff.1 (hok r' (by simp))).2 κ
        (List.mem_filterMap.2 ⟨t, ht, hκ⟩)
    intro i hi
    have := rowIvl_sound hwf hI hL hfs hd h2 hk h i hi
    rw [evalIntWith_summands, evalWith_summands]
    exact this
  | r :: r' :: rs, ks, rest, J, hok, h => by
    simp only [rowsIvl] at h
    obtain ⟨⟨J₁, rest₁⟩, hJ₁, hr⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨⟨J₂, rest₂⟩, hr₂, hrr⟩ := Option.map_eq_some_iff.1 hr
    simp only [Prod.mk.injEq] at hrr
    obtain ⟨rfl, rfl⟩ := hrr
    have ih := rowsIvl_sound hwf hI hL hfs hd h2
      (fun x hx => hok x (List.mem_cons_of_mem _ hx)) hr₂
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · have hk : ∀ t ∈ x.summands, ∀ κ, ir.kernelPart? t = some κ →
          ir.kernelOkB (ir.charOf (ir.domainField d)) sh κ = true := fun t ht κ hκ =>
        List.all_eq_true.1 (Bool.and_eq_true_iff.1 (hok x List.mem_cons_self)).2 κ
          (List.mem_filterMap.2 ⟨t, ht, hκ⟩)
      intro i hi
      have := rowIvl_sound hwf hI hL hfs hd h2 hk hJ₁ i hi
      rw [evalIntWith_summands, evalWith_summands]
      exact ⟨Ivl.hull_mem_left this.1, this.2⟩
    · intro i hi
      have := ih x hx i hi
      exact ⟨Ivl.hull_mem_right this.1, this.2⟩

/-- **`sideIvl` is sound**: a side's integer readings lie in its interval and cast to its values,
the side's rows those of the shape (`rowsAt`), fitting it, `n` coordinates each. -/
theorem sideIvl_sound (hwf : ir.WellFormed) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
    {rd : ir.Valuation I} {fs : List Fact} (hfs : ∀ f ∈ fs, f.HoldsWith ir rd) {d : ℕ}
    (hd : d < ir.domains.length) (h2 : 2 < ir.charOf (ir.domainField d))
    {sh : Option ProductShape} {e : Expr} {rows : List Expr} {ks rest : List ℕ} {J : Ivl}
    (hrows : ∀ sh', sh = some sh' → rows = ir.rowsAt sh'.n e ∧
      (∀ r ∈ rows, ir.rowOkB (ir.charOf (ir.domainField d)) sh' r = true) ∧
      ir.exprLen e = rows.length * sh'.n)
    (h : ir.sideIvl fs d (ir.charOf (ir.domainField d)) sh e rows ks = some (J, rest)) :
    SideFacts rd d e J (ir.exprLen e) := by
  unfold sideIvl at h
  split at h
  · rename_i sh'
    split_ifs at h
    · exact (wholeIvl_sound hfs h).1
    · obtain ⟨hr, hok, hlen⟩ := hrows sh' rfl
      have hrl : ∀ r ∈ ir.rowsAt sh'.n e, ir.exprLen r = sh'.n := fun r hr' => by
        have := hok r (hr ▸ hr')
        simp only [rowOkB, Bool.and_eq_true, decide_eq_true_eq] at this
        exact this.1
      have hR := rowsIvl_sound hwf hI hL hfs hd h2 hok h
      intro i hi
      have hn0 : 0 < sh'.n := by
        rcases Nat.eq_zero_or_pos sh'.n with h0 | h0
        · rw [hlen, h0, Nat.mul_zero] at hi
          omega
        · exact h0
      have hr' : i / sh'.n < rows.length := by
        rw [hlen] at hi
        exact Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hi)
      have hk : i % sh'.n < sh'.n := Nat.mod_lt _ hn0
      have hi' : i = i / sh'.n * sh'.n + i % sh'.n := by
        rw [Nat.mul_comm]
        exact (Nat.div_add_mod i sh'.n).symm
      have hrr : i / sh'.n < (ir.rowsAt sh'.n e).length := hr ▸ hr'
      have hmem : (ir.rowsAt sh'.n e).getD (i / sh'.n) default ∈ rows := by
        have : (ir.rowsAt sh'.n e).getD (i / sh'.n) default ∈ ir.rowsAt sh'.n e := by
          rw [List.getD_eq_getElem _ _ hrr]
          exact List.getElem_mem hrr
        rw [hr]
        exact this
      rw [hi', evalIntWith_rowsAt rd d hrl hrr hk, evalWith_rowsAt rd d hrl hrr hk]
      exact hR _ hmem _ hk
  · exact (wholeIvl_sound hfs h).1

/-- **The integer argument of `productMod`** (the C++ comment's): with the sides' readings in
their intervals, the quotient below `NQ` and `D − m qlo − m Q` a multiple of `p`, the side
conditions (`productSideB`) give `D = m (qlo + Q)` over the integers and `Q ≤ qmax`. -/
theorem productMod_int {p m : ℕ} {qlo : ℤ} {qmax NQ : ℕ} {JP JN : Ivl}
    (hside : productSideB p m qlo qmax NQ JP JN = true) (hm : 2 ≤ m) {P N Q : ℤ} (hP : P ∈ JP)
    (hN : N ∈ JN) (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ (NQ : ℤ) - 1)
    (hdvd : (p : ℤ) ∣ P - N - m * qlo - m * Q) : P - N = m * (qlo + Q) ∧ Q ≤ qmax := by
  simp only [productSideB, Bool.and_eq_true, decide_eq_true_eq] at hside
  obtain ⟨⟨hl, hr⟩, hq⟩ := hside
  set d0 := JP.lo - JN.lo - m * qlo with hd0
  have hab : max d0 0 - max (-d0) 0 = d0 := by
    rcases le_total 0 d0 with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]
      ring
    · rw [max_eq_right h, max_eq_left (by linarith)]
      ring
  have hA0 : 0 ≤ P - JP.lo + max d0 0 := by
    have := hP.1
    have := le_max_right d0 0
    linarith
  have hA1 : P - JP.lo + max d0 0 < p := by
    have := hP.2
    linarith
  have hm0 : (0 : ℤ) ≤ m := by positivity
  have hB0 : 0 ≤ N - JN.lo + m * Q + max (-d0) 0 := by
    have := hN.1
    have := le_max_right (-d0) 0
    have : 0 ≤ (m : ℤ) * Q := mul_nonneg hm0 hQ0
    linarith
  have hB1 : N - JN.lo + m * Q + max (-d0) 0 < p := by
    have := hN.2
    have : (m : ℤ) * Q ≤ m * ((NQ : ℤ) - 1) := mul_le_mul_of_nonneg_left hQ1 hm0
    linarith
  have hAB : (P - JP.lo + max d0 0) - (N - JN.lo + m * Q + max (-d0) 0) =
      P - N - m * qlo - m * Q := by
    have : max d0 0 - max (-d0) 0 = JP.lo - JN.lo - m * qlo := by rw [hab]
    linarith
  have heq : P - JP.lo + max d0 0 = N - JN.lo + m * Q + max (-d0) 0 := by
    have hd : (p : ℤ) ∣ (P - JP.lo + max d0 0) - (N - JN.lo + m * Q + max (-d0) 0) := by
      rw [hAB]
      exact hdvd
    have habs : |(P - JP.lo + max d0 0) - (N - JN.lo + m * Q + max (-d0) 0)| < p := by
      rw [abs_lt]
      constructor <;> linarith
    have := Int.eq_zero_of_abs_lt_dvd hd habs
    linarith
  have hD : P - N = m * (qlo + Q) := by linarith
  refine ⟨hD, ?_⟩
  have hle : (m : ℤ) * (qlo + Q) ≤ JP.hi - JN.lo := by
    rw [← hD]
    linarith [hP.2, hN.1]
  have hdiv : qlo + Q ≤ (JP.hi - JN.lo) / m := by
    rw [Int.le_ediv_iff_mul_le (by omega)]
    linarith
  linarith

/-- **The rows of a product form's shape** are its sides' rows (`rowsAt`). -/
theorem productShape?_rows {P N : Expr} {sh : ProductShape} (h : ir.productShape? P N = some sh) :
    sh.rowsP = ir.rowsAt sh.n P ∧ sh.rowsN = ir.rowsAt sh.n N := by
  unfold productShape? at h
  obtain ⟨κ, -, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨rfl, rfl⟩

/-- **The structural check's lengths**: a domain of the program, and `P`, `N` and the quotient of
one length. -/
theorem productOkB_lens {d m : ℕ} {P N : Expr} {real : ModRealization}
    (h : ir.productOkB (.mod d m P N real) = true) :
    d < ir.domains.length ∧ ir.exprLen N = ir.exprLen P ∧
      ∀ Q, real.quotient = some Q → ir.exprLen Q = ir.exprLen P := by
  simp only [productOkB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hd, hN⟩, hQ⟩, -⟩ := h
  refine ⟨hd, hN, fun Q hq => ?_⟩
  rw [hq] at hQ
  simpa using hQ

/-- **The structural check's quotient**: a product form passing it has a quotient. -/
theorem productOkB_quotient {d m : ℕ} {P N : Expr} {real : ModRealization}
    (h : ir.productOkB (.mod d m P N real) = true) : ∃ Q, real.quotient = some Q := by
  simp only [productOkB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨-, -⟩, hQ⟩, -⟩ := h
  cases hq : real.quotient with
  | none => rw [hq] at hQ; cases hQ
  | some Q => exact ⟨Q, rfl⟩

/-- **The structural check of a spectral product form**: its shape, the transform's root valid,
as many rows of `P` as of `N` covering both sides, every row fitting the shape. -/
theorem productOkB_spectral {d m : ℕ} {P N : Expr} {real : ModRealization}
    (h : ir.productOkB (.mod d m P N real) = true) (hf : real.form = .spectralProduct) :
    ∃ sh, ir.productShape? P N = some sh ∧
      rootOkB (ir.charOf (ir.domainField d)) sh.n sh.psi = true ∧
      sh.rowsP.length = sh.rowsN.length ∧ ir.exprLen P = sh.rowsP.length * sh.n ∧
      ir.exprLen N = sh.rowsN.length * sh.n ∧
      sh.rowsP.all (ir.rowOkB (ir.charOf (ir.domainField d)) sh) = true ∧
      sh.rowsN.all (ir.rowOkB (ir.charOf (ir.domainField d)) sh) = true := by
  simp only [productOkB, Bool.and_eq_true, hf] at h
  obtain ⟨-, h⟩ := h
  split at h
  · rename_i sh hsh
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨hr, hl⟩, hP⟩, hN⟩, hRP⟩, hRN⟩ := h
    exact ⟨sh, hsh, hr, hl, hP, hN, hRP, hRN⟩
  · cases h

/-- **The root facts from a valid root** (`rootOkB_facts`) in domain `d`'s field. -/
theorem rootFacts_of_rootOkB (hwf : ir.WellFormed) (hI : I.Registered ir)
    (hL : I.Lawful ir primeNodes) {d n psi : ℕ} (hd : d < ir.domains.length)
    (h : rootOkB (ir.charOf (ir.domainField d)) n psi = true) :
    RootFacts (I (ir.domainField d)).K n ((I (ir.domainField d)).decode psi) := by
  have hdF := domainField_lt hwf hd
  have hchar := charP_field hI hdF
  obtain ⟨hprim, hn0, hk, -, hneg, -⟩ :=
    rootOkB_facts (K := (I (ir.domainField d)).K) (p := ir.charOf (ir.domainField d))
      (dec := (I (ir.domainField d)).decode) (hL.decode_natCast _ hdF) h
  exact ⟨hprim, hn0, hk, hneg⟩

/-- **The field equation of a product form from its placed equation** (`ProductPlaced`), under the
structural check (`productOkB`): `P − N = m qlo + m Q` in the field at every coordinate (in the
spectral form by `coeff_of_spectral`). -/
theorem coeff_of_productPlaced (hwf : ir.WellFormed) (hI : I.Registered ir)
    (hL : I.Lawful ir primeNodes) {rd : ir.Valuation I} {d m : ℕ} {P N : Expr}
    {real : ModRealization} (hok : ir.productOkB (.mod d m P N real) = true)
    (hform : real.form.isProduct = true) (h2 : 2 < ir.charOf (ir.domainField d))
    (hpl : ir.ProductPlaced rd d m P N real) :
    ∀ i < ir.exprLen P, ir.evalWith rd d P i - ir.evalWith rd d N i = ir.quotTerm rd d m real i := by
  obtain ⟨hd, -, -⟩ := productOkB_lens hok
  have hdF := domainField_lt hwf hd
  have h1 : (I (ir.domainField d)).decode 1 = 1 := by
    rw [hL.decode_natCast _ hdF 1 (by have := h2; unfold charOf at this; omega), Nat.cast_one]
  cases hf : real.form with
  | product =>
    unfold ProductPlaced at hpl
    rw [hf] at hpl
    exact hpl
  | spectralProduct =>
    obtain ⟨sh, hsh, hr, hl, hP, -, hRP, hRN⟩ := productOkB_spectral hok hf
    unfold ProductPlaced at hpl
    rw [hf, hsh] at hpl
    exact coeff_of_spectral hsh hRP hRN hl hP h1 (rootFacts_of_rootOkB hwf hI hL hd hr) hpl.2
  | _ => rw [hf] at hform; cases hform

/-- **The placed equation of a product form from its field equation** (the honest prover's
direction of `coeff_of_productPlaced`, by `spectral_of_coeff`). -/
theorem productPlaced_of_coeff (hwf : ir.WellFormed) (hI : I.Registered ir)
    (hL : I.Lawful ir primeNodes) {rd : ir.Valuation I} {d m : ℕ} {P N : Expr}
    {real : ModRealization} (hok : ir.productOkB (.mod d m P N real) = true)
    (h2 : 2 < ir.charOf (ir.domainField d))
    (hc : ∀ i < ir.exprLen P,
      ir.evalWith rd d P i - ir.evalWith rd d N i = ir.quotTerm rd d m real i) :
    ir.ProductPlaced rd d m P N real := by
  obtain ⟨hd, -, -⟩ := productOkB_lens hok
  have hdF := domainField_lt hwf hd
  have h1 : (I (ir.domainField d)).decode 1 = 1 := by
    rw [hL.decode_natCast _ hdF 1 (by have := h2; unfold charOf at this; omega), Nat.cast_one]
  unfold ProductPlaced
  cases hf : real.form with
  | product => exact hc
  | spectralProduct =>
    obtain ⟨sh, hsh, hr, hl, hP, -, hRP, hRN⟩ := productOkB_spectral hok hf
    simp only [hsh]
    exact ⟨hl, spectral_of_coeff hsh hRP hRN hl hP h1 (rootFacts_of_rootOkB hwf hI hL hd hr) hc⟩
  | _ => trivial

/-- **`productModFact_sound`**: the rule is sound: under the realized program, its premises
holding, the predicate holds (`HoldsWith`): `m | P − N`, and the quotient's equation
`P − N = m (qlo + Q)` with `0 ≤ Q ≤ qmax` and faithful integer readings (`ProductQuotWith`). -/
theorem productModFact_sound (hwf : ir.WellFormed) (hI : I.Registered ir)
    (hL : I.Lawful ir primeNodes) {sr : List (ℕ × ℕ)} {e : ir.Env I} (h : ir.RealizedAt e)
    (hS : ∀ vN ∈ sr, ∀ i < (ir.value vN.1).size,
      ∃ n < vN.2, ir.reader e vN.1 i = ((n : ℕ) : (I (ir.valueField vN.1)).K))
    {fs : List Fact} (hfs : ∀ f ∈ fs, f.Holds e) {pid : ℕ} {body : PredBody}
    (hown : ir.OwnBody pid body) {ks : List ℕ} {f : Fact}
    (hf : ir.productModFact fs pid body ks = some f) : f.Holds e := by
  unfold productModFact at hf
  split at hf
  case h_2 => cases hf
  rename_i d m P N real
  rcases hown with ⟨hpid, hb⟩ | ⟨d', hd'⟩
  swap
  · cases hd'
  by_cases hc : real.form.isProduct = true ∧ ir.productOkB (.mod d m P N real) = true ∧ 2 < m ∧
      m < ir.charOf (ir.domainField d) ∧ 2 < ir.charOf (ir.domainField d)
  swap
  · rw [if_neg hc] at hf
    cases hf
  rw [if_pos hc] at hf
  obtain ⟨hform, hok, hm2, hmp, h2⟩ := hc
  obtain ⟨hd, hlN, hlQ⟩ := productOkB_lens hok
  have hdF := domainField_lt hwf hd
  have hchar := charP_field hI hdF
  generalize hq : real.quotient = qo at hf
  rcases qo with _ | Q₀
  · simp at hf
  rcases ks with _ | ⟨k0, rest⟩
  · cases Q₀ <;> simp at hf
  cases Q₀ <;> try (simp at hf; done)
  rename_i v
  simp only at hf
  generalize hk0 : fs[k0]? = fk at hf
  rcases fk with _ | fk
  · simp at hf
  cases fk <;> try (simp at hf; done)
  rename_i d0 Q NQ
  simp only at hf
  by_cases hc2 : d0 = d ∧ Q.beq (.leaf v) = true ∧ 0 < NQ ∧
      natReadB (ir.value v).kind NQ (ir.charOf (ir.domainField d)) = true ∧
      NQ ≤ ir.charOf (ir.domainField d) ∧ ir.valueField v = ir.domainField d ∧
      v < ir.values.length
  swap
  · rw [if_neg hc2] at hf
    cases hf
  rw [if_pos hc2] at hf
  obtain ⟨rfl, hQ, hNQ, hnat, hNQp, hvf, hv⟩ := hc2
  obtain rfl := Expr.eq_of_beq hQ
  generalize hsh : (if real.form = .spectralProduct then ir.productShape? P N else none) = sh
    at hf
  generalize hJP : ir.sideIvl fs d0 (ir.charOf (ir.domainField d0)) sh P
    ((sh.map (·.rowsP)).getD []) rest = oP at hf
  rcases oP with _ | ⟨JP, rest'⟩
  · simp at hf
  simp only at hf
  generalize hJN : ir.sideIvl fs d0 (ir.charOf (ir.domainField d0)) sh N
    ((sh.map (·.rowsN)).getD []) rest' = oN at hf
  rcases oN with _ | ⟨JN, _ | ⟨r0, rs0⟩⟩
  · simp at hf
  swap
  · simp at hf
  simp only at hf
  by_cases hside : productSideB (ir.charOf (ir.domainField d0)) m real.quotientLo real.qmax NQ JP JN
      = true
  swap
  · rw [if_neg hside] at hf
    cases hf
  rw [if_pos hside] at hf
  cases hf
  -- the facts at the reader
  have hfs' : ∀ f ∈ fs, f.HoldsWith ir (ir.reader e) := hfs
  have hrowsOf : ∀ (side : Expr) (rows : List Expr),
      (side = P ∧ rows = (sh.map (·.rowsP)).getD []) ∨
        (side = N ∧ rows = (sh.map (·.rowsN)).getD []) →
      ∀ sh', sh = some sh' → rows = ir.rowsAt sh'.n side ∧
        (∀ r ∈ rows, ir.rowOkB (ir.charOf (ir.domainField d0)) sh' r = true) ∧
        ir.exprLen side = rows.length * sh'.n := by
    intro side rows hside' sh' hsh'
    subst hsh'
    have hsf : real.form = .spectralProduct := by
      by_contra hne
      rw [if_neg hne] at hsh
      cases hsh
    rw [if_pos hsf] at hsh
    obtain ⟨sh'', hsh'', -, -, hlP, hlN', hRP, hRN⟩ := productOkB_spectral hok hsf
    rw [hsh''] at hsh
    cases hsh
    obtain ⟨hrP, hrN⟩ := productShape?_rows hsh''
    rcases hside' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [Option.map_some, Option.getD_some]
      exact ⟨hrP, fun r hr => List.all_eq_true.1 hRP r hr, hlP⟩
    · simp only [Option.map_some, Option.getD_some]
      exact ⟨hrN, fun r hr => List.all_eq_true.1 hRN r hr, hlN'⟩
  have hPf := sideIvl_sound hwf hI hL hfs' hd h2 (hrowsOf P _ (.inl ⟨rfl, rfl⟩)) hJP
  have hNf := sideIvl_sound hwf hI hL hfs' hd h2 (hrowsOf N _ (.inr ⟨rfl, rfl⟩)) hJN
  -- the quotient's interval
  have hQf : Fact.Holds e (.ivl d0 (.leaf v) 0 ((NQ : ℤ) - 1)) := by
    refine srcFact_sound (primeNodes := primeNodes) hwf hI hL h hS hfs (d := d0) (v := v)
      (s := .nat k0) (by simp [srcGuard, hv, hd, hvf, h2]) ?_
    simp only [srcFact, hk0, true_and, Expr.beq_iff, hnat, hNQ, hNQp, and_self, ↓reduceIte]
  -- the field equation
  have hpl := h.product _ (predicate_mem hpid) d0 m P N real hb hform hm2
  have hFE := coeff_of_productPlaced hwf hI hL hok hform h2 hpl
  have hmain : ∀ i < ir.exprLen P,
      ir.evalIntWith (ir.reader e) d0 P i - ir.evalIntWith (ir.reader e) d0 N i =
        m * (real.quotientLo + ir.evalIntWith (ir.reader e) d0 (.leaf v) i) ∧
      ir.evalIntWith (ir.reader e) d0 (.leaf v) i ≤ real.qmax := by
    intro i hi
    have hiN : i < ir.exprLen N := hlN ▸ hi
    have hiQ : i < ir.exprLen (.leaf v) := (hlQ _ hq) ▸ hi
    obtain ⟨hPm, hPc⟩ := hPf i hi
    obtain ⟨hNm, hNc⟩ := hNf i hiN
    obtain ⟨hQ0, hQ1, hQc⟩ := hQf i hiQ
    have hfe := hFE i hi
    unfold quotTerm at hfe
    rw [hq] at hfe
    simp only at hfe
    have hdvd : ((ir.charOf (ir.domainField d0) : ℕ) : ℤ) ∣
        ir.evalIntWith (ir.reader e) d0 P i - ir.evalIntWith (ir.reader e) d0 N i -
          m * real.quotientLo - m * ir.evalIntWith (ir.reader e) d0 (.leaf v) i := by
      rw [← CharP.intCast_eq_zero_iff (I (ir.domainField d0)).K]
      push_cast
      rw [hPc, hNc, hQc]
      change ir.evalWith (ir.reader e) d0 P i - ir.evalWith (ir.reader e) d0 N i - _ - _ = 0
      rw [hfe]
      push_cast
      ring
    exact productMod_int hside (by omega) hPm hNm hQ0 hQ1 hdvd
  show ir.HoldsWith (ir.reader e) (ir.predicate pid).body
  rw [hb]
  refine ⟨fun i hi => ⟨_, (hmain i hi).1⟩, ?_⟩
  unfold ProductQuotWith
  rw [hq]
  intro _ _ i hi
  have hiN : i < ir.exprLen N := hlN ▸ hi
  have hiQ : i < ir.exprLen (.leaf v) := (hlQ _ hq) ▸ hi
  exact ⟨(hmain i hi).1, (hQf i hiQ).1, (hmain i hi).2, (hPf i hi).2, (hNf i hiN).2,
    (hQf i hiQ).2.2⟩

end Sound

end GordieHowe.RealizedProgram
