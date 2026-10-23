-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Library.Eval
public import GordieHowe.Language.RealizedProgram.Interval

@[expose] public section

/-!
# GordieHowe: convolutions realized through a transform

The batch form of compiler/conv.h realizes `B` acyclic convolutions `conv(a, b)` of operand rows
of lengths `la` and `lb` by a committed value `z = NTT_M(a) · NTT_M(b)` (the operands zero-extended
to `M`, the predicate `SpectralConv.products`, a part of the domain's spectral batch) and reads each
convolution as the first `la + lb − 1` coordinates of `INTT_M(z)` (`SpectralConv.read`). This file
proves the reading sound:

* **the transform computes the product** (`Ops.inverseNtt_mul_nttScheme`): at a primitive
  `2M`-th root `ψ`, `M = 2^k` invertible, `INTT_M(NTT_M(u) · NTT_M(v))` is the negacyclic product
  of `u` and `v` (`DFT.negSpectrum_negacyclicConvCoeff`, `DFT.negacyclicConvCoeff_eq_untwist`),
  which for operands of lengths `la`, `lb` with `la + lb − 1 ≤ M` is their acyclic convolution;
* **the reading is the source** (`convRead_eq_source`): where the products predicate holds, the
  shared expression `read` equals the shared expression `source` below their common length, the
  index maps' entries read off once (`IndexMap.entry_convLeft`, `IndexMap.entry_convRight`,
  `IndexMap.entry_zeroExtend`, `IndexMap.entry_blockPrefix`);
* **a realized field equation holds** (`fieldEq_of_realized`): where every field `equal` with no
  realization target holds, the field equation `e = e'` of a predicate with the target
  `realized q` (`RealizedAdmits`) holds, as `q`'s sides are `e` and `e'` with convolutions read
  through their realizations (`Expr.eval_matchB`: an expression's value below its length depends
  only on its shared expressions' values below theirs).
-/

namespace GordieHowe.RealizedProgram

open Export

/-! ## Index maps -/

namespace IndexMap

/-- **The size of blocks of runs of one size** is their number times that size. -/
theorem size_flatMap_blocks (f : ℕ → IndexMap) (c : ℕ) :
    ∀ B, (∀ b < B, size (f b) = c) → size ((List.range B).flatMap f) = B * c
  | 0, _ => by simp [size]
  | B + 1, hf => by
    rw [List.range_succ, List.flatMap_append, size_append,
      size_flatMap_blocks f c B fun b hb => hf b (by omega)]
    simp [hf B (by omega), Nat.succ_mul]

/-- **Division and remainder of a block position**: `(q c + r) / c = q` and `(q c + r) % c = r`
for `r < c`. -/
theorem block_div_mod {q r c : ℕ} (hr : r < c) : (q * c + r) / c = q ∧ (q * c + r) % c = r := by
  have hc : 0 < c := by omega
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hc, Nat.div_eq_of_lt hr, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]

/-- **A block position lies below the blocks**: `q c + r < B c` for `q < B` and `r < c`. -/
theorem block_lt {q r c B : ℕ} (hq : q < B) (hr : r < c) : q * c + r < B * c := by
  have := Nat.mul_le_mul_right c (Nat.succ_le_of_lt hq)
  rw [Nat.succ_mul] at this
  omega

/-- **Entry `i` of blocks of runs of one size `c`**: entry `i mod c` of block `i / c`. -/
theorem entry_flatMap_blocks (f : ℕ → IndexMap) (c : ℕ) :
    ∀ B, (∀ b < B, size (f b) = c) → ∀ i, i < B * c →
      entry ((List.range B).flatMap f) i = entry (f (i / c)) (i % c)
  | 0, _, i, h => by simp at h
  | B + 1, hf, i, h => by
    rw [List.range_succ, List.flatMap_append, entry_append,
      size_flatMap_blocks f c B fun b hb => hf b (by omega)]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    by_cases hi : i < B * c
    · rw [if_pos hi, entry_flatMap_blocks f c B (fun b hb => hf b (by omega)) i hi]
    · rw [if_neg hi]
      have hlt : i - B * c < c := by rw [Nat.succ_mul] at h; omega
      obtain ⟨hdiv, hmod⟩ := block_div_mod (q := B) hlt
      rw [show B * c + (i - B * c) = i by omega] at hdiv hmod
      rw [hdiv, hmod]

/-- **Entry `t` of three runs** `(s₁, 0, c₁)`, `(s₂, d, c₂)`, `(s₃, 0, c₃)`: `s₁` below `c₁`, the
middle run's entry `t − c₁` below `c₁ + c₂`, `s₃` after. -/
theorem entry_three {s₁ s₂ s₃ c₁ c₂ c₃ : ℕ} {d : ℤ} {t : ℕ} (ht : t < c₁ + c₂ + c₃) :
    entry [(s₁, 0, c₁), (s₂, d, c₂), (s₃, 0, c₃)] t =
      if t < c₁ then s₁ else if t < c₁ + c₂ then ((s₂ : ℤ) + d * (t - c₁ : ℕ)).toNat else s₃ := by
  simp only [entry]
  by_cases h₁ : t < c₁
  · simp [h₁]
  · by_cases h₂ : t - c₁ < c₂
    · simp [h₁, h₂, show t < c₁ + c₂ by omega]
    · have h₃ : t - c₁ - c₂ < c₃ := by omega
      simp [h₁, h₂, h₃, show ¬ t < c₁ + c₂ by omega]

/-- The size of three runs. -/
theorem size_three (s₁ s₂ s₃ c₁ c₂ c₃ : ℕ) (d : ℤ) :
    size [(s₁, 0, c₁), (s₂, d, c₂), (s₃, 0, c₃)] = c₁ + c₂ + c₃ := by
  simp [size]
  omega

/-- The size of one block's runs of the left operand's view: `la`. -/
theorem size_convLeftRuns {B la lb k blk : ℕ} (hla : 0 < la) (hk : k < la + lb - 1) :
    size [(B * la, 0, k + 1 - lb), (blk * la + (k + 1 - lb), 1, min k (la - 1) + 1 - (k + 1 - lb)),
      (B * la, 0, la - 1 - min k (la - 1))] = la := by
  rw [size_three]
  omega

/-- The size of one block's runs of the right operand's view: `la`. -/
theorem size_convRightRuns {B la lb k blk : ℕ} (hla : 0 < la) (hk : k < la + lb - 1) :
    size [(B * lb, 0, k + 1 - lb), (blk * lb + (k - (k + 1 - lb)), -1,
      min k (la - 1) + 1 - (k + 1 - lb)), (B * lb, 0, la - 1 - min k (la - 1))] = la := by
  rw [size_three]
  omega

/-- **The left operand's view has `B (la + lb − 1) la` entries.** -/
theorem size_convLeft {B la lb : ℕ} (hla : 0 < la) :
    size (convLeft B la lb) = B * ((la + lb - 1) * la) := by
  unfold convLeft
  exact size_flatMap_blocks _ _ B fun blk _ =>
    size_flatMap_blocks _ _ _ fun k hk => size_convLeftRuns hla hk

/-- **The right operand's view has `B (la + lb − 1) la` entries.** -/
theorem size_convRight {B la lb : ℕ} (hla : 0 < la) :
    size (convRight B la lb) = B * ((la + lb - 1) * la) := by
  unfold convRight
  exact size_flatMap_blocks _ _ B fun blk _ =>
    size_flatMap_blocks _ _ _ fun k hk => size_convRightRuns hla hk

/-- **Entry `(blk, k, t)` of the left operand's view**: `blk la + t` when `k + 1 − lb ≤ t ≤ k`,
else `B la`. -/
theorem entry_convLeft {B la lb blk k t : ℕ} (hla : 0 < la) (hblk : blk < B)
    (hk : k < la + lb - 1) (ht : t < la) :
    entry (convLeft B la lb) ((blk * (la + lb - 1) + k) * la + t) =
      if k + 1 - lb ≤ t ∧ t ≤ k then blk * la + t else B * la := by
  have hin : k * la + t < (la + lb - 1) * la := block_lt hk ht
  have hpos : (blk * (la + lb - 1) + k) * la + t = blk * ((la + lb - 1) * la) + (k * la + t) := by
    ring
  have hrun := size_convLeftRuns (B := B) (blk := blk) hla hk
  rw [size_three] at hrun
  unfold convLeft
  rw [entry_flatMap_blocks _ _ B (fun b _ => size_flatMap_blocks _ _ _ fun k hk =>
    size_convLeftRuns hla hk) _ (by rw [hpos]; exact block_lt hblk hin), hpos,
    (block_div_mod hin).1, (block_div_mod hin).2,
    entry_flatMap_blocks _ _ _ (fun k hk => size_convLeftRuns hla hk) _ (block_lt hk ht),
    (block_div_mod ht).1, (block_div_mod ht).2, entry_three (by omega)]
  by_cases h₁ : t < k + 1 - lb
  · rw [if_pos h₁, if_neg (by omega)]
  · rw [if_neg h₁]
    by_cases h₂ : t < k + 1 - lb + (min k (la - 1) + 1 - (k + 1 - lb))
    · rw [if_pos h₂, if_pos (by omega)]
      have : ((blk * la + (k + 1 - lb) : ℕ) : ℤ) + 1 * ((t - (k + 1 - lb) : ℕ) : ℤ) =
          ((blk * la + t : ℕ) : ℤ) := by
        push_cast
        omega
      rw [this, Int.toNat_natCast]
    · rw [if_neg h₂, if_neg (by omega)]

/-- **Entry `(blk, k, t)` of the right operand's view**: `blk lb + (k − t)` when
`k + 1 − lb ≤ t ≤ k`, else `B lb`. -/
theorem entry_convRight {B la lb blk k t : ℕ} (hla : 0 < la) (hblk : blk < B)
    (hk : k < la + lb - 1) (ht : t < la) :
    entry (convRight B la lb) ((blk * (la + lb - 1) + k) * la + t) =
      if k + 1 - lb ≤ t ∧ t ≤ k then blk * lb + (k - t) else B * lb := by
  have hin : k * la + t < (la + lb - 1) * la := block_lt hk ht
  have hpos : (blk * (la + lb - 1) + k) * la + t = blk * ((la + lb - 1) * la) + (k * la + t) := by
    ring
  have hrun := size_convRightRuns (B := B) (blk := blk) hla hk
  rw [size_three] at hrun
  unfold convRight
  rw [entry_flatMap_blocks _ _ B (fun b _ => size_flatMap_blocks _ _ _ fun k hk =>
    size_convRightRuns hla hk) _ (by rw [hpos]; exact block_lt hblk hin), hpos,
    (block_div_mod hin).1, (block_div_mod hin).2,
    entry_flatMap_blocks _ _ _ (fun k hk => size_convRightRuns hla hk) _ (block_lt hk ht),
    (block_div_mod ht).1, (block_div_mod ht).2, entry_three (by omega)]
  by_cases h₁ : t < k + 1 - lb
  · rw [if_pos h₁, if_neg (by omega)]
  · rw [if_neg h₁]
    by_cases h₂ : t < k + 1 - lb + (min k (la - 1) + 1 - (k + 1 - lb))
    · rw [if_pos h₂, if_pos (by omega)]
      have : ((blk * lb + (k - (k + 1 - lb)) : ℕ) : ℤ) + -1 * ((t - (k + 1 - lb) : ℕ) : ℤ) =
          ((blk * lb + (k - t) : ℕ) : ℤ) := by
        push_cast
        omega
      rw [this, Int.toNat_natCast]
    · rw [if_neg h₂, if_neg (by omega)]

/-- **The zero extension has `B M` entries**, for `l ≤ M`. -/
theorem size_zeroExtend {B l M : ℕ} (hl : l ≤ M) : size (zeroExtend B l M) = B * M := by
  unfold zeroExtend
  exact size_flatMap_blocks _ _ B fun _ _ => by simp [size]; omega

/-- **Entry `(blk, t)` of the zero extension**: `blk l + t` for `t < l`, else `B l`. -/
theorem entry_zeroExtend {B l M blk t : ℕ} (hl : l ≤ M) (hblk : blk < B) (ht : t < M) :
    entry (zeroExtend B l M) (blk * M + t) = if t < l then blk * l + t else B * l := by
  unfold zeroExtend
  rw [entry_flatMap_blocks _ _ B (fun _ _ => by simp [size]; omega) _ (block_lt hblk ht),
    (block_div_mod ht).1, (block_div_mod ht).2]
  simp only [entry]
  by_cases h : t < l
  · simp [h]
    omega
  · have : t - l < M - l := by omega
    simp only [h, this, if_false, ↓reduceIte, Int.mul_zero, add_zero]
    simp only [zero_mul, add_zero, Int.toNat_natCast]

/-- **The block prefixes have `B n` entries.** -/
theorem size_blockPrefix (B M n : ℕ) : size (blockPrefix B M n) = B * n := by
  unfold blockPrefix
  exact size_flatMap_blocks _ _ B fun _ _ => by simp [size]

/-- **Entry `(blk, k)` of the block prefixes**: `blk M + k`. -/
theorem entry_blockPrefix {B M n blk k : ℕ} (hblk : blk < B) (hk : k < n) :
    entry (blockPrefix B M n) (blk * n + k) = blk * M + k := by
  unfold blockPrefix
  rw [entry_flatMap_blocks _ _ B (fun _ _ => by simp [size]) _ (block_lt hblk hk),
    (block_div_mod hk).1, (block_div_mod hk).2, entry_step_one hk]

end IndexMap

/-! ## The transform computes the product -/

namespace Ops

variable {K : Type*} [Field K]

/-- The first `n` coordinates of the negacyclic convolution are the vendored convolution of the
first `n` coordinates. -/
theorem toFin_negacyclic (n : ℕ) (h x : ℕ → K) :
    toFin n (negacyclic n h x) = LatticeCrypto.negacyclicConvCoeff (toFin n h) (toFin n x) := by
  funext i
  simp [negacyclic, toFin, ofFin_of_lt _ i.isLt]

/-- **The scheme-order transform of a negacyclic product is the pointwise product of the
transforms**, for `n = 2^k` and `ψ^n = −1` (`DFT.negSpectrum_negacyclicConvCoeff`). -/
theorem nttScheme_negacyclic {k n : ℕ} (hn : n = 2 ^ k) {ψ : K} (hψ : ψ ^ n = -1) (x y : ℕ → K)
    {m : ℕ} (hm : m < n) :
    nttScheme n ψ (negacyclic n x y) m = nttScheme n ψ x m * nttScheme n ψ y m := by
  subst hn
  have h1 := nttScheme_eq_negSpectrum ψ (negacyclic (2 ^ k) x y) ⟨m, hm⟩
  have h2 := nttScheme_eq_negSpectrum ψ x ⟨m, hm⟩
  have h3 := nttScheme_eq_negSpectrum ψ y ⟨m, hm⟩
  simp only at h1 h2 h3
  rw [h1, h2, h3, toFin_negacyclic, DFT.negSpectrum_negacyclicConvCoeff hψ]
  rfl

/-- **The inverse transform of the transforms' product is the negacyclic product**, at a
primitive `2n`-th root `ψ`, `n = 2^k` invertible. -/
theorem inverseNtt_mul_nttScheme {k n : ℕ} (hn : n = 2 ^ k) {ψ : K}
    (hψ : IsPrimitiveRoot ψ (2 * n)) (hn0 : (n : K) ≠ 0) (x y : ℕ → K) {i : ℕ} (hi : i < n) :
    inverseNtt n ψ (fun m => nttScheme n ψ x m * nttScheme n ψ y m) i = negacyclic n x y i := by
  have hn' : n ≠ 0 := fun h => hn0 (by simp [h])
  have hneg := DFT.IsPrimitiveRoot.pow_half_eq_neg_one hψ hn'
  rw [inverseNtt_congr (y := nttScheme n ψ (negacyclic n x y))
      (fun m hm => (nttScheme_negacyclic hn hneg x y hm).symm),
    inverseNtt_nttScheme hn hψ hn0 _ hi]

/-- **A negacyclic product of short operands is their acyclic convolution**: for `x` zero from
`la` on, `y` zero from `lb` on and `la + lb − 1 ≤ n`, coordinate `j < n` is
`Σ_{t < la, t ≤ j, j − t < lb} x_t y_{j−t}` (no product wraps around). -/
theorem negacyclic_eq_conv {n la lb : ℕ} (x y : ℕ → K) (hx : ∀ t, la ≤ t → x t = 0)
    (hy : ∀ t, lb ≤ t → y t = 0) (hla : 0 < la) (hlb : 0 < lb) (hfit : la + lb - 1 ≤ n) {j : ℕ}
    (hj : j < n) :
    negacyclic n x y j = ∑ t : Fin la, if (t : ℕ) ≤ j ∧ j - t < lb then x t * y (j - t) else 0 := by
  rw [negacyclic_apply n x y hj]
  have hwrap : (∑ i : Fin n, ∑ k : Fin n, if (i : ℕ) + k = j + n then x i * y k else 0) = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun k _ => ?_
    split_ifs with h
    · by_cases hi : la ≤ (i : ℕ)
      · rw [hx i hi, zero_mul]
      · by_cases hk : lb ≤ (k : ℕ)
        · rw [hy k hk, mul_zero]
        · omega
    · rfl
  have hinner : ∀ i : Fin n, (∑ k : Fin n, if (i : ℕ) + k = j then x i * y k else 0) =
      if (i : ℕ) ≤ j then x i * y (j - i) else 0 := by
    intro i
    split_ifs with hij
    · rw [Finset.sum_eq_single ⟨j - i, by omega⟩]
      · simp [show (i : ℕ) + (j - i) = j by omega]
      · intro k _ hk
        rw [if_neg]
        intro h
        apply hk
        ext
        simp only
        omega
      · intro h
        exact absurd (Finset.mem_univ _) h
    · exact Finset.sum_eq_zero fun k _ => by rw [if_neg]; omega
  rw [hwrap, sub_zero, Finset.sum_congr rfl fun i _ => hinner i]
  have hlan : la ≤ n := by omega
  rw [Fin.sum_univ_eq_sum_range (fun i => if i ≤ j then x i * y (j - i) else 0) n,
    Fin.sum_univ_eq_sum_range (fun t => if t ≤ j ∧ j - t < lb then x t * y (j - t) else 0) la,
    ← Finset.sum_range_add_sum_Ico _ hlan]
  have hrest : (∑ i ∈ Finset.Ico la n, if i ≤ j then x i * y (j - i) else 0) = 0 :=
    Finset.sum_eq_zero fun i hi => by
      rw [Finset.mem_Ico] at hi
      rw [hx i hi.1, zero_mul, ite_self]
  rw [hrest, add_zero]
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases htj : t ≤ j
  · by_cases hl : j - t < lb
    · rw [if_pos htj, if_pos ⟨htj, hl⟩]
    · rw [if_pos htj, if_neg (fun h => hl h.2), hy _ (by omega), mul_zero]
  · rw [if_neg htj, if_neg (fun h => htj h.1)]

/-- **A root with `ψ^(2^k) = −1` is a primitive `2·2^k`-th root of unity**, in a field where
`2 ≠ 0`. -/
theorem isPrimitiveRoot_of_pow_eq_neg_one {ψ : K} {k : ℕ} (h : ψ ^ (2 ^ k) = -1)
    (h2 : (2 : K) ≠ 0) : IsPrimitiveRoot ψ (2 * 2 ^ k) := by
  have hne : ¬ ψ ^ (2 ^ k) = 1 := by
    rw [h]
    intro h'
    apply h2
    linear_combination -h'
  have hone : ψ ^ (2 ^ (k + 1)) = 1 := by
    rw [pow_succ, pow_mul, h]
    norm_num
  have hord : orderOf ψ = 2 ^ (k + 1) := orderOf_eq_prime_pow hne hone
  rw [show 2 * 2 ^ k = 2 ^ (k + 1) by ring, ← hord]
  exact IsPrimitiveRoot.orderOf ψ

end Ops

/-! ## The forms of a realization -/

theorem Expr.eq_of_convSource? {e : Expr} {s : ConvSource} (h : e.convSource? = some s) :
    e = .apply (.sum s.la) (.mul (.reindex s.mA (.concat s.a (.leaf s.zA)))
      (.reindex s.mB (.concat s.b (.leaf s.zB)))) := by
  revert h
  unfold Expr.convSource?
  split
  · intro h
    cases h
    rfl
  · intro h
    cases h

theorem Expr.eq_of_convRead? {e : Expr} {r : ConvRead} (h : e.convRead? = some r) :
    e = .reindex r.g (.apply (.batched r.B (.inverseNtt r.M r.psi)) (.leaf r.z)) := by
  revert h
  unfold Expr.convRead?
  split
  · intro h
    cases h
    rfl
  · intro h
    cases h

theorem Expr.eq_of_convProducts? {e : Expr} {q : ConvProducts} (h : e.convProducts? = some q) :
    e = .mul (.apply (.batched q.B (.ntt q.M q.psi .scheme)) (.reindex q.pA (.concat q.a (.leaf q.zA))))
      (.apply (.batched q.B' (.ntt q.M' q.psi' .scheme))
        (.reindex q.pB (.concat q.b (.leaf q.zB)))) := by
  revert h
  unfold Expr.convProducts?
  split
  · intro h
    cases h
    rfl
  · intro h
    cases h

section

variable {ir : RealizedProgram} {I : Interp}

/-- **A batched operator's coordinate `j`** below `B rows`: the operator on block `j / rows` at
`j mod rows`. -/
theorem evalE_apply_batched (rd : ir.Valuation I) (f B : ℕ) (op : NamedOp) (e : Expr) {j : ℕ}
    (hj : j < B * NamedOp.rows ir op) :
    ir.evalE rd f (.apply (.batched B op) e) j =
      NamedOp.block ir f rd op
        (fun t => ir.evalE rd f e (j / NamedOp.rows ir op * NamedOp.cols ir op + t))
        (j % NamedOp.rows ir op) := by
  rw [evalE_apply]
  simp only [NamedOp.apply, NamedOp.block, NamedOp.rows, NamedOp.cols, Nat.div_eq_of_lt hj,
    Nat.mod_eq_of_lt hj, hj, if_true, ↓reduceIte, Nat.zero_mul, Nat.zero_add]

/-- The scheme-order transform reads only the first `n` coordinates of its operand. -/
theorem nttScheme_congr {K : Type*} [Field K] {n : ℕ} {ψ : K} {x y : ℕ → K}
    (hxy : ∀ t < n, x t = y t) (m : ℕ) : Ops.nttScheme n ψ x m = Ops.nttScheme n ψ y m := by
  unfold Ops.nttScheme
  split_ifs
  · exact NamedOp.nttNatural_congr hxy _
  · rfl

/-- **The field facts of a realization's root**: at `ψ < p`, `M < p`, `M = 2^k ≥ 1`, `2 < p` and
`ψ^M ≡ −1 (mod p)` in a field of characteristic `p`, the decoded root `ψ` is a primitive `2M`-th
root of unity and `M` is invertible. -/
theorem root_facts {K : Type*} [Field K] {p : ℕ} [CharP K p] {psi M : ℕ} (hp : 2 < p)
    (hpsi : psi ^ M % p = p - 1) (hM : M = 2 ^ Nat.log2 M) (hM0 : 0 < M) (hMp : M < p) :
    IsPrimitiveRoot (psi : K) (2 * M) ∧ (M : K) ≠ 0 := by
  have hneg : (psi : K) ^ M = -1 := by
    rw [← Nat.cast_pow, CharP.natCast_eq_natCast_mod K p, hpsi, Nat.cast_sub (by omega),
      CharP.cast_eq_zero, Nat.cast_one, zero_sub]
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K p] at this
    exact absurd (Nat.le_of_dvd (by norm_num) this) (by omega)
  refine ⟨?_, ?_⟩
  · rw [hM] at hneg ⊢
    exact Ops.isPrimitiveRoot_of_pow_eq_neg_one hneg h2
  · intro h
    rw [CharP.cast_eq_zero_iff K p] at h
    exact absurd (Nat.le_of_dvd hM0 h) (by omega)

/-- **Where its products predicate holds, a spectrally realized convolution's reading is its
source** (`ConvOkAt`): the shared expressions `read` and `source` have one length and agree below
it, at a reader `rd` whose zero constants read `0` (`hzero`), whose field decodes the naturals
below its characteristic `p` to their casts (`hdec`) and has characteristic `p` (`hchar`). Each
reading is `INTT_M(NTT_M(a) · NTT_M(b))` on the operands' rows zero-extended to `M`, the negacyclic
product (`Ops.inverseNtt_mul_nttScheme`), which no product wraps around
(`Ops.negacyclic_eq_conv`): the source's sum over the views `convLeft`, `convRight`. -/
theorem convRead_eq_source (ho : ir.RefsOrdered) {rd : ir.Valuation I} {d : ℕ}
    (hzero : ∀ v, ir.zeroConst v = true → ir.valueField v = ir.domainField d →
      ∀ i, ir.evalE rd (ir.domainField d) (.leaf v) i = 0)
    (hdec : ∀ c < (ir.field (ir.domainField d)).characteristic,
      (I (ir.domainField d)).decode c = (c : (I (ir.domainField d)).K))
    (hchar : CharP (I (ir.domainField d)).K (ir.field (ir.domainField d)).characteristic)
    {c : SpectralConv} (hc : ir.ConvOkAt d c)
    (hprod : ir.HoldsWith rd (ir.predicate c.products).body) :
    ir.exprLen (.ref c.read) = ir.exprLen (.ref c.source) ∧
      ∀ i < ir.exprLen (.ref c.source),
        ir.evalE rd (ir.domainField d) (.ref c.source) i =
          ir.evalE rd (ir.domainField d) (.ref c.read) i := by
  unfold ConvOkAt at hc
  split at hc
  case h_2 => exact hc.elim
  rename_i s r d' lhs z t hsrc hread hbody
  obtain ⟨hd, -, hpo⟩ := hc
  rw [hd] at hbody
  unfold ConvProductsOk at hpo
  split at hpo
  case h_2 => exact hpo.elim
  rename_i q hq
  have F := hpo
  set f := ir.domainField d with hf
  set B := c.blocks
  set la := c.left
  set lb := c.right
  set M := c.length
  have hS := Expr.eq_of_convSource? hsrc
  have hR := Expr.eq_of_convRead? hread
  have hQ := Expr.eq_of_convProducts? hq
  have hFla : s.la = la := F.la
  have hFmA : s.mA = IndexMap.convLeft B la lb := F.mA
  have hFmB : s.mB = IndexMap.convRight B la lb := F.mB
  have hFg : r.g = IndexMap.blockPrefix B M (la + lb - 1) := F.g
  have hFrB : r.B = B := F.rB
  have hFrM : r.M = M := F.rM
  have hFrpsi : r.psi = c.root := F.rpsi
  have hFrz : r.z = z := F.rz
  have hFpA : q.pA = IndexMap.zeroExtend B la M := F.pA
  have hFpB : q.pB = IndexMap.zeroExtend B lb M := F.pB
  have hFlenA : ir.exprLen s.a = B * la := F.lenA
  have hFlenB : ir.exprLen s.b = B * lb := F.lenB
  have hFpow : M = 2 ^ Nat.log2 M := F.pow2
  have hQB : q.B = B := F.qB.1
  have hQB' : q.B' = B := F.qB.2
  have hQM : q.M = M := F.qM.1
  have hQM' : q.M' = M := F.qM.2
  have hQpsi : q.psi = c.root := F.qpsi.1
  have hQpsi' : q.psi' = c.root := F.qpsi.2
  have hla : 0 < la := F.left_pos
  have hlb : 0 < lb := F.right_pos
  have hfit : la + lb - 1 ≤ M := F.fits
  have hM0 : 0 < M := by omega
  have hlaM : la ≤ M := by omega
  have hlbM : lb ≤ M := by omega
  have hzA := hzero s.zA (F.zeros s.zA (by simp)) (F.fields s.zA (by simp))
  have hzB := hzero s.zB (F.zeros s.zB (by simp)) (F.fields s.zB (by simp))
  have hzA' := hzero q.zA (F.zeros q.zA (by simp)) (F.fields q.zA (by simp))
  have hzB' := hzero q.zB (F.zeros q.zB (by simp)) (F.fields q.zB (by simp))
  -- The root.
  have hpsi : (I f).decode c.root = (c.root : (I f).K) := hdec _ F.root_lt
  obtain ⟨hprim, hMinv⟩ := @root_facts _ _ _ hchar c.root M F.char F.root_pow hFpow hM0
    F.length_lt
  rw [hFla] at hS
  -- Lengths.
  have hlenS : ir.exprLen (.ref c.source) = B * (la + lb - 1) := by
    rw [exprLen_ref ho F.source_lt, hS, exprLen_apply, exprLen_mul, exprLen_reindex, hFmA,
      IndexMap.size_convLeft hla]
    simp only [NamedOp.cols, NamedOp.rows, Nat.mul_one]
    rw [← Nat.mul_assoc, Nat.mul_div_cancel _ hla]
  have hlenR : ir.exprLen (.ref c.read) = B * (la + lb - 1) := by
    rw [exprLen_ref ho F.read_lt, hR, exprLen_reindex, hFg, IndexMap.size_blockPrefix]
  refine ⟨hlenR.trans hlenS.symm, fun i hi => ?_⟩
  rw [hlenS] at hi
  -- The block and the coordinate.
  set lc := la + lb - 1
  have hlc : 0 < lc := by omega
  set blk := i / lc
  set k := i % lc
  have hk : k < lc := Nat.mod_lt _ hlc
  have hblk : blk < B := (Nat.div_lt_iff_lt_mul hlc).2 hi
  have hik : i = blk * lc + k := by
    have := Nat.div_add_mod i lc
    rw [Nat.mul_comm] at this
    exact this.symm
  have hkM : k < M := by omega
  -- The operands' rows.
  set u : ℕ → (I f).K := fun t => if t < la then ir.evalE rd f s.a (blk * la + t) else 0 with hu
  set v : ℕ → (I f).K := fun t => if t < lb then ir.evalE rd f s.b (blk * lb + t) else 0 with hv
  -- The products predicate at the block's coordinates.
  have hz : ∀ m < M, ir.evalE rd f (.leaf z) (blk * M + m) =
      Ops.nttScheme M (c.root : (I f).K) u m * Ops.nttScheme M (c.root : (I f).K) v m := by
    intro m hm
    have hbody' := hbody
    rw [hQ] at hbody'
    have hh : ir.HoldsWith rd (ir.predicate c.products).body := hprod
    rw [hbody'] at hh
    have hlenL : blk * M + m < ir.exprLen (.mul (.apply (.batched q.B (.ntt q.M q.psi .scheme))
        (.reindex q.pA (.concat q.a (.leaf q.zA))))
        (.apply (.batched q.B' (.ntt q.M' q.psi' .scheme))
          (.reindex q.pB (.concat q.b (.leaf q.zB))))) := by
      rw [exprLen_mul, exprLen_apply, exprLen_reindex, hFpA, IndexMap.size_zeroExtend hlaM]
      simp only [NamedOp.cols, NamedOp.rows, hQB, hQM]
      rw [Nat.div_self (Nat.mul_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) hblk) hM0), Nat.one_mul]
      exact IndexMap.block_lt hblk hm
    have h1 := hh (blk * M + m) hlenL
    simp only [evalWith] at h1
    rw [← h1, evalE_mul]
    have hrow : blk * M + m < q.B * NamedOp.rows ir (.ntt q.M q.psi .scheme) := by
      simp only [NamedOp.rows, hQB, hQM]
      exact IndexMap.block_lt hblk hm
    have hrow' : blk * M + m < q.B' * NamedOp.rows ir (.ntt q.M' q.psi' .scheme) := by
      simp only [NamedOp.rows, hQB', hQM']
      exact IndexMap.block_lt hblk hm
    rw [evalE_apply_batched rd f _ _ _ hrow, evalE_apply_batched rd f _ _ _ hrow']
    simp only [NamedOp.block, NamedOp.rows, NamedOp.cols, hQM, hQM', hQpsi, hQpsi', hpsi]
    rw [(IndexMap.block_div_mod hm).1, (IndexMap.block_div_mod hm).2]
    congr 1
    · refine nttScheme_congr (fun t ht => ?_) m
      rw [evalE_reindex, hFpA, IndexMap.entry_zeroExtend hlaM hblk ht, F.qa]
      simp only [hu]
      split_ifs with htl
      · rw [evalE_concat, if_pos (by rw [hFlenA]; exact IndexMap.block_lt hblk htl)]
      · rw [evalE_concat, if_neg (by rw [hFlenA]; omega), hFlenA, Nat.sub_self, hzA']
    · refine nttScheme_congr (fun t ht => ?_) m
      rw [evalE_reindex, hFpB, IndexMap.entry_zeroExtend hlbM hblk ht, F.qb]
      simp only [hv]
      split_ifs with htl
      · rw [evalE_concat, if_pos (by rw [hFlenB]; exact IndexMap.block_lt hblk htl)]
      · rw [evalE_concat, if_neg (by rw [hFlenB]; omega), hFlenB, Nat.sub_self, hzB']
  -- The reading.
  have hread' : ir.evalE rd f (.ref c.read) i =
      ∑ t : Fin la, if (t : ℕ) ≤ k ∧ k - t < lb then u t * v (k - t) else 0 := by
    rw [evalE_ref ho rd f F.read_lt, hR, evalE_reindex, hFg, hik,
      IndexMap.entry_blockPrefix hblk hk]
    have hrow : blk * M + k < r.B * NamedOp.rows ir (.inverseNtt r.M r.psi) := by
      simp only [NamedOp.rows, hFrB, hFrM]
      exact IndexMap.block_lt hblk hkM
    rw [evalE_apply_batched rd f _ _ _ hrow]
    simp only [NamedOp.block, NamedOp.rows, NamedOp.cols, hFrM, hFrpsi, hFrz, hpsi]
    rw [(IndexMap.block_div_mod hkM).1, (IndexMap.block_div_mod hkM).2,
      Ops.inverseNtt_congr (y := fun m => Ops.nttScheme M (c.root : (I f).K) u m *
        Ops.nttScheme M (c.root : (I f).K) v m) (fun m hm => hz m hm),
      Ops.inverseNtt_mul_nttScheme hFpow hprim hMinv u v hkM,
      Ops.negacyclic_eq_conv u v (fun t ht => by simp [hu, show ¬ t < la by omega])
        (fun t ht => by simp [hv, show ¬ t < lb by omega]) hla hlb hfit hkM]
  -- The source.
  have hsource : ir.evalE rd f (.ref c.source) i =
      ∑ t : Fin la, if (t : ℕ) ≤ k ∧ k - t < lb then u t * v (k - t) else 0 := by
    rw [evalE_ref ho rd f F.source_lt, hS, evalE_apply_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    have ht := t.isLt
    rw [evalE_mul, evalE_reindex, evalE_reindex, hFmA, hFmB, hik,
      IndexMap.entry_convLeft hla hblk hk ht, IndexMap.entry_convRight hla hblk hk ht]
    by_cases hcond : k + 1 - lb ≤ (t : ℕ) ∧ (t : ℕ) ≤ k
    · rw [if_pos hcond, if_pos hcond, if_pos ⟨hcond.2, by omega⟩, evalE_concat, evalE_concat,
        if_pos (by rw [hFlenA]; exact IndexMap.block_lt hblk ht),
        if_pos (by rw [hFlenB]; exact IndexMap.block_lt hblk (show k - (t : ℕ) < lb by omega))]
      simp only [hu, hv, if_pos ht, if_pos (show k - (t : ℕ) < lb by omega)]
    · rw [if_neg hcond, if_neg hcond, if_neg (fun h => hcond ⟨by omega, h.1⟩), evalE_concat,
        if_neg (by rw [hFlenA]; omega), hFlenA, Nat.sub_self, hzA, zero_mul]
  rw [hsource, hread']


/-- **The facts of a spectrally realized convolution at its products predicate**
(`ConvOkAt`): the parts of its source, reading and products, with `ConvFacts`. -/
theorem ConvOkAt.facts {d : ℕ} {c : SpectralConv} (hc : ir.ConvOkAt d c) {lhs : Expr} {z : ℕ}
    {t : Target} (hb : (ir.predicate c.products).body = .equal d lhs (.leaf z) t) :
    ∃ s r q, (ir.expr c.source).convSource? = some s ∧ (ir.expr c.read).convRead? = some r ∧
      lhs.convProducts? = some q ∧ ir.ConvFacts c s r q d z := by
  unfold ConvOkAt at hc
  split at hc
  case h_2 => exact hc.elim
  rename_i s r d' lhs' z' t' hsrc hread hbody
  rw [hb] at hbody
  simp only [PredBody.equal.injEq, Expr.leaf.injEq] at hbody
  obtain ⟨-, rfl, rfl, rfl⟩ := hbody
  obtain ⟨-, -, hpo⟩ := hc
  unfold ConvProductsOk at hpo
  split at hpo
  case h_2 => exact hpo.elim
  rename_i q hq
  exact ⟨s, r, q, hsrc, hread, hq, hpo⟩

/-! ## Shared expressions read through their realizations -/

/-- **An expression's value below its length depends only on its shared expressions' values below
theirs** (`Expr.matchB`): where `P k k'` gives `k'` the length of `k` and `k`'s values below it, an
expression `E` matching a shape-correct `e` has `e`'s length and values below it. -/
theorem Expr.eval_matchB {f : ℕ} {leaf : ir.Valuation I} {ref : ℕ → ℕ → (I f).K} {rl : ℕ → ℕ}
    {P : ℕ → ℕ → Bool}
    (hP : ∀ k k', P k k' = true → rl k' = rl k ∧ ∀ i < rl k, ref k i = ref k' i) :
    ∀ (e E : Expr), Expr.matchB P e E = true → ir.shapeOkWith rl e = true →
      Expr.len ir rl E = Expr.len ir rl e ∧
        ∀ i < Expr.len ir rl e, Expr.eval ir f leaf ref rl e i = Expr.eval ir f leaf ref rl E i
  | .ref k, E, hm, _ => by
    cases E <;> simp only [Expr.matchB] at hm
    case ref k' =>
      simp only [Bool.or_eq_true, beq_iff_eq] at hm
      rcases hm with rfl | hm
      · exact ⟨rfl, fun _ _ => rfl⟩
      · obtain ⟨hl, he⟩ := hP k k' hm
        exact ⟨hl, fun i hi => he i hi⟩
    all_goals (cases Expr.eq_of_beq hm)
  | .add a b, E, hm, hs => by
    cases E <;> simp only [Expr.matchB] at hm
    case add a' b' =>
      simp only [Bool.and_eq_true] at hm
      simp only [shapeOkWith, Bool.and_eq_true, beq_iff_eq] at hs
      obtain ⟨ha1, ha2⟩ := Expr.eval_matchB (leaf := leaf) hP a a' hm.1 hs.1.1
      obtain ⟨hb1, hb2⟩ := Expr.eval_matchB (leaf := leaf) hP b b' hm.2 hs.1.2
      refine ⟨ha1, fun i hi => ?_⟩
      simp only [Expr.len] at hi
      simp only [Expr.eval, ha2 i hi, hb2 i (hs.2 ▸ hi)]
    all_goals (cases Expr.eq_of_beq hm)
  | .sub a b, E, hm, hs => by
    cases E <;> simp only [Expr.matchB] at hm
    case sub a' b' =>
      simp only [Bool.and_eq_true] at hm
      simp only [shapeOkWith, Bool.and_eq_true, beq_iff_eq] at hs
      obtain ⟨ha1, ha2⟩ := Expr.eval_matchB (leaf := leaf) hP a a' hm.1 hs.1.1
      obtain ⟨hb1, hb2⟩ := Expr.eval_matchB (leaf := leaf) hP b b' hm.2 hs.1.2
      refine ⟨ha1, fun i hi => ?_⟩
      simp only [Expr.len] at hi
      simp only [Expr.eval, ha2 i hi, hb2 i (hs.2 ▸ hi)]
    all_goals (cases Expr.eq_of_beq hm)
  | .mul a b, E, hm, hs => by
    cases E <;> simp only [Expr.matchB] at hm
    case mul a' b' =>
      simp only [Bool.and_eq_true] at hm
      simp only [shapeOkWith, Bool.and_eq_true, beq_iff_eq] at hs
      obtain ⟨ha1, ha2⟩ := Expr.eval_matchB (leaf := leaf) hP a a' hm.1 hs.1.1
      obtain ⟨hb1, hb2⟩ := Expr.eval_matchB (leaf := leaf) hP b b' hm.2 hs.1.2
      refine ⟨ha1, fun i hi => ?_⟩
      simp only [Expr.len] at hi
      simp only [Expr.eval, ha2 i hi, hb2 i (hs.2 ▸ hi)]
    all_goals (cases Expr.eq_of_beq hm)
  | .concat a b, E, hm, hs => by
    cases E <;> simp only [Expr.matchB] at hm
    case concat a' b' =>
      simp only [Bool.and_eq_true] at hm
      simp only [shapeOkWith, Bool.and_eq_true] at hs
      obtain ⟨ha1, ha2⟩ := Expr.eval_matchB (leaf := leaf) hP a a' hm.1 hs.1
      obtain ⟨hb1, hb2⟩ := Expr.eval_matchB (leaf := leaf) hP b b' hm.2 hs.2
      refine ⟨by simp only [Expr.len, ha1, hb1], fun i hi => ?_⟩
      simp only [Expr.len] at hi
      simp only [Expr.eval, ha1]
      split_ifs with h
      · exact ha2 i h
      · exact hb2 _ (by omega)
    all_goals (cases Expr.eq_of_beq hm)
  | .scale c a, E, hm, hs => by
    cases E <;> simp only [Expr.matchB] at hm
    case scale c' a' =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
      obtain ⟨rfl, hm⟩ := hm
      simp only [shapeOkWith] at hs
      obtain ⟨ha1, ha2⟩ := Expr.eval_matchB (leaf := leaf) hP a a' hm hs
      refine ⟨ha1, fun i hi => ?_⟩
      simp only [Expr.len] at hi
      simp only [Expr.eval, ha2 i hi]
    all_goals (cases Expr.eq_of_beq hm)
  | .reindex m a, E, hm, hs => by
    cases E <;> simp only [Expr.matchB] at hm
    case reindex m' a' =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
      obtain ⟨rfl, hm⟩ := hm
      simp only [shapeOkWith, Bool.and_eq_true] at hs
      obtain ⟨ha1, ha2⟩ := Expr.eval_matchB (leaf := leaf) hP a a' hm hs.1
      refine ⟨rfl, fun i hi => ?_⟩
      simp only [Expr.len] at hi
      simp only [Expr.eval]
      exact ha2 _ (IndexMap.entry_lt_of_inRange (by rw [← IndexMap.inRangeNat_eq]; exact hs.2) hi)
    all_goals (cases Expr.eq_of_beq hm)
  | .apply op a, E, hm, hs => by
    cases E <;> simp only [Expr.matchB] at hm
    case apply op' a' =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
      obtain ⟨rfl, hm⟩ := hm
      simp only [shapeOkWith, Bool.and_eq_true] at hs
      obtain ⟨ha1, ha2⟩ := Expr.eval_matchB (leaf := leaf) hP a a' hm hs.1.1
      refine ⟨by simp only [Expr.len, ha1], fun i hi => ?_⟩
      simp only [Expr.len] at hi
      simp only [Expr.eval, NamedOp.apply]
      have hrows : 0 < NamedOp.rows ir op := by
        rcases Nat.eq_zero_or_pos (NamedOp.rows ir op) with h | h
        · rw [h, Nat.mul_zero] at hi
          omega
        · exact h
      refine NamedOp.block_congr_cols ir leaf op (Nat.mod_lt _ hrows) fun t ht => ha2 _ ?_
      have hq : i / NamedOp.rows ir op < Expr.len ir rl a / NamedOp.cols ir op :=
        (Nat.div_lt_iff_lt_mul hrows).2 hi
      have := Nat.div_mul_le_self (Expr.len ir rl a) (NamedOp.cols ir op)
      have := IndexMap.block_lt hq ht
      omega
    all_goals (cases Expr.eq_of_beq hm)
  | .leaf v, E, hm, _ => by
    cases E <;> simp only [Expr.matchB] at hm <;> (cases Expr.eq_of_beq hm) <;>
      exact ⟨rfl, fun _ _ => rfl⟩
  | .linear rows a, E, hm, _ => by
    cases E <;> simp only [Expr.matchB] at hm <;> (cases Expr.eq_of_beq hm) <;>
      exact ⟨rfl, fun _ _ => rfl⟩
  | .prod n a, E, hm, _ => by
    cases E <;> simp only [Expr.matchB] at hm <;> (cases Expr.eq_of_beq hm) <;>
      exact ⟨rfl, fun _ _ => rfl⟩
  | .mux b t a, E, hm, _ => by
    cases E <;> simp only [Expr.matchB] at hm <;> (cases Expr.eq_of_beq hm) <;>
      exact ⟨rfl, fun _ _ => rfl⟩
  | .logic op w args, E, hm, _ => by
    cases E <;> simp only [Expr.matchB] at hm <;> (cases Expr.eq_of_beq hm) <;>
      exact ⟨rfl, fun _ _ => rfl⟩

/-- **The products predicate of a spectrally realized convolution** is a field `equal` of the
program whose target is no realization's. -/
theorem ConvOkAt.products {d : ℕ} {c : SpectralConv} (hc : ir.ConvOkAt d c) :
    c.products < ir.predicates.length ∧ ∃ lhs z t,
      (ir.predicate c.products).body = .equal d lhs (.leaf z) t ∧ t.isRealized = false := by
  unfold ConvOkAt at hc
  split at hc
  case h_2 => exact hc.elim
  rename_i s r d' lhs z t _ _ hbody
  obtain ⟨rfl, ht, hpo⟩ := hc
  unfold ConvProductsOk at hpo
  split at hpo
  case h_2 => exact hpo.elim
  exact ⟨hpo.products_lt, lhs, z, t, hbody, ht⟩

/-- **A zero constant reads `0`** in every environment where its field decodes `0` to `0`. -/
theorem evalE_leaf_zeroConst (e : ir.Env I) {f v : ℕ} (hv : ir.zeroConst v = true)
    (hf : ir.valueField v = f) (h0 : (I f).decode 0 = 0) (i : ℕ) :
    ir.evalE (ir.reader e) f (.leaf v) i = 0 := by
  unfold zeroConst at hv
  split at hv
  · rename_i es hk
    rw [evalE_leaf, reader_of_constant e hk]
    have h00 : es.getD i 0 = 0 := by
      rw [List.getD_eq_getElem?_getD]
      cases hes : es[i]? with
      | none => rfl
      | some c =>
        have := List.all_eq_true.1 hv c (List.mem_of_getElem? hes)
        simpa using this
    rw [h00, castElt_decode hf, h0]
  · cases hv

/-- **The shared expressions of a convolution and its reading agree below their length**
(`ConvPair`), where every spectrally realized convolution's products predicate holds
(`convRead_eq_source`). -/
theorem convPair_agree (ho : ir.RefsOrdered) {rd : ir.Valuation I} {d : ℕ}
    (hzero : ∀ v, ir.zeroConst v = true → ir.valueField v = ir.domainField d →
      ∀ i, ir.evalE rd (ir.domainField d) (.leaf v) i = 0)
    (hdec : ∀ c < (ir.field (ir.domainField d)).characteristic,
      (I (ir.domainField d)).decode c = (c : (I (ir.domainField d)).K))
    (hchar : CharP (I (ir.domainField d)).K (ir.field (ir.domainField d)).characteristic)
    (hprod : ∀ c ∈ ir.convs, ir.ConvOkAt d c → ir.HoldsWith rd (ir.predicate c.products).body) :
    ∀ k k', decide (ir.ConvPair d k k') = true →
      ir.refLen ir.exprs.length k' = ir.refLen ir.exprs.length k ∧
        ∀ i < ir.refLen ir.exprs.length k,
          ir.refVal rd ir.exprs.length (ir.domainField d) k i =
            ir.refVal rd ir.exprs.length (ir.domainField d) k' i := by
  intro k k' h
  obtain ⟨c, hc, rfl, rfl, hok⟩ := of_decide_eq_true h
  exact convRead_eq_source ho hzero hdec hchar hok (hprod c hc hok)

/-- **A realized predicate's sides read as the source's** (`RealizedAdmits`): `q` is a field
`equal` whose sides have the lengths of `e` and `e'` and their values below them, where the
convolutions' readings agree with their sources (`hP`, `convPair_agree`). -/
theorem realized_sides {rd : ir.Valuation I} {d : ℕ}
    (hP : ∀ k k', decide (ir.ConvPair d k k') = true →
      ir.refLen ir.exprs.length k' = ir.refLen ir.exprs.length k ∧
        ∀ i < ir.refLen ir.exprs.length k,
          ir.refVal rd ir.exprs.length (ir.domainField d) k i =
            ir.refVal rd ir.exprs.length (ir.domainField d) k' i)
    {e e' : Expr} {q : ℕ} (hR : ir.RealizedAdmits d e e' q) (hs : ir.exprShapeOk e = true)
    (hs' : ir.exprShapeOk e' = true) :
    q < ir.predicates.length ∧ ∃ E E' t, (ir.predicate q).body = .equal d E E' t ∧
      t.isRealized = false ∧
      ir.exprLen E = ir.exprLen e ∧ ir.exprLen E' = ir.exprLen e' ∧
      (∀ i < ir.exprLen e, ir.evalWith rd d e i = ir.evalWith rd d E i) ∧
      ∀ i < ir.exprLen e', ir.evalWith rd d e' i = ir.evalWith rd d E' i := by
  obtain ⟨hq, hm⟩ := hR
  split at hm
  case h_2 => exact hm.elim
  rename_i d' E E' t hbody
  obtain ⟨hd, ht, hm, hm'⟩ := hm
  rw [hd] at hbody
  have hsw : ∀ x, ir.exprShapeOk x = true →
      ir.shapeOkWith (ir.refLen ir.exprs.length) x = true := fun x hx => by
    rwa [exprShapeOk_eq] at hx
  obtain ⟨hl, hE⟩ := Expr.eval_matchB (leaf := rd) hP e E hm (hsw e hs)
  obtain ⟨hl', hE'⟩ := Expr.eval_matchB (leaf := rd) hP e' E' hm' (hsw e' hs')
  exact ⟨hq, E, E', t, hbody, ht, hl, hl', fun i hi => hE i hi, fun i hi => hE' i hi⟩

/-- **A realized field equation holds** (`RealizedAdmits`, `Target.realized q`): at a reader `rd`
where every field `equal` with no realization target holds (`hnr`), whose zero constants read `0`
and whose field decodes the naturals below its characteristic to their casts, the sides `e`, `e'`
(shape-correct, of one length) are equal: `q`'s sides are `e` and `e'` with every convolution
read through its realization, which agrees with it below its length where its products predicate
holds (`convRead_eq_source`, `Expr.eval_matchB`), and `q` holds. -/
theorem fieldEq_of_realized (ho : ir.RefsOrdered) {rd : ir.Valuation I} {d : ℕ}
    (hzero : ∀ v, ir.zeroConst v = true → ir.valueField v = ir.domainField d →
      ∀ i, ir.evalE rd (ir.domainField d) (.leaf v) i = 0)
    (hdec : ∀ c < (ir.field (ir.domainField d)).characteristic,
      (I (ir.domainField d)).decode c = (c : (I (ir.domainField d)).K))
    (hchar : CharP (I (ir.domainField d)).K (ir.field (ir.domainField d)).characteristic)
    (hnr : ∀ p < ir.predicates.length, ∀ d e e' t, (ir.predicate p).body = .equal d e e' t →
      t.isRealized = false → ir.HoldsWith rd (ir.predicate p).body)
    {e e' : Expr} {q : ℕ} (hR : ir.RealizedAdmits d e e' q) (hs : ir.exprShapeOk e = true)
    (hs' : ir.exprShapeOk e' = true) (hlen : ir.exprLen e' = ir.exprLen e) :
    ∀ i < ir.exprLen e, ir.evalWith rd d e i = ir.evalWith rd d e' i := by
  have hP := convPair_agree ho hzero hdec hchar fun c _ hok => by
    obtain ⟨hpl, lhs, z, t', hb, ht'⟩ := hok.products
    exact hnr c.products hpl _ _ _ _ hb ht'
  obtain ⟨hq, E, E', t, hbody, ht, hl, hl', hE, hE'⟩ := realized_sides hP hR hs hs'
  have hq' := hnr q hq _ _ _ _ hbody ht
  rw [hbody] at hq'
  intro i hi
  rw [hE i hi, hq' i (by rw [hl]; exact hi), ← hE' i (by rw [hlen]; exact hi)]

/-- **A realized predicate holds where the source's field equation does** (`RealizedAdmits`): at
a reader where every spectrally realized convolution's products predicate holds, `q` holds when
`e = e'` (`realized_sides`). -/
theorem holdsWith_realized_of_fieldEq (ho : ir.RefsOrdered) {rd : ir.Valuation I} {d : ℕ}
    (hzero : ∀ v, ir.zeroConst v = true → ir.valueField v = ir.domainField d →
      ∀ i, ir.evalE rd (ir.domainField d) (.leaf v) i = 0)
    (hdec : ∀ c < (ir.field (ir.domainField d)).characteristic,
      (I (ir.domainField d)).decode c = (c : (I (ir.domainField d)).K))
    (hchar : CharP (I (ir.domainField d)).K (ir.field (ir.domainField d)).characteristic)
    (hprod : ∀ c ∈ ir.convs, ir.ConvOkAt d c → ir.HoldsWith rd (ir.predicate c.products).body)
    {e e' : Expr} {q : ℕ} (hR : ir.RealizedAdmits d e e' q) (hs : ir.exprShapeOk e = true)
    (hs' : ir.exprShapeOk e' = true) (hlen : ir.exprLen e' = ir.exprLen e)
    (hfe : ∀ i < ir.exprLen e, ir.evalWith rd d e i = ir.evalWith rd d e' i) :
    ir.HoldsWith rd (ir.predicate q).body := by
  obtain ⟨-, E, E', t, hbody, -, hl, hl', hE, hE'⟩ :=
    realized_sides (convPair_agree ho hzero hdec hchar hprod) hR hs hs'
  rw [hbody]
  intro i hi
  rw [hl] at hi
  rw [← hE i hi, hfe i hi, hE' i (by rw [hlen]; exact hi)]
end

end GordieHowe.RealizedProgram
