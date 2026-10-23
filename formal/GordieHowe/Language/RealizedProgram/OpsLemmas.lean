-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.Semantics
public import GordieHowe.Language.Realizations.Bits

@[expose] public section

/-!
# GordieHowe: facts about the Logic builders and the MAC convolution

Facts about the Logic builders (`Ops.ltReduce`, `Ops.eqReduce`, `Ops.andTree`, `Ops.orTree`,
`LogicOp.eval`) and the MAC's carry-free convolution (`Ops.macConv`) of
`GordieHowe/Language/RealizedProgram/Ops.lean`, which the interval evaluator (`GordieHowe/Language/RealizedProgram/Interval.lean`)
reads:

* **Booleans in, Booleans out** (`LogicOp.eval_bool`): on arguments whose coordinates in the window
  read are `0` or `1`, every Logic builder is `0` or `1` (`lt_reduce` keeps the pair `(eq, lt)` in
  `{(1, 0), (0, 0), (0, 1)}`, `ltReduce_bool`).
* **Ring maps** (`LogicOp.eval_map`): a ring map commutes with every Logic builder (they are
  polynomials in their arguments).
* **The window read** (`LogicOp.eval_congr`): output coordinate `j` reads only coordinates
  `j w, …, j w + w − 1` of its arguments.
* **The MAC convolution on a unit vector** (`Ops.macConv_single`): its column `c w + i` is entry
  `(b, i)` of the matrix of chunk `c`.
* **Comparison on bits** (`Ops.ltReduce_eq`, `Ops.ltWord_eq_ltConst`): on bits, `lt_reduce` is the
  pair `([A = B], [A < B])` of the windows' naturals (`Ops.winNat`), so `Logic::lt` against a
  constant's bits is the gadget library's comparator `Bits.ltConst`.
-/

namespace GordieHowe.RealizedProgram

namespace Ops

section Logic

variable {R S : Type*} [CommRing R] [CommRing S]

/-- **`lor` of two bits is a bit.** -/
theorem lor_bool {a b : R} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    lor a b = 0 ∨ lor a b = 1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [lor]

/-- **`lt_reduce` on bits** keeps the pair `(eq, lt)` in `{(1, 0), (0, 0), (0, 1)}`. -/
theorem ltReduce_bool {a b : ℕ → R} (n : ℕ) :
    ∀ i0, (∀ t < n, a (i0 + t) = 0 ∨ a (i0 + t) = 1) →
      (∀ t < n, b (i0 + t) = 0 ∨ b (i0 + t) = 1) →
      ((ltReduce a b n i0).1 = 1 ∧ (ltReduce a b n i0).2 = 0) ∨
        ((ltReduce a b n i0).1 = 0 ∧ (ltReduce a b n i0).2 = 0) ∨
        ((ltReduce a b n i0).1 = 0 ∧ (ltReduce a b n i0).2 = 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i0 ha hb
    rcases n with _ | _ | n
    · simp [ltReduce.eq_1]
    · simp only [Nat.zero_add, ltReduce.eq_2 (R := R)]
      have ha0 : a i0 = 0 ∨ a i0 = 1 := by simpa using ha 0 (by omega)
      have hb0 : b i0 = 0 ∨ b i0 = 1 := by simpa using hb 0 (by omega)
      rcases ha0 with h | h <;> rcases hb0 with h' | h' <;> simp [h, h', lxor] <;> norm_num
    · simp only [ltReduce.eq_3 (R := R)]
      set h := (n + 2) / 2
      have hh : h ≤ n + 2 := Nat.div_le_self _ _
      have hpos : 0 < h := by omega
      have lo := ih h (by omega) i0 (fun t ht => ha t (by omega)) (fun t ht => hb t (by omega))
      have hi := ih (n + 2 - h) (by omega) (i0 + h)
        (fun t ht => by simpa [Nat.add_assoc] using ha (h + t) (by omega))
        (fun t ht => by simpa [Nat.add_assoc] using hb (h + t) (by omega))
      rcases hi with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
      · simpa using lo
      · simp
      · simp

/-- **`eq_reduce` on bits is a bit.** -/
theorem eqReduce_bool {a b : ℕ → R} (n : ℕ) :
    ∀ i0, (∀ t < n, a (i0 + t) = 0 ∨ a (i0 + t) = 1) →
      (∀ t < n, b (i0 + t) = 0 ∨ b (i0 + t) = 1) →
      eqReduce a b n i0 = 0 ∨ eqReduce a b n i0 = 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i0 ha hb
    rcases n with _ | _ | n
    · simp [eqReduce.eq_1]
    · simp only [Nat.zero_add, eqReduce.eq_2 (R := R)]
      have ha0 : a i0 = 0 ∨ a i0 = 1 := by simpa using ha 0 (by omega)
      have hb0 : b i0 = 0 ∨ b i0 = 1 := by simpa using hb 0 (by omega)
      rcases ha0 with h | h <;> rcases hb0 with h' | h' <;> simp [h, h', lxor] <;> norm_num
    · simp only [eqReduce.eq_3 (R := R)]
      set h := (n + 2) / 2
      have hh : h ≤ n + 2 := Nat.div_le_self _ _
      have lo := ih h (by omega) i0 (fun t ht => ha t (by omega)) (fun t ht => hb t (by omega))
      have hi := ih (n + 2 - h) (by omega) (i0 + h)
        (fun t ht => by simpa [Nat.add_assoc] using ha (h + t) (by omega))
        (fun t ht => by simpa [Nat.add_assoc] using hb (h + t) (by omega))
      rcases lo with h1 | h1 <;> rcases hi with h2 | h2 <;> simp [h1, h2]

/-- **The balanced AND tree on bits is a bit.** -/
theorem andTree_bool {a : ℕ → R} (n : ℕ) :
    ∀ i0, (∀ t < n, a (i0 + t) = 0 ∨ a (i0 + t) = 1) →
      andTree a n i0 = 0 ∨ andTree a n i0 = 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i0 ha
    rcases n with _ | _ | n
    · simp [andTree.eq_1]
    · simp only [Nat.zero_add, andTree.eq_2 (R := R)]
      simpa using ha 0 (by omega)
    · simp only [andTree.eq_3 (R := R)]
      set h := (n + 2) / 2
      have hh : h ≤ n + 2 := Nat.div_le_self _ _
      have lo := ih h (by omega) i0 (fun t ht => ha t (by omega))
      have hi := ih (n + 2 - h) (by omega) (i0 + h)
        (fun t ht => by simpa [Nat.add_assoc] using ha (h + t) (by omega))
      rcases lo with h1 | h1 <;> rcases hi with h2 | h2 <;> simp [h1, h2]

/-- **The balanced OR tree on bits is a bit.** -/
theorem orTree_bool {a : ℕ → R} (n : ℕ) :
    ∀ i0, (∀ t < n, a (i0 + t) = 0 ∨ a (i0 + t) = 1) →
      orTree a n i0 = 0 ∨ orTree a n i0 = 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i0 ha
    rcases n with _ | _ | n
    · simp [orTree.eq_1]
    · simp only [Nat.zero_add, orTree.eq_2 (R := R)]
      simpa using ha 0 (by omega)
    · simp only [orTree.eq_3 (R := R)]
      set h := (n + 2) / 2
      have hh : h ≤ n + 2 := Nat.div_le_self _ _
      have lo := ih h (by omega) i0 (fun t ht => ha t (by omega))
      have hi := ih (n + 2 - h) (by omega) (i0 + h)
        (fun t ht => by simpa [Nat.add_assoc] using ha (h + t) (by omega))
      exact lor_bool lo hi

/-- **A ring map commutes with `lxor`.** -/
theorem lxor_map (φ : R →+* S) (a b : R) : φ (lxor a b) = lxor (φ a) (φ b) := by
  simp [lxor, map_ofNat]

/-- **A ring map commutes with `lor`.** -/
theorem lor_map (φ : R →+* S) (a b : R) : φ (lor a b) = lor (φ a) (φ b) := by
  simp [lor]

/-- **A ring map commutes with `lt_reduce`.** -/
theorem ltReduce_map (φ : R →+* S) (a b : ℕ → R) (n : ℕ) :
    ∀ i0, (φ (ltReduce a b n i0).1, φ (ltReduce a b n i0).2) =
      ltReduce (fun t => φ (a t)) (fun t => φ (b t)) n i0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i0
    rcases n with _ | _ | n
    · simp [ltReduce.eq_1]
    · simp [ltReduce.eq_2, lxor_map]
    · rw [ltReduce.eq_3, ltReduce.eq_3]
      have lo := Prod.ext_iff.1 (ih ((n + 2) / 2) (by omega) i0)
      have hi := Prod.ext_iff.1 (ih (n + 2 - (n + 2) / 2) (by omega) (i0 + (n + 2) / 2))
      dsimp only at lo hi ⊢
      rw [map_mul, map_add, map_mul, lo.1, lo.2, hi.1, hi.2]

/-- **A ring map commutes with `eq_reduce`.** -/
theorem eqReduce_map (φ : R →+* S) (a b : ℕ → R) (n : ℕ) :
    ∀ i0, φ (eqReduce a b n i0) = eqReduce (fun t => φ (a t)) (fun t => φ (b t)) n i0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i0
    rcases n with _ | _ | n
    · simp [eqReduce.eq_1]
    · simp [eqReduce.eq_2, lxor_map]
    · rw [eqReduce.eq_3, eqReduce.eq_3, map_mul, ih _ (by omega), ih _ (by omega)]

/-- **A ring map commutes with the balanced AND tree.** -/
theorem andTree_map (φ : R →+* S) (a : ℕ → R) (n : ℕ) :
    ∀ i0, φ (andTree a n i0) = andTree (fun t => φ (a t)) n i0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i0
    rcases n with _ | _ | n
    · simp [andTree.eq_1]
    · simp [andTree.eq_2]
    · rw [andTree.eq_3, andTree.eq_3, map_mul, ih _ (by omega), ih _ (by omega)]

/-- **A ring map commutes with the balanced OR tree.** -/
theorem orTree_map (φ : R →+* S) (a : ℕ → R) (n : ℕ) :
    ∀ i0, φ (orTree a n i0) = orTree (fun t => φ (a t)) n i0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i0
    rcases n with _ | _ | n
    · simp [orTree.eq_1]
    · simp [orTree.eq_2]
    · rw [orTree.eq_3, orTree.eq_3, lor_map, ih _ (by omega), ih _ (by omega)]

/-- **`lt_reduce` reads only its window** `[i0, i0 + n)`. -/
theorem ltReduce_congr {a b a' b' : ℕ → R} (n : ℕ) :
    ∀ i0, (∀ t < n, a (i0 + t) = a' (i0 + t)) → (∀ t < n, b (i0 + t) = b' (i0 + t)) →
      ltReduce a b n i0 = ltReduce a' b' n i0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i0 ha hb
    rcases n with _ | _ | n
    · simp [ltReduce.eq_1]
    · have ha0 : a i0 = a' i0 := by simpa using ha 0 (by omega)
      have hb0 : b i0 = b' i0 := by simpa using hb 0 (by omega)
      simp [ltReduce.eq_2, ha0, hb0]
    · rw [ltReduce.eq_3, ltReduce.eq_3]
      set h := (n + 2) / 2
      rw [ih h (by omega) i0 (fun t ht => ha t (by omega)) (fun t ht => hb t (by omega)),
        ih (n + 2 - h) (by omega) (i0 + h)
          (fun t ht => by simpa [Nat.add_assoc] using ha (h + t) (by omega))
          (fun t ht => by simpa [Nat.add_assoc] using hb (h + t) (by omega))]

/-- **`eq_reduce` reads only its window** `[i0, i0 + n)`. -/
theorem eqReduce_congr {a b a' b' : ℕ → R} (n : ℕ) :
    ∀ i0, (∀ t < n, a (i0 + t) = a' (i0 + t)) → (∀ t < n, b (i0 + t) = b' (i0 + t)) →
      eqReduce a b n i0 = eqReduce a' b' n i0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i0 ha hb
    rcases n with _ | _ | n
    · simp [eqReduce.eq_1]
    · have ha0 : a i0 = a' i0 := by simpa using ha 0 (by omega)
      have hb0 : b i0 = b' i0 := by simpa using hb 0 (by omega)
      simp [eqReduce.eq_2, ha0, hb0]
    · rw [eqReduce.eq_3, eqReduce.eq_3]
      set h := (n + 2) / 2
      rw [ih h (by omega) i0 (fun t ht => ha t (by omega)) (fun t ht => hb t (by omega)),
        ih (n + 2 - h) (by omega) (i0 + h)
          (fun t ht => by simpa [Nat.add_assoc] using ha (h + t) (by omega))
          (fun t ht => by simpa [Nat.add_assoc] using hb (h + t) (by omega))]

/-- **The balanced AND tree reads only its window** `[i0, i0 + n)`. -/
theorem andTree_congr {a a' : ℕ → R} (n : ℕ) :
    ∀ i0, (∀ t < n, a (i0 + t) = a' (i0 + t)) → andTree a n i0 = andTree a' n i0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i0 ha
    rcases n with _ | _ | n
    · simp [andTree.eq_1]
    · simpa [andTree.eq_2] using ha 0 (by omega)
    · rw [andTree.eq_3, andTree.eq_3]
      set h := (n + 2) / 2
      rw [ih h (by omega) i0 (fun t ht => ha t (by omega)),
        ih (n + 2 - h) (by omega) (i0 + h)
          (fun t ht => by simpa [Nat.add_assoc] using ha (h + t) (by omega))]

/-- **The balanced OR tree reads only its window** `[i0, i0 + n)`. -/
theorem orTree_congr {a a' : ℕ → R} (n : ℕ) :
    ∀ i0, (∀ t < n, a (i0 + t) = a' (i0 + t)) → orTree a n i0 = orTree a' n i0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i0 ha
    rcases n with _ | _ | n
    · simp [orTree.eq_1]
    · simpa [orTree.eq_2] using ha 0 (by omega)
    · rw [orTree.eq_3, orTree.eq_3]
      set h := (n + 2) / 2
      rw [ih h (by omega) i0 (fun t ht => ha t (by omega)),
        ih (n + 2 - h) (by omega) (i0 + h)
          (fun t ht => by simpa [Nat.add_assoc] using ha (h + t) (by omega))]

end Logic

/-! ## The MAC convolution on a unit vector -/

section MacConv

variable {K : Type*} [Field K]

/-- **The MAC convolution on the unit vector `e_{c w + i}`** is entry `(b, i)` of the matrix of
chunk `c` (for `b < w`). -/
theorem macConv_single (w nch : ℕ) (taps : List ℕ) (rb : ℕ → Fin w → ℕ) {b : ℕ} (hb : b < w)
    (c : Fin nch) (i : Fin w) :
    macConv w nch taps rb (fun s => if s = (c : ℕ) * w + i then (1 : K) else 0) b =
      (Conv.matrix taps.toFinset (rb c) ⟨b, hb⟩ i : K) := by
  rw [macConv, dif_pos hb, Finset.sum_eq_single c, Finset.sum_eq_single i]
  · simp
  · intro i' _ hi'
    rw [if_neg (fun h => hi' (Fin.ext (by omega))), mul_zero]
  · simp
  · intro c' _ hc'
    refine Finset.sum_eq_zero fun i' _ => ?_
    rw [if_neg, mul_zero]
    intro h
    apply hc'
    have h1 : (c' : ℕ) * w + i' < ((c' : ℕ) + 1) * w := by
      have := i'.2
      rw [Nat.add_mul, Nat.one_mul]
      omega
    have h2 : (c : ℕ) * w + i < ((c : ℕ) + 1) * w := by
      have := i.2
      rw [Nat.add_mul, Nat.one_mul]
      omega
    have h3 : (c' : ℕ) * w ≤ (c' : ℕ) * w + i' := Nat.le_add_right _ _
    have h4 : (c : ℕ) * w ≤ (c : ℕ) * w + i := Nat.le_add_right _ _
    refine Fin.ext (le_antisymm ?_ ?_)
    · by_contra hlt
      push Not at hlt
      have := Nat.mul_le_mul_right w (Nat.succ_le_of_lt hlt)
      rw [Nat.succ_eq_add_one] at this
      omega
    · by_contra hlt
      push Not at hlt
      have := Nat.mul_le_mul_right w (Nat.succ_le_of_lt hlt)
      rw [Nat.succ_eq_add_one] at this
      omega
  · simp

end MacConv

section Compare

variable {R : Type*} [Field R] [DecidableEq R]

/-- **The natural number of a window of bits**: `Σ_{t < n} 2^t [a(i0 + t) = 1]`, the little-endian
reading of the coordinates `i0, …, i0 + n − 1` of `a` (`Bits.natOfBits` on a window of a vector
indexed by `ℕ`). -/
def winNat (a : ℕ → R) (i0 n : ℕ) : ℕ :=
  ∑ t ∈ Finset.range n, if a (i0 + t) = 1 then 2 ^ t else 0

/-- A window of `n` bits reads a natural below `2^n`. -/
theorem winNat_lt (a : ℕ → R) (i0 n : ℕ) : winNat a i0 n < 2 ^ n := by
  induction n with
  | zero => simp [winNat]
  | succ n ih =>
    rw [winNat, Finset.sum_range_succ, ← winNat, pow_succ]
    split_ifs <;> omega

/-- **A window splits** into its first `h` coordinates and the rest. -/
theorem winNat_add (a : ℕ → R) (i0 h m : ℕ) :
    winNat a i0 (h + m) = winNat a i0 h + 2 ^ h * winNat a (i0 + h) m := by
  simp only [winNat, Finset.sum_range_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Nat.add_assoc, pow_add]
  split_ifs <;> simp

/-- The window of the bits of a constant is the constant modulo `2^n`. -/
theorem winNat_constBit (c n : ℕ) :
    winNat (fun t => Bits.constBit (K := R) c t) 0 n = c % 2 ^ n := by
  induction n with
  | zero => simp [winNat, Nat.mod_one]
  | succ n ih =>
    rw [winNat, Finset.sum_range_succ, ← winNat, ih, Nat.zero_add, pow_succ, Nat.mod_mul]
    rcases Nat.mod_two_eq_zero_or_one (c / 2 ^ n) with h | h <;>
      simp [Bits.constBit, h]

omit [Field R] [DecidableEq R] in
/-- **Two-digit comparison**: with low digits below `P`, `x₁ + P x₂ < y₁ + P y₂` exactly when the
high digits compare so, or are equal and the low digits do. -/
theorem lex_lt {P x₁ x₂ y₁ y₂ : ℕ} (hx : x₁ < P) (hy : y₁ < P) :
    x₁ + P * x₂ < y₁ + P * y₂ ↔ x₂ < y₂ ∨ (x₂ = y₂ ∧ x₁ < y₁) := by
  constructor
  · intro h
    rcases lt_trichotomy x₂ y₂ with h2 | rfl | h2
    · exact .inl h2
    · exact .inr ⟨rfl, by omega⟩
    · have : P * (y₂ + 1) ≤ P * x₂ := Nat.mul_le_mul_left _ h2
      rw [mul_add, mul_one] at this
      omega
  · rintro (h2 | ⟨rfl, h1⟩)
    · have : P * (x₂ + 1) ≤ P * y₂ := Nat.mul_le_mul_left _ h2
      rw [mul_add, mul_one] at this
      omega
    · omega

omit [Field R] [DecidableEq R] in
/-- **Two-digit equality**: with low digits below `P`, `x₁ + P x₂ = y₁ + P y₂` exactly when both
digits are equal. -/
theorem lex_eq {P x₁ x₂ y₁ y₂ : ℕ} (hx : x₁ < P) (hy : y₁ < P) :
    x₁ + P * x₂ = y₁ + P * y₂ ↔ x₂ = y₂ ∧ x₁ = y₁ := by
  constructor
  · intro h
    rcases lt_trichotomy x₂ y₂ with h2 | rfl | h2
    · exact absurd h (ne_of_lt ((lex_lt hx hy).2 (.inl h2)))
    · exact ⟨rfl, by omega⟩
    · exact absurd h.symm (ne_of_lt ((lex_lt hy hx).2 (.inl h2)))
  · rintro ⟨rfl, rfl⟩
    rfl

/-- **`lt_reduce` on bits computes the comparison**: on a window whose coordinates are `0` or `1`,
`lt_reduce` is the pair `([A = B], [A < B])` of the window's naturals (`winNat`). -/
theorem ltReduce_eq {a b : ℕ → R} (n : ℕ) :
    ∀ i0, (∀ t < n, a (i0 + t) = 0 ∨ a (i0 + t) = 1) →
      (∀ t < n, b (i0 + t) = 0 ∨ b (i0 + t) = 1) →
      ltReduce a b n i0 = (if winNat a i0 n = winNat b i0 n then 1 else 0,
        if winNat a i0 n < winNat b i0 n then 1 else 0) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i0 ha hb
    rcases n with _ | _ | n
    · simp [ltReduce.eq_1, winNat]
    · rw [Nat.zero_add, ltReduce.eq_2 (R := R)]
      have ha0 : a i0 = 0 ∨ a i0 = 1 := by simpa using ha 0 (by omega)
      have hb0 : b i0 = 0 ∨ b i0 = 1 := by simpa using hb 0 (by omega)
      rcases ha0 with h | h <;> rcases hb0 with h' | h' <;> simp [winNat, h, h', lxor]; norm_num
    · rw [ltReduce.eq_3 (R := R)]
      set h := (n + 2) / 2
      have hpos : 0 < h := by omega
      have hle : h ≤ n + 2 := Nat.div_le_self _ _
      have lo := ih h (by omega) i0 (fun t ht => ha t (by omega)) (fun t ht => hb t (by omega))
      have hi := ih (n + 2 - h) (by omega) (i0 + h)
        (fun t ht => by simpa [Nat.add_assoc] using ha (h + t) (by omega))
        (fun t ht => by simpa [Nat.add_assoc] using hb (h + t) (by omega))
      simp only [lo, hi]
      have hsplit : ∀ c : ℕ → R,
          winNat c i0 (n + 2) = winNat c i0 h + 2 ^ h * winNat c (i0 + h) (n + 2 - h) :=
        fun c => by rw [← winNat_add, Nat.add_sub_cancel' hle]
      simp only [hsplit a, hsplit b, lex_eq (winNat_lt a i0 h) (winNat_lt b i0 h),
        lex_lt (winNat_lt a i0 h) (winNat_lt b i0 h)]
      generalize winNat a i0 h = x₁
      generalize winNat b i0 h = y₁
      generalize winNat a (i0 + h) (n + 2 - h) = x₂
      generalize winNat b (i0 + h) (n + 2 - h) = y₂
      by_cases h2 : x₂ = y₂
      · subst h2
        by_cases h1 : x₁ = y₁
        · subst h1
          simp
        · rcases Nat.lt_or_gt_of_ne h1 with h1 | h1 <;> simp [h1, Nat.ne_of_lt, Nat.ne_of_gt]
      · rcases Nat.lt_or_gt_of_ne h2 with h2' | h2' <;> simp [h2, h2', Nat.not_lt_of_gt]

/-- **`a < c` on a word of `w` bits against the constant `c`** (`Logic::lt` with the constant's
bits) is `Bits.ltConst`, the comparator of the gadget library, when the word's bits are `0` or `1`
and `c < 2^w`. -/
theorem ltWord_eq_ltConst {w c : ℕ} {a : ℕ → R} (ha : ∀ t < w, a t = 0 ∨ a t = 1)
    (hc : c < 2 ^ w) :
    ltWord w a (fun t => Bits.constBit c t) = Bits.ltConst (fun t : Fin w => a t) c := by
  have hab : ∀ t < w, Bits.constBit (K := R) c (0 + t) = 0 ∨ Bits.constBit (K := R) c (0 + t) = 1 :=
    fun t _ => Bits.constBit_bool c _
  rw [ltWord, ltReduce_eq w 0 (fun t ht => by simpa using ha t ht) hab, winNat_constBit,
    Nat.mod_eq_of_lt hc, Bits.ltConst_eq (fun t => ha t t.isLt) hc]
  simp only [winNat, Bits.natOfBits, Nat.zero_add,
    Fin.sum_univ_eq_sum_range (fun t => if a t = 1 then 2 ^ t else 0) w]

end Compare

end Ops

/-! ## The Logic builders -/

namespace LogicOp

variable {R S : Type*} [CommRing R] [CommRing S]

/-- **On bits, a Logic builder is a bit**: output coordinate `j` of `op` on arguments whose
coordinates `j w, …, j w + w − 1` are `0` or `1`. -/
theorem eval_bool (op : LogicOp) (w : ℕ) {args : List (ℕ → R)} (j : ℕ)
    (h : ∀ f ∈ args, ∀ t < w, f (j * w + t) = 0 ∨ f (j * w + t) = 1) :
    op.eval w args j = 0 ∨ op.eval w args j = 1 := by
  have h0 : ∀ t < w, args.headD 0 (j * w + (0 + t)) = 0 ∨ args.headD 0 (j * w + (0 + t)) = 1 := by
    intro t ht
    rw [Nat.zero_add]
    cases args with
    | nil => exact .inl rfl
    | cons f _ => exact h f (List.mem_cons_self ..) t ht
  have h1 : ∀ t < w,
      args.getD 1 0 (j * w + (0 + t)) = 0 ∨ args.getD 1 0 (j * w + (0 + t)) = 1 := by
    intro t ht
    rw [Nat.zero_add, List.getD_eq_getElem?_getD]
    cases hg : args[1]? with
    | none => exact .inl rfl
    | some f => exact h f (List.mem_of_getElem? hg) t ht
  cases op with
  | lt =>
    rcases Ops.ltReduce_bool (a := fun t => args.headD 0 (j * w + t))
      (b := fun t => args.getD 1 0 (j * w + t)) w 0 h0 h1 with h' | h' | h'
    · exact .inl h'.2
    · exact .inl h'.2
    · exact .inr h'.2
  | leq =>
    rcases Ops.ltReduce_bool (a := fun t => args.getD 1 0 (j * w + t))
      (b := fun t => args.headD 0 (j * w + t)) w 0 h1 h0 with h' | h' | h' <;>
      simp only [eval, Ops.leqWord, Ops.ltWord, h'.2] <;> norm_num
  | eq => exact Ops.eqReduce_bool w 0 h0 h1
  | any => exact Ops.orTree_bool w 0 h0
  | all => exact Ops.andTree_bool w 0 h0

/-- **A ring map commutes with a Logic builder**, applied to every argument. -/
theorem eval_map (φ : R →+* S) (op : LogicOp) (w : ℕ) (args : List (ℕ → R)) (j : ℕ) :
    φ (op.eval w args j) = op.eval w (args.map fun f t => φ (f t)) j := by
  have h0 : ∀ t, φ (args.headD 0 t) =
      (args.map fun (f : ℕ → R) (t : ℕ) => φ (f t)).headD (0 : ℕ → S) t := by
    intro t
    cases args <;> simp
  have h1 : ∀ t, φ (args.getD 1 0 t) =
      (args.map fun (f : ℕ → R) (t : ℕ) => φ (f t)).getD 1 (0 : ℕ → S) t := by
    intro t
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases args[1]? <;> simp
  cases op with
  | lt =>
    simp only [eval, Ops.ltWord, ← h0, ← h1]
    exact congrArg Prod.snd (Ops.ltReduce_map φ _ _ w 0)
  | leq =>
    simp only [eval, Ops.leqWord, Ops.ltWord, map_sub, map_one, ← h0, ← h1]
    rw [← congrArg Prod.snd (Ops.ltReduce_map φ _ _ w 0)]
  | eq =>
    simp only [eval, Ops.eqWord, ← h0, ← h1]
    exact Ops.eqReduce_map φ _ _ w 0
  | any =>
    simp only [eval, ← h0]
    exact Ops.orTree_map φ _ w 0
  | all =>
    simp only [eval, ← h0]
    exact Ops.andTree_map φ _ w 0

/-- **A Logic builder reads only its window**: output coordinate `j` of `op` is the same on two
argument lists that agree, argument by argument, at coordinates `j w, …, j w + w − 1`. -/
theorem eval_congr (op : LogicOp) (w : ℕ) {args args' : List (ℕ → R)} (j : ℕ)
    (h : List.Forall₂ (fun f g => ∀ t < w, f (j * w + t) = g (j * w + t)) args args') :
    op.eval w args j = op.eval w args' j := by
  have h0 : ∀ t < w, args.headD 0 (j * w + (0 + t)) = args'.headD 0 (j * w + (0 + t)) := by
    intro t ht
    rw [Nat.zero_add]
    cases h with
    | nil => rfl
    | cons hfg _ => exact hfg t ht
  have h1 : ∀ t < w, args.getD 1 0 (j * w + (0 + t)) = args'.getD 1 0 (j * w + (0 + t)) := by
    intro t ht
    rw [Nat.zero_add]
    cases h with
    | nil => rfl
    | cons _ h' =>
      cases h' with
      | nil => rfl
      | cons hfg _ => exact hfg t ht
  cases op with
  | lt =>
    simp only [eval, Ops.ltWord]
    rw [Ops.ltReduce_congr (a' := fun t => args'.headD 0 (j * w + t))
      (b' := fun t => args'.getD 1 0 (j * w + t)) w 0 h0 h1]
  | leq =>
    simp only [eval, Ops.leqWord, Ops.ltWord]
    rw [Ops.ltReduce_congr (a' := fun t => args'.getD 1 0 (j * w + t))
      (b' := fun t => args'.headD 0 (j * w + t)) w 0 h1 h0]
  | eq =>
    simp only [eval, Ops.eqWord]
    rw [Ops.eqReduce_congr (a' := fun t => args'.headD 0 (j * w + t))
      (b' := fun t => args'.getD 1 0 (j * w + t)) w 0 h0 h1]
  | any =>
    simp only [eval]
    rw [Ops.orTree_congr (a' := fun t => args'.headD 0 (j * w + t)) w 0 h0]
  | all =>
    simp only [eval]
    rw [Ops.andTree_congr (a' := fun t => args'.headD 0 (j * w + t)) w 0 h0]

end LogicOp

end GordieHowe.RealizedProgram
