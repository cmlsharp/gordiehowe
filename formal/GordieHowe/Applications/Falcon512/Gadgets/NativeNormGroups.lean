-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Gadgets.NativeEncoding

@[expose] public section

/-!
# The native Falcon norm and encoding as constraint groups

States the native norm (`GordieHowe.Falcon512.NativeNorm.run`) and the native encoding check
(`GordieHowe.Falcon512.NativeEncoding.run`) as separate constraint groups and per-cell range requests, the form
the GordieHowe native Falcon instance uses, and connects them to `NativeNorm.sound` and
`NativeEncoding.sound`, which take `run`'s acceptance and table membership.
-/

namespace GordieHowe.Falcon512.NativeNorm

variable {F : Type*} [Field F] [DecidableEq F]

/-! ### The norm as constraint groups

`run`'s fold, restated as independent constraint groups: one square check per coefficient,
one normalization per batch of its derived column sums `batchCol`, and the complement bound
(`Holds`, `run_ok_iff`); and its lookup requests, as one range request per committed digit
(`DigitsBelow`, `inTable_needles`); and soundness from the groups (`sound_of_holds`). -/

/-- Square digit `m` of coefficient `k`, zero past the last coefficient. -/
def sqAt (w : Wit F) (k : ℕ) (m : Fin 6) : F :=
  if h : k < 1024 then (w.square ⟨k, h⟩).sq m else 0

/-- The digits batch `b` starts from: the previous batch's normalized digits, zero for the
first batch. -/
def prevDigits (w : Wit F) (b : Fin 17) (m : Fin 6) : F :=
  if h : (b : ℕ) = 0 then 0 else (w.batch ⟨(b : ℕ) - 1, by omega⟩).ndig m

/-- **The derived column sums of batch `b`**: the previous batch's normalized digits (zero for the
first batch) plus the square digits of the batch's coefficients `63 b + k < 1024` (the C++
`native_running_sum` row, `lib/gordiehowe/lib/norm.h`: `prev[b][m] + Σ_k sq[63 b + k][m]`). -/
def batchCol (w : Wit F) (b : Fin 17) (m : Fin 6) : F :=
  prevDigits w b m + ∑ k ∈ Finset.Ico (startOf b) (startOf ((b : ℕ) + 1)), sqAt w k m

/-- **The sum over a batch's coefficients**: coefficients `startOf b ≤ k < startOf (b + 1)` are
`63 b + s`, `s < 63`, those past `1024` contributing `0`. -/
theorem sum_Ico_startOf {M : Type*} [AddCommMonoid M] {f : ℕ → M} (hf : ∀ k, 1024 ≤ k → f k = 0)
    {b : ℕ} (hb : b < 17) :
    ∑ k ∈ Finset.Ico (startOf b) (startOf (b + 1)), f k =
      ∑ s : Fin 63, f (63 * b + s) := by
  have h0 : startOf b = 63 * b := by unfold startOf; omega
  have hsub :
      Finset.Ico (63 * b) (startOf (b + 1)) ⊆ Finset.Ico (63 * b) (63 * b + 63) := by
    intro k hk
    simp only [Finset.mem_Ico, startOf] at hk ⊢
    omega
  rw [h0, Fin.sum_univ_eq_sum_range (fun s => f (63 * b + s)), Finset.sum_subset hsub,
    Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  intro k hk hk'
  apply hf
  simp only [Finset.mem_Ico, startOf] at hk hk'
  omega

/-- The fold's accumulator before coefficient `n < 1024`: the digits its batch starts from
plus the square digits of the batch's coefficients before `n`. -/
theorem prefixState_fst_eq (v : Fin 1024 → F) (w : Wit F) :
    ∀ n (hn : n < 1024) (m : Fin 6), (prefixState v w n).1 m =
      prevDigits w ⟨n / 63, by omega⟩ m + ∑ k ∈ Finset.Ico (63 * (n / 63)) n, sqAt w k m := by
  intro n
  induction n with
  | zero => intro _ m; simp [prevDigits]
  | succ n ih =>
    intro hn1 m
    have hn : n < 1024 := by omega
    rw [prefixState_fst_succ v w ⟨n, hn⟩]
    by_cases hb : boundary ⟨n, hn⟩ = true
    · rw [if_pos hb]
      have hmod : (n + 1) % 63 = 0 := by
        simp only [boundary, decide_eq_true_eq] at hb; omega
      have hdiv : (n + 1) / 63 = n / 63 + 1 := Nat.succ_div_of_mod_eq_zero hmod
      have hIco : 63 * ((n + 1) / 63) = n + 1 := by omega
      rw [hIco, Finset.Ico_self, Finset.sum_empty, add_zero, prevDigits,
        dif_neg (show ((n + 1) / 63 : ℕ) ≠ 0 by omega)]
      congr 2
      apply Fin.ext
      simp only [batchIndex]
      omega
    · rw [if_neg hb]
      have hmod : (n + 1) % 63 ≠ 0 := by
        simp only [boundary, decide_eq_true_eq, not_or] at hb; exact hb.1
      have hdiv : (n + 1) / 63 = n / 63 := Nat.succ_div_of_mod_ne_zero hmod
      dsimp only
      rw [ih hn m]
      have hle : 63 * (n / 63) ≤ n := Nat.mul_div_le n 63
      simp only [hdiv]
      rw [Finset.sum_Ico_succ_top hle, sqAt, dif_pos hn, add_assoc]

/-- At a batch boundary, the column sums `step` normalizes are the batch's `batchCol`. -/
theorem boundary_col_eq (v : Fin 1024 → F) (w : Wit F) {i : Fin 1024} (hb : boundary i = true) :
    (fun m => (prefixState v w (i : ℕ)).1 m + (w.square i).sq m) = batchCol w (batchIndex i) := by
  funext m
  have hstart := startOf_batchIndex_succ i.isLt hb
  have hs0 : startOf (batchIndex i : ℕ) = 63 * ((i : ℕ) / 63) := by
    simp only [startOf, batchIndex]; omega
  rw [prefixState_fst_eq v w i i.isLt m, batchCol, hs0, hstart,
    Finset.sum_Ico_succ_top (Nat.mul_div_le (i : ℕ) 63), sqAt, dif_pos i.isLt, add_assoc]
  rfl

/-- **The constraint groups of the native norm**: every coefficient's square check (centering and
columns), every batch's normalization of its derived column sums, and the complement bound. -/
structure Holds (v : Fin 1024 → F) (w : Wit F) : Prop where
  square : ∀ i : Fin 1024, (square (decide (512 ≤ (i : ℕ))) (v i) (w.square i)).ok = true
  batch : ∀ b : Fin 17, (batchNormalize (batchCol w b) (w.batch b)).ok = true
  bound : (leqConst 34034726 (w.batch 16).ndig w.D w.Dcarry).ok = true

/-- Every prefix of the fold accepts when the constraint groups hold. -/
theorem prefixState_ok_of_holds {v : Fin 1024 → F} {w : Wit F} (h : Holds v w) :
    ∀ n, n ≤ 1024 → (prefixState v w n).2.ok = true := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn1
    have hn : n < 1024 := by omega
    rw [prefixState_succ v w hn, step_snd_eq]
    simp only [Check.and_ok, Bool.and_eq_true_iff]
    refine ⟨⟨ih (by omega), h.square _⟩, ?_⟩
    split
    · rename_i hb
      rw [boundary_col_eq v w (i := ⟨n, hn⟩) hb]
      exact h.batch _
    · rfl

theorem run_ok_iff (v : Fin 1024 → F) (w : Wit F) : (run v w).ok = true ↔ Holds v w := by
  constructor
  · intro h
    refine ⟨square_ok v w h, fun b => ?_, leqConst_ok v w h⟩
    obtain ⟨i, hb, rfl⟩ := exists_boundary_witness b
    rw [← boundary_col_eq v w hb]
    exact batchNormalize_ok v w h i hb
  · intro h
    rw [run_eq]
    simp only [Check.and_ok, Bool.and_eq_true_iff]
    exact ⟨prefixState_ok_of_holds h 1024 le_rfl, h.bound⟩

/-- **Every committed digit of the norm witness is below `64`** (the requests `norm.a`, `norm.sq`,
`norm.cc`, `norm.nd`, `norm.nc`, `norm.D`). -/
structure DigitsBelow (w : Wit F) : Prop where
  a : ∀ i l, Range.IsNatBelow 64 ((w.square i).a l)
  sq : ∀ i m, Range.IsNatBelow 64 ((w.square i).sq m)
  carry : ∀ i m l, Range.IsNatBelow 64 ((w.square i).carry m l)
  ndig : ∀ b m, Range.IsNatBelow 64 ((w.batch b).ndig m)
  ncarry : ∀ b m, Range.IsNatBelow 64 ((w.batch b).ncarry m)
  D : ∀ m, Range.IsNatBelow 64 (w.D m)

/-- A coefficient's square check requests exactly its magnitude digits, square digits and
carry limbs. -/
theorem square_inTable {hi : Bool} {v : F} {s : SquareWit F}
    (ha : ∀ l, Range.IsNatBelow 64 (s.a l)) (hsq : ∀ m, Range.IsNatBelow 64 (s.sq m))
    (hc : ∀ m l, Range.IsNatBelow 64 (s.carry m l)) :
    Range.InTable 64 (square hi v s).needles := by
  intro x hx
  simp only [square, Check.and_needles, List.mem_append, Check.all_needles, List.mem_flatMap,
    List.mem_map, List.mem_finRange, true_and] at hx
  rcases hx with hx | ⟨_, ⟨m, rfl⟩, hx⟩
  · obtain ⟨l, rfl⟩ := List.mem_ofFn.mp hx
    exact ha l
  · split at hx
    · simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hsq m
      · obtain ⟨l, rfl⟩ := List.mem_ofFn.mp hx
        exact hc _ l
    · simp only [List.mem_singleton] at hx
      subst hx
      exact hsq m

/-- A batch normalization requests exactly its digits and carries. -/
theorem batchNormalize_inTable {col : Fin 6 → F} {b : BatchWit F}
    (hd : ∀ m, Range.IsNatBelow 64 (b.ndig m)) (hc : ∀ m, Range.IsNatBelow 64 (b.ncarry m)) :
    Range.InTable 64 (batchNormalize col b).needles := by
  intro x hx
  simp only [batchNormalize, Check.all_needles, List.mem_flatMap, List.mem_map,
    List.mem_finRange, true_and] at hx
  obtain ⟨_, ⟨m, rfl⟩, hx⟩ := hx
  split at hx
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact hd m
    · exact hc _
  · simp only [List.mem_singleton] at hx
    subst hx
    exact hd m

/-- The complement check requests exactly the complement digits. -/
theorem leqConst_inTable {C : ℕ} {S D Dc : Fin 6 → F} (hD : ∀ m, Range.IsNatBelow 64 (D m)) :
    Range.InTable 64 (leqConst C S D Dc).needles := by
  intro x hx
  simp only [leqConst, Check.and_needles, Check.assert_needles, List.append_nil,
    Check.all_needles, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and] at hx
  obtain ⟨_, ⟨m, rfl⟩, hx⟩ := hx
  simp only [List.mem_singleton] at hx
  rw [hx]
  exact hD m

/-- Every prefix's needles are committed digits. -/
theorem prefixState_inTable {v : Fin 1024 → F} {w : Wit F} (h : DigitsBelow w) :
    ∀ n, n ≤ 1024 → Range.InTable 64 (prefixState v w n).2.needles := by
  intro n
  induction n with
  | zero => intro _ x hx; simp at hx
  | succ n ih =>
    intro hn1
    have hn : n < 1024 := by omega
    rw [prefixState_succ v w hn, step_snd_eq]
    refine Check.and_inTable (Check.and_inTable (ih (by omega))
      (square_inTable (h.a _) (h.sq _) (h.carry _))) ?_
    split
    · exact batchNormalize_inTable (h.ndig _) (h.ncarry _)
    · intro x hx; simp at hx

/-- The norm's needles are its committed digits. -/
theorem inTable_needles {v : Fin 1024 → F} {w : Wit F} (h : DigitsBelow w) :
    Range.InTable 64 (run v w).needles := by
  rw [run_eq]
  exact Check.and_inTable (prefixState_inTable h 1024 le_rfl) (leqConst_inTable h.D)

/-- **Soundness of the native norm, from its constraint groups**: `sound` with the run's
acceptance and table membership replaced by `Holds` and `DigitsBelow`. -/
theorem sound_of_holds [CharP F 12289] {v : Fin 1024 → F} {w : Wit F}
    (hd : DigitsBelow w) (h : Holds v w) :
    ∃ vals : Fin 1024 → ℕ, EmulatedNorm.Lifted 12289 34034726 v vals ∧
      ∀ i : Fin 1024, 512 ≤ (i : ℕ) →
        ∃ a : ℕ, a < 64 ^ 2 ∧ (a : F) = mag true (w.square i) ∧
          (LatticeCrypto.centeredRepr (vals i : ZMod 12289)).natAbs = a :=
  sound (inTable_needles hd) ((run_ok_iff v w).mpr h)

/-! ### The normalization and the complement bound as per-column equations

`batchNormalize` and `leqConst` as the affine rows the C++ emits (`norm.h`, `native_running_sum`:
`prev + Σ sq + nc[m-1] − nd[m] − B nc[m] = 0`, absent terms zero; `native_at_most`:
`S[m] + D[m] + Dc[m-1] − digit(β², m) − B Dc[m] = 0`, `Dc` Boolean, `Dc[5] = 0`). -/

/-- The incoming carry of column `m`: carry `m - 1`, zero for the first column. -/
def carryIn (c : Fin 5 → F) (m : Fin 6) : F :=
  if h : (m : ℕ) = 0 then 0 else c ⟨m - 1, by omega⟩

/-- The outgoing carry of column `m`: carry `m`, zero for the last column. -/
def carryOut (c : Fin 5 → F) (m : Fin 6) : F :=
  if h : (m : ℕ) < 5 then c ⟨m, h⟩ else 0

/-- The incoming complement carry of column `m`: `Dc[m - 1]`, zero for the first column. -/
def dcIn (Dc : Fin 6 → F) (m : Fin 6) : F :=
  if h : (m : ℕ) = 0 then 0 else Dc ⟨m - 1, by omega⟩

/-- **The normalization as per-column equations**: `col[m] + nc[m-1] = nd[m] + B nc[m]`. -/
theorem batchNormalize_ok_iff (col : Fin 6 → F) (b : BatchWit F) :
    (batchNormalize col b).ok = true ↔
      ∀ m : Fin 6, col m + carryIn b.ncarry m - b.ndig m - 64 * carryOut b.ncarry m = 0 := by
  simp only [batchNormalize, Check.all_ok, List.all_eq_true, List.mem_map, List.mem_finRange,
    true_and, forall_exists_index, forall_apply_eq_imp_iff]
  refine forall_congr' fun m => ?_
  by_cases h : (m : ℕ) < 5
  · simp only [h, dite_true, decide_eq_true_eq, carryIn, carryOut]
    exact sub_eq_zero.symm.trans (by rw [sub_sub])
  · simp only [h, dite_false, decide_eq_true_eq, carryIn, carryOut, mul_zero, sub_zero]
    exact sub_eq_zero.symm

/-- **The complement bound as per-column equations**: `Dc` Boolean,
`S[m] + D[m] + Dc[m-1] = digit(C, m) + B Dc[m]`, and `Dc[5] = 0`. -/
theorem leqConst_ok_iff (C : ℕ) (S D Dc : Fin 6 → F) :
    (leqConst C S D Dc).ok = true ↔
      (∀ m, Dc m * (Dc m - 1) = 0) ∧
        (∀ m, S m + D m + dcIn Dc m - (digit C m : F) - 64 * Dc m = 0) ∧ Dc 5 = 0 := by
  simp only [leqConst, Check.and_ok, Check.all_ok, Check.assert_ok, Bool.and_eq_true,
    List.all_eq_true, List.mem_map, List.mem_finRange, true_and, forall_exists_index,
    forall_apply_eq_imp_iff, decide_eq_true_eq]
  constructor
  · rintro ⟨h, h5⟩
    refine ⟨fun m => (h m).1, fun m => ?_, h5⟩
    rw [dcIn, sub_sub, sub_eq_zero]
    exact (h m).2
  · rintro ⟨hb, he, h5⟩
    refine ⟨fun m => ⟨hb m, ?_⟩, h5⟩
    have := he m
    rw [dcIn, sub_sub, sub_eq_zero] at this
    exact this

/-- **The square check as equations**: the centering `v² = mag²` and the six columns
`colprod_m + C_{m−1} = sq_m + 64 C_m` (`C_5 = 0`, `C_{−1} = 0`). -/
theorem square_ok_iff (hi : Bool) (v : F) (s : SquareWit F) :
    (square hi v s).ok = true ↔ v * v = mag hi s * mag hi s ∧
      ∀ m : Fin 6, colprod (limbs hi s) m + carryIn (carryVal s) m - s.sq m -
        64 * carryOut (carryVal s) m = 0 := by
  simp only [square, Check.and_ok, Bool.and_eq_true, decide_eq_true_eq, Check.all_ok,
    List.all_eq_true, List.mem_map, List.mem_finRange, true_and, forall_exists_index,
    forall_apply_eq_imp_iff]
  refine and_congr Iff.rfl (forall_congr' fun m => ?_)
  by_cases h : (m : ℕ) < 5
  · simp only [h, dite_true, decide_eq_true_eq, carryIn, carryOut]
    by_cases h0 : (m : ℕ) = 0
    · simp only [h0, dite_true]
      constructor
      · intro hh; rw [hh]; ring
      · intro hh; linear_combination hh
    · simp only [h0, dite_false]
      constructor
      · intro hh; rw [hh]; ring
      · intro hh; linear_combination hh
  · have h0 : (m : ℕ) ≠ 0 := by omega
    simp only [h, dite_false, decide_eq_true_eq, carryIn, carryOut, h0, mul_zero, sub_zero]
    constructor
    · intro hh; rw [hh]; ring
    · intro hh; linear_combination hh

end GordieHowe.Falcon512.NativeNorm

namespace GordieHowe.Falcon512.NativeEncoding

variable {F : Type*} [Field F] [DecidableEq F]

/-- The bit `b = a₁ − 2 a₂` of `s₂` coefficient `i`: its raw middle digit minus twice the high
part stored in the top slot. -/
def parityBit (w : NativeNorm.Wit F) (i : Fin 512) : F :=
  (w.square ⟨512 + i, by omega⟩).a 1 - 2 * high w i

/-- **The encoding's Boolean checks**: for every `s₂` coefficient, `b = a₁ − 2 a₂` is a bit. -/
def BitsHold (w : NativeNorm.Wit F) : Prop :=
  ∀ i : Fin 512, parityBit w i * (parityBit w i - 1) = 0

theorem run_ok_iff (w : NativeNorm.Wit F) (slackHi : F) :
    (run w slackHi).ok = true ↔ BitsHold w := by
  simp only [run, Check.and_ok, Bool.and_true, Check.all_ok, List.all_eq_true, List.mem_map,
    List.mem_finRange, true_and, forall_exists_index, forall_apply_eq_imp_iff, decide_eq_true_eq,
    BitsHold, parityBit, high]

/-- **The encoding's requests hold**: each high slot plus `48`, the low slack digit
`392 − Σ h − 64 slackHi`, and `slackHi`, below `64`. -/
structure RequestsHold (w : NativeNorm.Wit F) (slackHi : F) : Prop where
  high : ∀ i : Fin 512, Range.IsNatBelow 64 ((w.square ⟨512 + i, by omega⟩).a 2 + 48)
  slackLo : Range.IsNatBelow 64 (392 - ∑ i, NativeEncoding.high w i - 64 * slackHi)
  slackHi : Range.IsNatBelow 64 slackHi

theorem inTable_needles_iff (w : NativeNorm.Wit F) (slackHi : F) :
    Range.InTable 64 (run w slackHi).needles ↔ RequestsHold w slackHi := by
  constructor
  · intro h
    exact ⟨fun i => h _ (coeff_needle_mem w slackHi i), h _ (slackLo_mem_needles w slackHi),
      h _ (slackHi_mem_needles w slackHi)⟩
  · intro h v hv
    rw [run, Check.and_needles, List.mem_append] at hv
    rcases hv with hv | hv
    · rw [Check.all_needles, List.mem_flatMap] at hv
      obtain ⟨c, hc, hv'⟩ := hv
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hc
      simp only [List.mem_singleton] at hv'
      rw [hv']
      exact h.high i
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · exact h.slackLo
      · exact h.slackHi

end GordieHowe.Falcon512.NativeEncoding
