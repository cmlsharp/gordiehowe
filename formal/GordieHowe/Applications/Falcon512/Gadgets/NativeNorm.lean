-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.ToMathlib.List
public import GordieHowe.Applications.Falcon512.Gadgets.EmulatedNorm
public import GordieHowe.Foundations.Algebra.CheckOps
public import GordieHowe.Applications.Falcon512.SchoolbookSquareBound
public import GordieHowe.Foundations.Algebra.ReconstructSum
public import GordieHowe.Foundations.Algebra.CenteredMagnitude
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.CharP.Basic

@[expose] public section

/-!
# The native Falcon `ℓ₂` norm

Over a field of characteristic `q = 12289` the squared norm (up to `β² ≈ 2^25`) cannot be formed
directly, so the native arm checks it one base-`64` digit at a time. This file transcribes the
flagship C++ (`fn-native`, `lib/schemes/falcon/falcon_norm.h`: `falcon_assert_square`,
`falcon_assert_norm_periodic`, `falcon_assert_leq_const`; parameters from
`lib/params/param_sets.h`, `kFalconNative{64, 16, 3, 63}`: `B = 64`, three magnitude
limbs, six square digits, six sum digits, batch width `Wc = 63`, `2n = 1024` coefficients, the `s₂`
coefficients from index `512` on).

Per coefficient `v` (`square`):
* three magnitude digits `a[0..3)`, each a lookup request in `[0, 64)`. For an
  `s₂` coefficient the top slot holds the encoding high part and the magnitude is
  the lower two digits (`limbs`);
* the centering assertion `v² = mag²`, so `mag ≡ ±v (mod q)`;
* the schoolbook columns `Σ_{j+k=m} x_j x_k + C_{m−1} = sq[m] + 64·C_m`, with the
  square digits `sq[m]` and the two-limb carries `C_m` requested in `[0, 64)`,
  and the last column's carry zero. These equations hold only modulo `q`.

The running sum (`run`) adds each coefficient's square digits into derived
column sums and normalizes them into committed digits `ndig` and carries
`ncarry` after every `63` coefficients and after the last (`batchNormalize`, 17
batches; the top column has carry zero). The final digits `S` satisfy
`S + D = β²` limbwise with Boolean carries and final carry zero (`leqConst`).

The C++ also commits a sixth batch carry `ncarry[5]` that no constraint reads; it
is omitted here.

Soundness (`sound`) is a backward argument: the batch and complement equalities are exact over the
integers, so the represented squares sum to at most `β²`; reading each coefficient's columns from
the top, the represented square is at least `mag²`; and `mag ≥ |centered v|`. The argument depends
on the exact parameters, so the theorem is stated at them.
-/

namespace GordieHowe.Falcon512.NativeNorm

variable {F : Type*} [Field F] [DecidableEq F]

/-- One coefficient's advice: magnitude digits, square digits and the two-limb
column carries. -/
structure SquareWit (F : Type*) where
  a : Fin 3 → F
  sq : Fin 6 → F
  carry : Fin 5 → Fin 2 → F

/-- One batch normalization: the committed digits and carries. -/
structure BatchWit (F : Type*) where
  ndig : Fin 6 → F
  ncarry : Fin 5 → F

/-- The committed norm witness for the `1024` coefficients of `s₁ ‖ s₂`. -/
structure Wit (F : Type*) where
  square : Fin 1024 → SquareWit F
  batch : Fin 17 → BatchWit F
  D : Fin 6 → F
  Dcarry : Fin 6 → F

/-- The magnitude digits the schoolbook square reads: for an `s₂` coefficient
(`hi`) the top slot holds the encoding high part and is replaced by zero. -/
def limbs (hi : Bool) (s : SquareWit F) : Fin 3 → F :=
  fun l => if hi = true ∧ (l : ℕ) = 2 then 0 else s.a l

/-- The magnitude the centering assertion reads. -/
def mag (hi : Bool) (s : SquareWit F) : F :=
  Range.reconstruct 64 (List.ofFn (limbs hi s))

/-- The value of a two-limb column carry. -/
def carryVal (s : SquareWit F) (m : Fin 5) : F :=
  Range.reconstruct 64 (List.ofFn (s.carry m))

/-- The schoolbook column product `Σ_{j+k=m} x_j x_k`. -/
def colprod (x : Fin 3 → F) (m : ℕ) : F :=
  ∑ j : Fin 3, ∑ k : Fin 3, if (j : ℕ) + k = m then x j * x k else 0

/-- One coefficient: magnitude requests, centering, and the six square columns. -/
def square (hi : Bool) (v : F) (s : SquareWit F) : Check F :=
  let x := limbs hi s
  let a := mag hi s
  let cin : Fin 6 → F := fun m => if h : (m : ℕ) = 0 then 0 else carryVal s ⟨m - 1, by omega⟩
  let columns := Check.all <| (List.finRange 6).map fun (m : Fin 6) =>
    if h : (m : ℕ) < 5 then
      (⟨decide (colprod x (m : ℕ) + cin m = s.sq m + 64 * carryVal s ⟨m, h⟩),
        s.sq m :: List.ofFn (s.carry ⟨m, h⟩)⟩ : Check F)
    else ⟨decide (colprod x (m : ℕ) + cin m = s.sq m), [s.sq m]⟩
  (⟨decide (v * v = a * a), List.ofFn s.a⟩ : Check F).and columns

/-- Normalize the derived column sums into one batch's committed digits. -/
def batchNormalize (col : Fin 6 → F) (b : BatchWit F) : Check F :=
  let cin : Fin 6 → F := fun m => if h : (m : ℕ) = 0 then 0 else b.ncarry ⟨m - 1, by omega⟩
  Check.all <| (List.finRange 6).map fun (m : Fin 6) =>
    if h : (m : ℕ) < 5 then
      (⟨decide (col m + cin m = b.ndig m + 64 * b.ncarry ⟨m, h⟩),
        [b.ndig m, b.ncarry ⟨m, h⟩]⟩ : Check F)
    else ⟨decide (col m + cin m = b.ndig m), [b.ndig m]⟩

/-- Base-`64` digit `m` of a public constant. -/
def digit (C m : ℕ) : ℕ := C / 64 ^ m % 64

/-- `S ≤ C`: the complement `D` with Boolean carries, `S + D = C` limbwise, and
final carry zero. -/
def leqConst (C : ℕ) (S D Dc : Fin 6 → F) : Check F :=
  let cin : Fin 6 → F := fun m => if h : (m : ℕ) = 0 then 0 else Dc ⟨m - 1, by omega⟩
  (Check.all <| (List.finRange 6).map fun (m : Fin 6) =>
    (⟨decide (Dc m * (Dc m - 1) = 0) &&
        decide (S m + D m + cin m = (digit C m : F) + 64 * Dc m), [D m]⟩ : Check F)).and
    (Check.assert (decide (Dc 5 = 0)))

/-- Coefficient `i` ends a batch: every `63` coefficients, and the last. -/
def boundary (i : Fin 1024) : Bool := decide (((i : ℕ) + 1) % 63 = 0 ∨ (i : ℕ) + 1 = 1024)

/-- The batch that coefficient `i` belongs to. -/
def batchIndex (i : Fin 1024) : Fin 17 := ⟨(i : ℕ) / 63, by omega⟩

/-- One step of the running sum: check the coefficient's square, add its digits
into the derived columns, and normalize at a batch boundary. -/
def step (v : Fin 1024 → F) (w : Wit F) (st : (Fin 6 → F) × Check F) (i : Fin 1024) :
    (Fin 6 → F) × Check F :=
  let s := w.square i
  let chk := st.2.and (square (decide (512 ≤ (i : ℕ))) (v i) s)
  let col : Fin 6 → F := fun m => st.1 m + s.sq m
  if boundary i then
    let b := w.batch (batchIndex i)
    (b.ndig, chk.and (batchNormalize col b))
  else (col, chk)

/-- The native norm gadget on the `1024` coefficient wires of `s₁ ‖ s₂`, with the
Falcon-512 bound `β² = 34034726`. -/
def run (v : Fin 1024 → F) (w : Wit F) : Check F :=
  let st := (List.finRange 1024).foldl (step v w) (fun _ => 0, Check.pass)
  st.2.and (leqConst 34034726 (w.batch 16).ndig w.D w.Dcarry)

/-! ### The fold as a sequence of prefixes

`run`'s `foldl` is never unfolded over `List.finRange 1024` at once: every fact
about it is proved by peeling off one coefficient at a time from `prefixState`,
via `prefixState_succ`. -/

/-- The fold's state after processing the first `n` coefficients (`n ≤ 1024`). -/
def prefixState (v : Fin 1024 → F) (w : Wit F) (n : ℕ) : (Fin 6 → F) × Check F :=
  ((List.finRange 1024).take n).foldl (step v w) (fun _ => 0, Check.pass)

@[simp] theorem prefixState_zero (v : Fin 1024 → F) (w : Wit F) :
    prefixState v w 0 = (fun _ => 0, Check.pass) := rfl

/-- One step of the prefix. -/
theorem prefixState_succ (v : Fin 1024 → F) (w : Wit F) {n : ℕ} (hn : n < 1024) :
    prefixState v w (n + 1) = step v w (prefixState v w n) ⟨n, hn⟩ := by
  unfold prefixState
  rw [List.take_succ_finRange hn, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem prefixState_full (v : Fin 1024 → F) (w : Wit F) :
    prefixState v w 1024 = (List.finRange 1024).foldl (step v w) (fun _ => 0, Check.pass) := by
  show ((List.finRange 1024).take 1024).foldl (step v w) (fun _ => 0, Check.pass) = _
  rw [List.take_of_length_le (l := List.finRange 1024) (by simp)]

/-- `run` is the final prefix followed by the complement check. -/
theorem run_eq (v : Fin 1024 → F) (w : Wit F) :
    run v w = (prefixState v w 1024).2.and (leqConst 34034726 (w.batch 16).ndig w.D w.Dcarry) := by
  simp only [run, prefixState_full]

/-- `step`'s second component: the previous prefix's check, extended by exactly
one coefficient's square check and, at a batch boundary, that batch's
normalization. -/
theorem step_snd_eq (v : Fin 1024 → F) (w : Wit F) (st : (Fin 6 → F) × Check F) (i : Fin 1024) :
    (step v w st i).2 = (st.2.and (square (decide (512 ≤ (i : ℕ))) (v i) (w.square i))).and
      (if boundary i = true then
        batchNormalize (fun m => st.1 m + (w.square i).sq m) (w.batch (batchIndex i))
      else Check.pass) := by
  by_cases hb : boundary i = true <;> simp [step, hb, Check.and_pass]

/-- `step`'s first component. -/
theorem step_fst_eq (v : Fin 1024 → F) (w : Wit F) (st : (Fin 6 → F) × Check F) (i : Fin 1024) :
    (step v w st i).1 = if boundary i = true then (w.batch (batchIndex i)).ndig
      else fun m => st.1 m + (w.square i).sq m := by
  by_cases hb : boundary i = true <;> simp [step, hb]

/-! ### Needle-count lemmas

Each of these counts a gadget's lookup requests from the gadget's own structure alone,
independent of the witness. -/

/-- The prefix's accumulator, one coefficient later. -/
theorem prefixState_fst_succ (v : Fin 1024 → F) (w : Wit F) (i : Fin 1024) :
    (prefixState v w ((i : ℕ) + 1)).1 = if boundary i = true then (w.batch (batchIndex i)).ndig
      else fun m => (prefixState v w (i : ℕ)).1 m + (w.square i).sq m := by
  rw [prefixState_succ v w i.isLt, step_fst_eq]

/-- Acceptance propagates from a later prefix's check to an earlier one. -/
theorem prefixState_ok_of_le (v : Fin 1024 → F) (w : Wit F) :
    ∀ m, m ≤ 1024 → ∀ n, n ≤ m →
      (prefixState v w m).2.ok = true → (prefixState v w n).2.ok = true := by
  intro m
  induction m with
  | zero =>
      intro _ n hn h
      have hn0 : n = 0 := by omega
      subst hn0; exact h
  | succ m ih =>
      intro hm n hn h
      rcases Nat.lt_or_ge n (m + 1) with hlt | hge
      · have hprev : (prefixState v w m).2.ok = true := by
          rw [prefixState_succ v w (show m < 1024 by omega), step_snd_eq] at h
          exact Check.ok_of_and_left (Check.ok_of_and_left h)
        exact ih (by omega) n (by omega) hprev
      · have hnm : n = m + 1 := by omega
        subst hnm; exact h

/-- Needle membership propagates from an earlier prefix's check to a later one. -/
theorem prefixState_needle_of_le (v : Fin 1024 → F) (w : Wit F) :
    ∀ m, m ≤ 1024 → ∀ n, n ≤ m →
      ∀ x, x ∈ (prefixState v w n).2.needles → x ∈ (prefixState v w m).2.needles := by
  intro m
  induction m with
  | zero =>
      intro _ n hn x hx
      have hn0 : n = 0 := by omega
      subst hn0; exact hx
  | succ m ih =>
      intro hm n hn x hx
      rcases Nat.lt_or_ge n (m + 1) with hlt | hge
      · have hstep : x ∈ (prefixState v w m).2.needles := ih (by omega) n (by omega) x hx
        rw [prefixState_succ v w (show m < 1024 by omega), step_snd_eq]
        exact Check.needles_subset_and_left _ _ _
          (Check.needles_subset_and_left _ _ _ hstep)
      · have hnm : n = m + 1 := by omega
        subst hnm; exact hx

/-- Every prefix's check accepts, given the full run does. -/
theorem prefixState_ok (v : Fin 1024 → F) (w : Wit F) (h : (run v w).ok = true) {n : ℕ}
    (hn : n ≤ 1024) : (prefixState v w n).2.ok = true := by
  apply prefixState_ok_of_le v w 1024 le_rfl n hn
  rw [run_eq] at h
  exact Check.ok_of_and_left h

/-- Every prefix's needles lie in the table, given the full run's do. -/
theorem prefixState_needle (v : Fin 1024 → F) (w : Wit F)
    (hn : Range.InTable 64 (run v w).needles) {n : ℕ} (hn' : n ≤ 1024) :
    Range.InTable 64 (prefixState v w n).2.needles := by
  intro x hx
  apply hn
  rw [run_eq]
  exact Check.needles_subset_and_left _ _ _
    (prefixState_needle_of_le v w 1024 le_rfl n hn' x hx)

/-- Coefficient `i`'s square check accepts. -/
theorem square_ok (v : Fin 1024 → F) (w : Wit F) (h : (run v w).ok = true) (i : Fin 1024) :
    (square (decide (512 ≤ (i : ℕ))) (v i) (w.square i)).ok = true := by
  have hp := prefixState_ok v w h (n := (i : ℕ) + 1) (by omega)
  rw [prefixState_succ v w i.isLt, step_snd_eq] at hp
  exact Check.ok_of_and_right (Check.ok_of_and_left hp)

/-- Coefficient `i`'s square check's needles lie in the table. -/
theorem square_needle (v : Fin 1024 → F) (w : Wit F) (hn : Range.InTable 64 (run v w).needles)
    (i : Fin 1024) :
    Range.InTable 64 (square (decide (512 ≤ (i : ℕ))) (v i) (w.square i)).needles := by
  intro x hx
  apply prefixState_needle v w hn (n := (i : ℕ) + 1) (by omega)
  rw [prefixState_succ v w i.isLt, step_snd_eq]
  exact Check.needles_subset_and_left _ _ _ (Check.needles_subset_and_right _ _ _ hx)

/-- At a batch boundary, that batch's normalization check accepts. -/
theorem batchNormalize_ok (v : Fin 1024 → F) (w : Wit F) (h : (run v w).ok = true) (i : Fin 1024)
    (hb : boundary i = true) :
    (batchNormalize (fun m => (prefixState v w (i : ℕ)).1 m + (w.square i).sq m)
        (w.batch (batchIndex i))).ok = true := by
  have hp := prefixState_ok v w h (n := (i : ℕ) + 1) (by omega)
  rw [prefixState_succ v w i.isLt, step_snd_eq, if_pos hb] at hp
  exact Check.ok_of_and_right hp

/-- At a batch boundary, that batch's normalization check's needles lie in the
table. -/
theorem batchNormalize_needle (v : Fin 1024 → F) (w : Wit F)
    (hn : Range.InTable 64 (run v w).needles) (i : Fin 1024) (hb : boundary i = true) :
    Range.InTable 64 (batchNormalize (fun m => (prefixState v w (i : ℕ)).1 m + (w.square i).sq m)
        (w.batch (batchIndex i))).needles := by
  intro x hx
  apply prefixState_needle v w hn (n := (i : ℕ) + 1) (by omega)
  rw [prefixState_succ v w i.isLt, step_snd_eq, if_pos hb]
  exact Check.needles_subset_and_right _ _ _ hx

/-- The final complement check accepts. -/
theorem leqConst_ok (v : Fin 1024 → F) (w : Wit F) (h : (run v w).ok = true) :
    (leqConst 34034726 (w.batch 16).ndig w.D w.Dcarry).ok = true := by
  rw [run_eq] at h
  exact Check.ok_of_and_right h

/-- The final complement check's needles lie in the table. -/
theorem leqConst_needle (v : Fin 1024 → F) (w : Wit F) (hn : Range.InTable 64 (run v w).needles) :
    Range.InTable 64 (leqConst 34034726 (w.batch 16).ndig w.D w.Dcarry).needles := by
  intro x hx
  apply hn
  rw [run_eq]
  exact Check.needles_subset_and_right _ _ _ hx

/-! ### Reading off `colprod`, `carryVal`, `mag` under natural-number digits -/

omit [DecidableEq F] in
/-- `colprod` commutes with casting each magnitude digit from a natural. -/
theorem colprod_natCast {x : Fin 3 → F} {xNat : Fin 3 → ℕ} (hx : ∀ l, (xNat l : F) = x l)
    (m : ℕ) :
    colprod x m = ((∑ j : Fin 3, ∑ k : Fin 3, if (j : ℕ) + k = m then xNat j * xNat k else 0 : ℕ)
      : F) := by
  unfold colprod
  push_cast
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  split
  · rw [hx j, hx k]
  · simp

/-! ### Reading off `square`'s constraints -/

/-- Coefficient's centering equation. -/
theorem square_centering (hi : Bool) (v : F) (s : SquareWit F) (h : (square hi v s).ok = true) :
    v * v = mag hi s * mag hi s := by
  simp only [square, Check.and_ok, Bool.and_eq_true_iff, decide_eq_true_eq] at h
  exact h.1

/-- Coefficient's per-column schoolbook square equation, uniform over all six
columns (the missing carry-out term at the top column folded into the `if`). -/
theorem square_column (hi : Bool) (v : F) (s : SquareWit F) (h : (square hi v s).ok = true)
    (m : Fin 6) :
    colprod (limbs hi s) (m : ℕ) +
        (if (m : ℕ) = 0 then (0 : F) else carryVal s ⟨(m : ℕ) - 1, by omega⟩) =
      s.sq m + if hlt : (m : ℕ) + 1 < 6 then 64 * carryVal s ⟨(m : ℕ), by omega⟩ else 0 := by
  simp only [square, Check.and_ok, Bool.and_eq_true_iff, Check.all_ok, List.all_eq_true] at h
  have hm := h.2 _ (List.mem_map_of_mem (List.mem_finRange m))
  by_cases hlt5 : (m : ℕ) < 5
  · rw [dif_pos (show (m : ℕ) + 1 < 6 by omega)]
    rw [dif_pos hlt5] at hm
    simpa using hm
  · rw [dif_neg (show ¬ (m : ℕ) + 1 < 6 by omega)]
    rw [dif_neg hlt5] at hm
    simpa using hm

/-- Every magnitude digit is a needle of the coefficient's square check. -/
theorem square_a_mem (hi : Bool) (v : F) (s : SquareWit F) (l : Fin 3) :
    s.a l ∈ (square hi v s).needles := by
  simp only [square, Check.and_needles, List.mem_append]
  exact Or.inl (List.mem_ofFn.mpr ⟨l, rfl⟩)

/-- Every square digit is a needle of the coefficient's square check. -/
theorem square_sq_mem (hi : Bool) (v : F) (s : SquareWit F) (m : Fin 6) :
    s.sq m ∈ (square hi v s).needles := by
  refine Check.needles_subset_and_right _ _ _ ?_
  rw [Check.all_needles, List.mem_flatMap]
  refine ⟨_, List.mem_map_of_mem (List.mem_finRange m), ?_⟩
  by_cases hlt : (m : ℕ) < 5 <;> simp [hlt]

/-- Every square carry limb is a needle of the coefficient's square check. -/
theorem square_carry_mem (hi : Bool) (v : F) (s : SquareWit F) (m : Fin 5) (l : Fin 2) :
    s.carry m l ∈ (square hi v s).needles := by
  refine Check.needles_subset_and_right _ _ _ ?_
  rw [Check.all_needles, List.mem_flatMap]
  refine ⟨_, List.mem_map_of_mem (List.mem_finRange (⟨(m : ℕ), by omega⟩ : Fin 6)), ?_⟩
  have hlt : ((⟨(m : ℕ), by omega⟩ : Fin 6) : ℕ) < 5 := m.isLt
  simp only [hlt, dif_pos, List.mem_cons]
  right
  exact List.mem_ofFn.mpr ⟨l, rfl⟩

/-! ### Reading off `batchNormalize`'s constraints -/

/-- The batch's per-column normalization equation, uniform over all six
columns. -/
theorem batchNormalize_column (col : Fin 6 → F) (b : BatchWit F)
    (h : (batchNormalize col b).ok = true) (m : Fin 6) :
    col m + (if (m : ℕ) = 0 then (0 : F) else b.ncarry ⟨(m : ℕ) - 1, by omega⟩) =
      b.ndig m + if hlt : (m : ℕ) + 1 < 6 then 64 * b.ncarry ⟨(m : ℕ), by omega⟩ else 0 := by
  simp only [batchNormalize, Check.all_ok, List.all_eq_true] at h
  have hm := h _ (List.mem_map_of_mem (List.mem_finRange m))
  by_cases hlt5 : (m : ℕ) < 5
  · rw [dif_pos (show (m : ℕ) + 1 < 6 by omega)]
    rw [dif_pos hlt5] at hm
    simpa using hm
  · rw [dif_neg (show ¬ (m : ℕ) + 1 < 6 by omega)]
    rw [dif_neg hlt5] at hm
    simpa using hm

/-- Every batch digit is a needle of the batch's normalization check. -/
theorem batchNormalize_ndig_mem (col : Fin 6 → F) (b : BatchWit F) (m : Fin 6) :
    b.ndig m ∈ (batchNormalize col b).needles := by
  simp only [batchNormalize]
  rw [Check.all_needles, List.mem_flatMap]
  refine ⟨_, List.mem_map_of_mem (List.mem_finRange m), ?_⟩
  by_cases hlt : (m : ℕ) < 5 <;> simp [hlt]

/-- Every batch carry is a needle of the batch's normalization check. -/
theorem batchNormalize_ncarry_mem (col : Fin 6 → F) (b : BatchWit F) (m : Fin 5) :
    b.ncarry m ∈ (batchNormalize col b).needles := by
  simp only [batchNormalize]
  rw [Check.all_needles, List.mem_flatMap]
  refine ⟨_, List.mem_map_of_mem (List.mem_finRange (⟨(m : ℕ), by omega⟩ : Fin 6)), ?_⟩
  have hlt : ((⟨(m : ℕ), by omega⟩ : Fin 6) : ℕ) < 5 := m.isLt
  simp [hlt]

/-! ### Reading off `leqConst`'s constraints -/

/-- Every complement carry is a Boolean field element. -/
theorem leqConst_bit (C : ℕ) (S D Dc : Fin 6 → F) (h : (leqConst C S D Dc).ok = true) (m : Fin 6) :
    Dc m = 0 ∨ Dc m = 1 := by
  simp only [leqConst, Check.and_ok, Bool.and_eq_true_iff, Check.all_ok, List.all_eq_true] at h
  have hm := h.1 _ (List.mem_map_of_mem (List.mem_finRange m))
  simp only [Bool.and_eq_true_iff, decide_eq_true_eq] at hm
  rcases mul_eq_zero.mp hm.1 with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)

/-- The complement's per-column equation, uniform over all six columns (no
carry-out term is dropped: the top column's carry is separately asserted
zero by `leqConst_top`). -/
theorem leqConst_column (C : ℕ) (S D Dc : Fin 6 → F) (h : (leqConst C S D Dc).ok = true)
    (m : Fin 6) :
    S m + D m + (if (m : ℕ) = 0 then (0 : F) else Dc ⟨(m : ℕ) - 1, by omega⟩) =
      (digit C (m : ℕ) : F) + 64 * Dc m := by
  simp only [leqConst, Check.and_ok, Bool.and_eq_true_iff, Check.all_ok, List.all_eq_true] at h
  have hm := h.1 _ (List.mem_map_of_mem (List.mem_finRange m))
  simp only [Bool.and_eq_true_iff, decide_eq_true_eq] at hm
  exact hm.2

/-- The final carry is zero. -/
theorem leqConst_top (C : ℕ) (S D Dc : Fin 6 → F) (h : (leqConst C S D Dc).ok = true) :
    Dc 5 = 0 := by
  simp only [leqConst, Check.and_ok, Bool.and_eq_true_iff, Check.assert_ok,
    decide_eq_true_eq] at h
  exact h.2

/-- Every complement digit is a needle of the complement check. -/
theorem leqConst_D_mem (C : ℕ) (S D Dc : Fin 6 → F) (m : Fin 6) :
    D m ∈ (leqConst C S D Dc).needles := by
  refine Check.needles_subset_and_left _ _ _ ?_
  rw [Check.all_needles, List.mem_flatMap]
  exact ⟨_, List.mem_map_of_mem (List.mem_finRange m), by simp⟩

/-! ### Exact accumulation -/

/-- Six exact base-`64` column identities telescope: the column-value sum
equals the digit sum. Pure arithmetic, no wraparound (used where columns are
already known exact, unlike `schoolbook_square_lower_bound`). -/
theorem batch_column_sum {col ndig : Fin 6 → ℕ} {carry : Fin 5 → ℕ}
    (h0 : col 0 = ndig 0 + 64 * carry 0)
    (h1 : col 1 + carry 0 = ndig 1 + 64 * carry 1)
    (h2 : col 2 + carry 1 = ndig 2 + 64 * carry 2)
    (h3 : col 3 + carry 2 = ndig 3 + 64 * carry 3)
    (h4 : col 4 + carry 3 = ndig 4 + 64 * carry 4)
    (h5 : col 5 + carry 4 = ndig 5) :
    ∑ m : Fin 6, col m * 64 ^ (m : ℕ) = ∑ m : Fin 6, ndig m * 64 ^ (m : ℕ) := by
  simp only [Fin.sum_univ_six]
  norm_num
  omega

/-- The fold's second component, in natural numbers: matches
`(prefixState v w n).1` once `sqNat`/`ndigNat` are cast-compatible with the
committed square and batch digits (`colValNat_inv`). -/
def colValNat (sqNat : Fin 1024 → Fin 6 → ℕ) (ndigNat : Fin 17 → Fin 6 → ℕ) :
    ℕ → Fin 6 → ℕ
  | 0 => fun _ => 0
  | n + 1 => fun m =>
      if h : n < 1024 then
        if boundary ⟨n, h⟩ = true then ndigNat (batchIndex ⟨n, h⟩) m
        else colValNat sqNat ndigNat n m + sqNat ⟨n, h⟩ m
      else colValNat sqNat ndigNat n m

/-- The shadow accumulator matches the real one, and never exceeds a previous
batch digit (if any) plus up to `63` more square digits since the last
reset — enough to keep every batch column below the characteristic. -/
theorem colValNat_inv (v : Fin 1024 → F) (w : Wit F)
    (sqNat : Fin 1024 → Fin 6 → ℕ) (ndigNat : Fin 17 → Fin 6 → ℕ)
    (hsq : ∀ i m, (sqNat i m : F) = (w.square i).sq m) (hsq_lt : ∀ i m, sqNat i m < 64)
    (hndig : ∀ b m, (ndigNat b m : F) = (w.batch b).ndig m) (hndig_lt : ∀ b m, ndigNat b m < 64) :
    ∀ n ≤ 1024, ∀ m, colValNat sqNat ndigNat n m ≤ 63 + 63 * (n % 63) ∧
      (colValNat sqNat ndigNat n m : F) = (prefixState v w n).1 m := by
  intro n
  induction n with
  | zero => intro _ m; refine ⟨by simp [colValNat], ?_⟩; simp [colValNat]
  | succ n ih =>
    intro hn1 m
    have hn : n < 1024 := by omega
    obtain ⟨ihb, ihc⟩ := ih (by omega) m
    rw [prefixState_fst_succ v w ⟨n, hn⟩]
    have hunfold : colValNat sqNat ndigNat (n + 1) =
        fun m => if h : n < 1024 then
          (if boundary ⟨n, h⟩ = true then ndigNat (batchIndex ⟨n, h⟩) m
            else colValNat sqNat ndigNat n m + sqNat ⟨n, h⟩ m)
          else colValNat sqNat ndigNat n m := rfl
    rw [hunfold]
    simp only [dif_pos hn]
    by_cases hb : boundary ⟨n, hn⟩ = true
    · simp only [if_pos hb]
      refine ⟨?_, hndig _ m⟩
      have := hndig_lt (batchIndex ⟨n, hn⟩) m
      omega
    · simp only [if_neg hb]
      have hbfalse : ¬(((n : ℕ) + 1) % 63 = 0 ∨ (n : ℕ) + 1 = 1024) := by
        intro hc
        exact hb (by simp only [boundary]; exact decide_eq_true hc)
      have hmod : ((n : ℕ) + 1) % 63 = n % 63 + 1 := by omega
      refine ⟨by rw [hmod]; have := hsq_lt ⟨n, hn⟩ m; omega, by push_cast; rw [ihc, hsq]⟩

/-! ### The backward argument -/

omit [DecidableEq F] in
/-- Read a uniform six-column identity (the shape `square_column`,
`batchNormalize_column` share, after the two-limb carry-out term at column
`5` is folded into an `if`) at each concrete column, matching the six named
per-column hypotheses `batch_column_sum` and `schoolbook_square_lower_bound`
need. -/
theorem sixColumn_explicit {col ndig : Fin 6 → F} {carry : Fin 5 → F}
    (huniform : ∀ m : Fin 6, col m + (if (m : ℕ) = 0 then (0 : F) else carry ⟨(m : ℕ) - 1, by omega⟩) =
      ndig m + if hlt : (m : ℕ) + 1 < 6 then 64 * carry ⟨(m : ℕ), by omega⟩ else 0) :
    col 0 = ndig 0 + 64 * carry 0 ∧
    col 1 + carry 0 = ndig 1 + 64 * carry 1 ∧
    col 2 + carry 1 = ndig 2 + 64 * carry 2 ∧
    col 3 + carry 2 = ndig 3 + 64 * carry 3 ∧
    col 4 + carry 3 = ndig 4 + 64 * carry 4 ∧
    col 5 + carry 4 = ndig 5 :=
  ⟨by simpa using huniform 0, by simpa using huniform 1, by simpa using huniform 2,
    by simpa using huniform 3, by simpa using huniform 4, by simpa using huniform 5⟩

/-- **Square lower bound**. The natural square a coefficient's committed digits represent is at
least its magnitude squared, wiring `schoolbook_square_lower_bound` to `square_column` via chosen
natural witnesses of the coefficient's in-table digits. Needs the represented total already known
at most `β²` (`ht`), established afterward from `leqConst_bound`; this is the coefficient-local
part of `sound`'s backward argument. -/
theorem square_lower_bound [CharP F 12289] {hi : Bool} {v : F} {s : SquareWit F}
    (h : (square hi v s).ok = true)
    {x : Fin 3 → ℕ} (hx : ∀ l, (x l : F) = limbs hi s l) (hx_lt : ∀ l, x l < 64)
    {sq : Fin 6 → ℕ} (hsq : ∀ m, (sq m : F) = s.sq m) (hsq_lt : ∀ m, sq m < 64)
    {carry : Fin 5 → ℕ} (hcarry : ∀ m, (carry m : F) = carryVal s m) (hcarry_lt : ∀ m, carry m < 4096)
    (ht : ∑ m : Fin 6, sq m * 64 ^ (m : ℕ) ≤ 34034726) :
    (x 0 + 64 * x 1 + 4096 * x 2) ^ 2 ≤ ∑ m : Fin 6, sq m * 64 ^ (m : ℕ) := by
  have hf0 := square_column hi v s h 0
  have hf1 := square_column hi v s h 1
  have hf2 := square_column hi v s h 2
  have hf3 := square_column hi v s h 3
  have hf4 := square_column hi v s h 4
  have hf5 := square_column hi v s h 5
  simp [colprod_natCast hx, Fin.sum_univ_three] at hf0 hf1 hf2 hf3 hf4 hf5
  have hm0 : Nat.ModEq 12289 (x 0 * x 0) (sq 0 + 64 * carry 0) := by
    apply (CharP.natCast_eq_natCast (R := F) (p := 12289)).mp
    push_cast
    simp only [hsq, hcarry]
    linear_combination hf0
  have hm1 : Nat.ModEq 12289 (2 * x 0 * x 1 + carry 0) (sq 1 + 64 * carry 1) := by
    apply (CharP.natCast_eq_natCast (R := F) (p := 12289)).mp
    push_cast
    simp only [hsq, hcarry]
    linear_combination hf1
  have hm2 : Nat.ModEq 12289 (2 * x 0 * x 2 + x 1 * x 1 + carry 1) (sq 2 + 64 * carry 2) := by
    apply (CharP.natCast_eq_natCast (R := F) (p := 12289)).mp
    push_cast
    simp only [hsq, hcarry]
    linear_combination hf2
  have hm3 : Nat.ModEq 12289 (2 * x 1 * x 2 + carry 2) (sq 3 + 64 * carry 3) := by
    apply (CharP.natCast_eq_natCast (R := F) (p := 12289)).mp
    push_cast
    simp only [hsq, hcarry]
    linear_combination hf3
  have hm4 : Nat.ModEq 12289 (x 2 * x 2 + carry 3) (sq 4 + 64 * carry 4) := by
    apply (CharP.natCast_eq_natCast (R := F) (p := 12289)).mp
    push_cast
    simp only [hsq, hcarry]
    linear_combination hf4
  have hm5 : Nat.ModEq 12289 (sq 5) (carry 4) := by
    apply (CharP.natCast_eq_natCast (R := F) (p := 12289)).mp
    simp only [hsq, hcarry]
    exact hf5.symm
  have hschool := schoolbook_square_lower_bound
    (x0 := x 0) (x1 := x 1) (x2 := x 2)
    (d0 := sq 0) (d1 := sq 1) (d2 := sq 2) (d3 := sq 3) (d4 := sq 4) (d5 := sq 5)
    (C0 := carry 0) (C1 := carry 1) (C2 := carry 2) (C3 := carry 3) (C4 := carry 4)
    (hx_lt 0) (hx_lt 1) (hx_lt 2)
    (hsq_lt 0) (hsq_lt 1) (hsq_lt 2) (hsq_lt 3) (hsq_lt 4) (hsq_lt 5)
    (hcarry_lt 0) (hcarry_lt 1) (hcarry_lt 2) (hcarry_lt 3) (hcarry_lt 4)
    hm0.symm hm1.symm hm2.symm hm3.symm hm4.symm hm5
    (by
      have h6 := ht
      simp [Fin.sum_univ_six] at h6
      omega)
  have hgoal : ∑ m : Fin 6, sq m * 64 ^ (m : ℕ) =
      sq 0 + 64 * sq 1 + 64 ^ 2 * sq 2 + 64 ^ 3 * sq 3 + 64 ^ 4 * sq 4 + 64 ^ 5 * sq 5 := by
    simp [Fin.sum_univ_six]
    ring
  rw [hgoal]
  exact hschool

/-- **Exact accumulation.** The last batch's committed digits, weighted by their base-`64` place
value, equal the exact sum over all `1024` coefficients of their square digits' weighted sum: the
batch-boundary jump preserves the running total (`batch_column_sum`), so summing across the `17`
batches telescopes to the grand total. -/
theorem colValNat_sum [CharP F 12289] (v : Fin 1024 → F) (w : Wit F) (h : (run v w).ok = true)
    {sqNat : Fin 1024 → Fin 6 → ℕ} (hsq : ∀ i m, (sqNat i m : F) = (w.square i).sq m)
    (hsq_lt : ∀ i m, sqNat i m < 64)
    {ndigNat : Fin 17 → Fin 6 → ℕ} (hndig : ∀ b m, (ndigNat b m : F) = (w.batch b).ndig m)
    (hndig_lt : ∀ b m, ndigNat b m < 64)
    {ncarryNat : Fin 17 → Fin 5 → ℕ}
    (hncarry : ∀ b m, (ncarryNat b m : F) = (w.batch b).ncarry m) (hncarry_lt : ∀ b m, ncarryNat b m < 64) :
    ∑ m : Fin 6, ndigNat 16 m * 64 ^ (m : ℕ) =
      ∑ i : Fin 1024, ∑ m : Fin 6, sqNat i m * 64 ^ (m : ℕ) := by
  have hinv := colValNat_inv v w sqNat ndigNat hsq hsq_lt hndig hndig_lt
  let tNat' : ℕ → ℕ := fun k => if h : k < 1024 then ∑ m : Fin 6, sqNat ⟨k, h⟩ m * 64 ^ (m : ℕ) else 0
  have key : ∀ n ≤ 1024, ∑ m : Fin 6, colValNat sqNat ndigNat n m * 64 ^ (m : ℕ) =
      ∑ k ∈ Finset.range n, tNat' k := by
    intro n
    induction n with
    | zero => intro _; simp [colValNat]
    | succ n ih =>
      intro hn1
      have hn : n < 1024 := by omega
      have ihh := ih (by omega)
      have htn : tNat' n = ∑ m : Fin 6, sqNat ⟨n, hn⟩ m * 64 ^ (m : ℕ) := by
        simp only [tNat', dif_pos hn]
      by_cases hb : boundary ⟨n, hn⟩ = true
      · -- boundary: `colValNat` jumps to the batch's committed digits.
        have hstep : colValNat sqNat ndigNat (n + 1) = ndigNat (batchIndex ⟨n, hn⟩) := by
          funext m
          show (if h' : n < 1024 then
            (if boundary ⟨n, h'⟩ = true then ndigNat (batchIndex ⟨n, h'⟩) m
              else colValNat sqNat ndigNat n m + sqNat ⟨n, h'⟩ m)
            else colValNat sqNat ndigNat n m) = ndigNat (batchIndex ⟨n, hn⟩) m
          rw [dif_pos hn, if_pos hb]
        rw [hstep, Finset.sum_range_succ, ← ihh, htn]
        set b := batchIndex ⟨n, hn⟩ with hbdef
        set col : Fin 6 → ℕ := fun m => colValNat sqNat ndigNat n m + sqNat ⟨n, hn⟩ m with hcoldef
        have hcolLt : ∀ m, col m ≤ 4032 := by
          intro m
          have h1 := (hinv n (by omega) m).1
          have h2 := hsq_lt ⟨n, hn⟩ m
          have hmod : n % 63 ≤ 62 := by omega
          simp only [hcoldef]
          omega
        have hcolCast : ∀ m, (col m : F) =
            (prefixState v w n).1 m + (w.square ⟨n, hn⟩).sq m := by
          intro m
          simp only [hcoldef]
          push_cast
          rw [(hinv n (by omega) m).2, hsq]
        have hok := batchNormalize_ok v w h ⟨n, hn⟩ hb
        obtain ⟨hf0, hf1, hf2, hf3, hf4, hf5⟩ := sixColumn_explicit (batchNormalize_column _ _ hok)
        have hn0 : col 0 = ndigNat b 0 + 64 * ncarryNat b 0 := by
          apply IntLift.natCast_inj_of_lt (K := F) (p := 12289)
            (by have := hcolLt 0; omega) (by have := hndig_lt b 0; have := hncarry_lt b 0; omega)
          rw [hcolCast]
          push_cast
          simp only [← hndig, ← hncarry] at hf0
          linear_combination hf0
        have hn1 : col 1 + ncarryNat b 0 = ndigNat b 1 + 64 * ncarryNat b 1 := by
          apply IntLift.natCast_inj_of_lt (K := F) (p := 12289)
            (by have := hcolLt 1; have := hncarry_lt b 0; omega)
            (by have := hndig_lt b 1; have := hncarry_lt b 1; omega)
          push_cast
          rw [hcolCast]
          simp only [← hndig, ← hncarry] at hf1
          linear_combination hf1
        have hn2 : col 2 + ncarryNat b 1 = ndigNat b 2 + 64 * ncarryNat b 2 := by
          apply IntLift.natCast_inj_of_lt (K := F) (p := 12289)
            (by have := hcolLt 2; have := hncarry_lt b 1; omega)
            (by have := hndig_lt b 2; have := hncarry_lt b 2; omega)
          push_cast
          rw [hcolCast]
          simp only [← hndig, ← hncarry] at hf2
          linear_combination hf2
        have hn3 : col 3 + ncarryNat b 2 = ndigNat b 3 + 64 * ncarryNat b 3 := by
          apply IntLift.natCast_inj_of_lt (K := F) (p := 12289)
            (by have := hcolLt 3; have := hncarry_lt b 2; omega)
            (by have := hndig_lt b 3; have := hncarry_lt b 3; omega)
          push_cast
          rw [hcolCast]
          simp only [← hndig, ← hncarry] at hf3
          linear_combination hf3
        have hn4 : col 4 + ncarryNat b 3 = ndigNat b 4 + 64 * ncarryNat b 4 := by
          apply IntLift.natCast_inj_of_lt (K := F) (p := 12289)
            (by have := hcolLt 4; have := hncarry_lt b 3; omega)
            (by have := hndig_lt b 4; have := hncarry_lt b 4; omega)
          push_cast
          rw [hcolCast]
          simp only [← hndig, ← hncarry] at hf4
          linear_combination hf4
        have hn5 : col 5 + ncarryNat b 4 = ndigNat b 5 := by
          apply IntLift.natCast_inj_of_lt (K := F) (p := 12289)
            (by have := hcolLt 5; have := hncarry_lt b 4; omega)
            (by have := hndig_lt b 5; omega)
          push_cast
          rw [hcolCast]
          simp only [← hndig, ← hncarry] at hf5
          linear_combination hf5
        have hkey := (batch_column_sum (col := col) (ndig := ndigNat b) (carry := ncarryNat b)
          hn0 hn1 hn2 hn3 hn4 hn5).symm
        rw [hkey]
        simp only [hcoldef]
        simp only [add_mul]
        rw [Finset.sum_add_distrib]
      · have hstep : colValNat sqNat ndigNat (n + 1) =
            fun m => colValNat sqNat ndigNat n m + sqNat ⟨n, hn⟩ m := by
          funext m
          show (if h' : n < 1024 then
            (if boundary ⟨n, h'⟩ = true then ndigNat (batchIndex ⟨n, h'⟩) m
              else colValNat sqNat ndigNat n m + sqNat ⟨n, h'⟩ m)
            else colValNat sqNat ndigNat n m) = colValNat sqNat ndigNat n m + sqNat ⟨n, hn⟩ m
          rw [dif_pos hn, if_neg hb]
        rw [Finset.sum_range_succ, ← ihh, htn, hstep]
        simp only [add_mul]
        rw [Finset.sum_add_distrib]
  have h1024 := key 1024 le_rfl
  have hlast : colValNat sqNat ndigNat 1024 = ndigNat 16 := by
    funext m
    have hlt : (1023 : ℕ) < 1024 := by omega
    have hb : boundary ⟨1023, hlt⟩ = true := by
      simp [boundary]
    have hidx : batchIndex ⟨1023, hlt⟩ = 16 := by
      apply Fin.ext
      simp only [batchIndex]
      decide
    show (if h' : 1023 < 1024 then
      (if boundary ⟨1023, h'⟩ = true then ndigNat (batchIndex ⟨1023, h'⟩) m
        else colValNat sqNat ndigNat 1023 m + sqNat ⟨1023, h'⟩ m)
      else colValNat sqNat ndigNat 1023 m) = ndigNat 16 m
    rw [dif_pos hlt, if_pos hb, hidx]
  rw [hlast] at h1024
  rw [h1024]
  rw [Finset.sum_range tNat']
  apply Finset.sum_congr rfl
  intro i _
  simp only [tNat', dif_pos i.isLt]

/-- **Exact accumulation of the complement.** Given the complement's six
column identities and the final carry zero (`leqConst_top`, already used to
eliminate column `5`'s carry-out term), the represented digits sum to at most
the public constant. -/
theorem leqConst_bound {S D : Fin 6 → ℕ} {Dc : Fin 5 → ℕ}
    (h0 : S 0 + D 0 = digit 34034726 0 + 64 * Dc 0)
    (h1 : S 1 + D 1 + Dc 0 = digit 34034726 1 + 64 * Dc 1)
    (h2 : S 2 + D 2 + Dc 1 = digit 34034726 2 + 64 * Dc 2)
    (h3 : S 3 + D 3 + Dc 2 = digit 34034726 3 + 64 * Dc 3)
    (h4 : S 4 + D 4 + Dc 3 = digit 34034726 4 + 64 * Dc 4)
    (h5 : S 5 + D 5 + Dc 4 = digit 34034726 5) :
    ∑ m : Fin 6, S m * 64 ^ (m : ℕ) ≤ 34034726 := by
  have hkey := batch_column_sum (col := fun m => S m + D m) (ndig := fun m => digit 34034726 m)
    (carry := Dc) h0 h1 h2 h3 h4 h5
  have hdig : ∑ m : Fin 6, digit 34034726 m * 64 ^ (m : ℕ) = 34034726 := by
    simp [digit, Fin.sum_univ_six]
  have hle : ∑ m : Fin 6, S m * 64 ^ (m : ℕ) ≤ ∑ m : Fin 6, (S m + D m) * 64 ^ (m : ℕ) := by
    apply Finset.sum_le_sum
    intro i _
    rw [add_mul]
    exact Nat.le_add_right _ _
  rw [hkey, hdig] at hle
  exact hle

/-- Every batch has a boundary coefficient: the last coefficient the batch
normalizes, whose acceptance carries the batch's own lookup membership. -/
theorem exists_boundary_witness (b : Fin 17) :
    ∃ i : Fin 1024, boundary i = true ∧ batchIndex i = b := by
  rcases lt_or_ge (b : ℕ) 16 with hb | hb
  · refine ⟨⟨63 * (b : ℕ) + 62, by omega⟩, ?_, ?_⟩
    · simp only [boundary, decide_eq_true_eq]
      omega
    · apply Fin.ext
      simp only [batchIndex]
      omega
  · have hb16 : (b : ℕ) = 16 := by omega
    refine ⟨⟨1023, by omega⟩, ?_, ?_⟩
    · simp [boundary]
    · apply Fin.ext
      simp only [batchIndex]
      omega

/-- A natural whose square is at most `β²` lies at most half the
characteristic `12289`, enough for `GordieHowe.Centered.exists_cast_centered_eq`'s
exact centering. -/
theorem magNat_le_half (magNat : ℕ) (h : magNat ^ 2 ≤ 34034726) : magNat ≤ 6144 := by
  by_contra hcon
  push_neg at hcon
  have h1 : 6145 ≤ magNat := hcon
  have h2 : 6145 * 6145 ≤ magNat * magNat := Nat.mul_le_mul h1 h1
  have h3 : magNat * magNat ≤ 34034726 := by
    have hp : magNat ^ 2 = magNat * magNat := sq magNat
    omega
  omega

/-- **Soundness of the native norm.** If every lookup request lies in `[0, 64)`
(`hn`, the conclusion of the range argument) and the gadget accepts, the wires are
casts of residues whose centered squared norm is at most `β²`; and every `s₂`
coefficient's two-digit magnitude is exactly its centered magnitude, below `64²`.
`CharP F 12289` is a fact about the field. -/
theorem sound [CharP F 12289] {v : Fin 1024 → F} {w : Wit F}
    (hn : Range.InTable 64 (run v w).needles) (h : (run v w).ok = true) :
    ∃ vals : Fin 1024 → ℕ, EmulatedNorm.Lifted 12289 34034726 v vals ∧
      ∀ i : Fin 1024, 512 ≤ (i : ℕ) →
        ∃ a : ℕ, a < 64 ^ 2 ∧ (a : F) = mag true (w.square i) ∧
          (LatticeCrypto.centeredRepr (vals i : ZMod 12289)).natAbs = a := by
  -- Coefficient witnesses: magnitude digits, square digits, and the two-limb
  -- column carry, each the natural in-table value of a committed wire.
  have hsq_ex : ∀ i : Fin 1024, ∀ m : Fin 6, Range.IsNatBelow 64 ((w.square i).sq m) := by
    intro i m
    exact square_needle v w hn i _ (square_sq_mem _ _ (w.square i) m)
  choose sqNat hsqNat_lt hsqNat_cast using hsq_ex
  have hxRaw_ex : ∀ i : Fin 1024, ∀ l : Fin 3, Range.IsNatBelow 64 ((w.square i).a l) := by
    intro i l
    exact square_needle v w hn i _ (square_a_mem _ _ (w.square i) l)
  choose xRaw hxRaw_lt hxRaw_cast using hxRaw_ex
  set hiB : Fin 1024 → Bool := fun i => decide (512 ≤ (i : ℕ)) with hiBdef
  set x : Fin 1024 → Fin 3 → ℕ := fun i l => if hiB i = true ∧ (l : ℕ) = 2 then 0 else xRaw i l
    with hxdef
  have hx_cast : ∀ i l, (x i l : F) = limbs (hiB i) (w.square i) l := by
    intro i l
    simp only [hxdef, limbs]
    split
    · simp
    · exact hxRaw_cast i l
  have hx_lt : ∀ i l, x i l < 64 := by
    intro i l
    simp only [hxdef]
    split
    · norm_num
    · exact hxRaw_lt i l
  have hx2_zero : ∀ i, hiB i = true → x i 2 = 0 := by
    intro i hi
    simp [hxdef, hi]
  have hcarryRaw_ex : ∀ i : Fin 1024, ∀ m : Fin 5, ∀ l : Fin 2,
      Range.IsNatBelow 64 ((w.square i).carry m l) := by
    intro i m l
    exact square_needle v w hn i _ (square_carry_mem _ _ (w.square i) m l)
  choose carryRaw hcarryRaw_lt hcarryRaw_cast using hcarryRaw_ex
  set carry : Fin 1024 → Fin 5 → ℕ := fun i m => carryRaw i m 0 + 64 * carryRaw i m 1 with hcarrydef
  have hcarry_cast : ∀ i m, (carry i m : F) = carryVal (w.square i) m := by
    intro i m
    have hr := Range.reconstruct_natCast (K := F) (k := 2) (B := 64) (carryRaw i m)
      ((w.square i).carry m) (hcarryRaw_cast i m)
    simp only [carryVal]
    rw [hr]
    simp only [hcarrydef]
    push_cast
    simp [Fin.sum_univ_two]
    ring
  have hcarry_lt : ∀ i m, carry i m < 4096 := by
    intro i m
    have h0 := hcarryRaw_lt i m 0
    have h1 := hcarryRaw_lt i m 1
    simp only [hcarrydef]
    omega
  -- Batch witnesses: the committed digits and carry of every batch, read off
  -- at the coefficient ending it.
  have hndig_ex : ∀ b : Fin 17, ∀ m : Fin 6, Range.IsNatBelow 64 ((w.batch b).ndig m) := by
    intro b m
    obtain ⟨i, hbi, hbidx⟩ := exists_boundary_witness b
    have hbn := batchNormalize_needle v w hn i hbi
    rw [hbidx] at hbn
    exact hbn _ (batchNormalize_ndig_mem _ (w.batch b) m)
  choose ndigNat hndigNat_lt hndigNat_cast using hndig_ex
  have hncarry_ex : ∀ b : Fin 17, ∀ m : Fin 5, Range.IsNatBelow 64 ((w.batch b).ncarry m) := by
    intro b m
    obtain ⟨i, hbi, hbidx⟩ := exists_boundary_witness b
    have hbn := batchNormalize_needle v w hn i hbi
    rw [hbidx] at hbn
    exact hbn _ (batchNormalize_ncarry_mem _ (w.batch b) m)
  choose ncarryNat hncarryNat_lt hncarryNat_cast using hncarry_ex
  -- The final complement's committed digits and Boolean carries.
  have hD_ex : ∀ m : Fin 6, Range.IsNatBelow 64 (w.D m) := by
    intro m
    exact leqConst_needle v w hn _ (leqConst_D_mem _ _ w.D w.Dcarry m)
  choose DNat hDNat_lt hDNat_cast using hD_ex
  have hDc_bit : ∀ m : Fin 6, w.Dcarry m = 0 ∨ w.Dcarry m = 1 :=
    leqConst_bit 34034726 _ w.D w.Dcarry (leqConst_ok v w h)
  have hDc5 : w.Dcarry 5 = 0 := leqConst_top 34034726 _ w.D w.Dcarry (leqConst_ok v w h)
  set DcNat : Fin 5 → ℕ := fun m => if w.Dcarry ⟨(m : ℕ), by omega⟩ = 0 then 0 else 1 with hDcdef
  have hDcNat_cast : ∀ m : Fin 5, (DcNat m : F) = w.Dcarry ⟨(m : ℕ), by omega⟩ := by
    intro m
    simp only [hDcdef]
    rcases hDc_bit ⟨(m : ℕ), by omega⟩ with h0 | h1
    · simp [h0]
    · simp [h1]
  have hDcNat_lt : ∀ m : Fin 5, DcNat m < 2 := by
    intro m
    simp only [hDcdef]
    split <;> omega
  have hLC := leqConst_ok v w h
  have hLcol : ∀ m : Fin 6, (w.batch 16).ndig m + w.D m +
      (if (m : ℕ) = 0 then (0 : F) else w.Dcarry ⟨(m : ℕ) - 1, by omega⟩) =
      (digit 34034726 (m : ℕ) : F) + 64 * w.Dcarry m :=
    leqConst_column 34034726 (w.batch 16).ndig w.D w.Dcarry hLC
  have hl0 := hLcol 0
  have hl1 := hLcol 1
  have hl2 := hLcol 2
  have hl3 := hLcol 3
  have hl4 := hLcol 4
  have hl5 := hLcol 5
  simp only [hDc5, mul_zero, add_zero] at hl5
  have hn0 : ndigNat 16 0 + DNat 0 = digit 34034726 0 + 64 * DcNat 0 := by
    apply IntLift.natCast_inj_of_lt (K := F) (p := 12289)
      (by have := hndigNat_lt 16 0; have := hDNat_lt 0; omega)
      (by have hd : digit 34034726 0 < 64 := by decide
          have := hDcNat_lt 0
          omega)
    push_cast
    rw [hndigNat_cast, hDNat_cast, hDcNat_cast]
    simpa using hl0
  have hn1 : ndigNat 16 1 + DNat 1 + DcNat 0 = digit 34034726 1 + 64 * DcNat 1 := by
    apply IntLift.natCast_inj_of_lt (K := F) (p := 12289)
      (by have := hndigNat_lt 16 1; have := hDNat_lt 1; have := hDcNat_lt 0; omega)
      (by have hd : digit 34034726 1 < 64 := by decide
          have := hDcNat_lt 1
          omega)
    push_cast
    simp only [hndigNat_cast, hDNat_cast, hDcNat_cast]
    simpa using hl1
  have hn2 : ndigNat 16 2 + DNat 2 + DcNat 1 = digit 34034726 2 + 64 * DcNat 2 := by
    apply IntLift.natCast_inj_of_lt (K := F) (p := 12289)
      (by have := hndigNat_lt 16 2; have := hDNat_lt 2; have := hDcNat_lt 1; omega)
      (by have hd : digit 34034726 2 < 64 := by decide
          have := hDcNat_lt 2
          omega)
    push_cast
    simp only [hndigNat_cast, hDNat_cast, hDcNat_cast]
    simpa using hl2
  have hn3 : ndigNat 16 3 + DNat 3 + DcNat 2 = digit 34034726 3 + 64 * DcNat 3 := by
    apply IntLift.natCast_inj_of_lt (K := F) (p := 12289)
      (by have := hndigNat_lt 16 3; have := hDNat_lt 3; have := hDcNat_lt 2; omega)
      (by have hd : digit 34034726 3 < 64 := by decide
          have := hDcNat_lt 3
          omega)
    push_cast
    simp only [hndigNat_cast, hDNat_cast, hDcNat_cast]
    simpa using hl3
  have hn4 : ndigNat 16 4 + DNat 4 + DcNat 3 = digit 34034726 4 + 64 * DcNat 4 := by
    apply IntLift.natCast_inj_of_lt (K := F) (p := 12289)
      (by have := hndigNat_lt 16 4; have := hDNat_lt 4; have := hDcNat_lt 3; omega)
      (by have hd : digit 34034726 4 < 64 := by decide
          have := hDcNat_lt 4
          omega)
    push_cast
    simp only [hndigNat_cast, hDNat_cast, hDcNat_cast]
    simpa using hl4
  have hn5 : ndigNat 16 5 + DNat 5 + DcNat 4 = digit 34034726 5 := by
    apply IntLift.natCast_inj_of_lt (K := F) (p := 12289)
      (by have := hndigNat_lt 16 5; have := hDNat_lt 5; have := hDcNat_lt 4; omega)
      (by have hd : digit 34034726 5 < 64 := by decide
          omega)
    push_cast
    simp only [hndigNat_cast, hDNat_cast, hDcNat_cast]
    simpa using hl5
  have hbound := leqConst_bound (S := ndigNat 16) (D := DNat) (Dc := DcNat) hn0 hn1 hn2 hn3 hn4 hn5
  -- Exact accumulation: the represented squares sum to at most `β²`.
  have hsum_eq := colValNat_sum v w h (sqNat := sqNat) (hsq := hsqNat_cast) (hsq_lt := hsqNat_lt)
    (ndigNat := ndigNat) (hndig := hndigNat_cast) (hndig_lt := hndigNat_lt)
    (ncarryNat := ncarryNat) (hncarry := hncarryNat_cast) (hncarry_lt := hncarryNat_lt)
  have htotal : ∑ i : Fin 1024, ∑ m : Fin 6, sqNat i m * 64 ^ (m : ℕ) ≤ 34034726 := by
    rw [← hsum_eq]; exact hbound
  -- Reading each coefficient's columns from the top: the represented square
  -- is at least its magnitude squared, and the magnitude is at most half the
  -- characteristic, so centering is exact.
  have key : ∀ i : Fin 1024, ∃ magNat : ℕ, magNat ≤ 6144 ∧
      (magNat : F) = mag (hiB i) (w.square i) ∧ (hiB i = true → magNat < 64 ^ 2) ∧
      magNat ^ 2 ≤ ∑ m : Fin 6, sqNat i m * 64 ^ (m : ℕ) := by
    intro i
    have hti : ∑ m : Fin 6, sqNat i m * 64 ^ (m : ℕ) ≤ 34034726 := by
      calc ∑ m, sqNat i m * 64 ^ (m : ℕ)
          ≤ ∑ j : Fin 1024, ∑ m, sqNat j m * 64 ^ (m : ℕ) :=
            Finset.single_le_sum (f := fun j => ∑ m : Fin 6, sqNat j m * 64 ^ (m : ℕ))
              (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
        _ ≤ 34034726 := htotal
    have hsq_ok := square_ok v w h i
    have hsq_lb := square_lower_bound (hi := hiB i) (v := v i) (s := w.square i) hsq_ok
      (x := x i) (hx_cast i) (hx_lt i) (sq := sqNat i) (hsqNat_cast i) (hsqNat_lt i)
      (carry := carry i) (hcarry_cast i) (hcarry_lt i) hti
    have hmagcast : ((x i 0 + 64 * x i 1 + 4096 * x i 2 : ℕ) : F) = mag (hiB i) (w.square i) := by
      have hr := Range.reconstruct_natCast (K := F) (k := 3) (B := 64) (x i)
        (limbs (hiB i) (w.square i)) (hx_cast i)
      simp only [mag]
      rw [hr]
      simp [Fin.sum_univ_three]
      ring
    refine ⟨x i 0 + 64 * x i 1 + 4096 * x i 2, ?_, hmagcast, ?_, hsq_lb⟩
    · apply magNat_le_half
      omega
    · intro hi512
      rw [hx2_zero i hi512]
      have := hx_lt i 0
      have := hx_lt i 1
      omega
  choose magNat hmagNat_le hmagNat_cast hmagNat_lt512 hmagNat_sq using key
  -- Centering: extract the residues from the sign choice.
  have hcenter : ∀ i : Fin 1024, ∃ vali : ℕ, vali ≤ 12289 ∧ (vali : F) = v i ∧
      (LatticeCrypto.centeredRepr (vali : ZMod 12289)).natAbs = magNat i := by
    intro i
    have hcentering := square_centering (hiB i) (v i) (w.square i) (square_ok v w h i)
    rw [← hmagNat_cast i] at hcentering
    have hv : v i = (magNat i : F) ∨ v i = -(magNat i : F) :=
      mul_self_eq_mul_self_iff.mp hcentering
    have hmagle : (magNat i : ℤ) ≤ (12289 : ℤ) / 2 := by
      have := hmagNat_le i
      omega
    exact Centered.exists_cast_centered_eq (q := 12289) hmagle hv
  choose vals hvals_le hvals_cast hvals_natAbs using hcenter
  refine ⟨vals, ⟨hvals_le, hvals_cast, ?_⟩, ?_⟩
  · calc ∑ i, (LatticeCrypto.centeredRepr (vals i : ZMod 12289)).natAbs ^ 2
        = ∑ i, magNat i ^ 2 := by
          apply Finset.sum_congr rfl; intro i _; rw [hvals_natAbs i]
      _ ≤ ∑ i, ∑ m : Fin 6, sqNat i m * 64 ^ (m : ℕ) := by
          apply Finset.sum_le_sum; intro i _; exact hmagNat_sq i
      _ ≤ 34034726 := htotal
  · intro i h512
    have hhi : hiB i = true := by simp only [hiB]; exact decide_eq_true h512
    exact ⟨magNat i, hmagNat_lt512 i hhi, hhi ▸ hmagNat_cast i, hvals_natAbs i⟩

/-! ### Honest advice: the ripple-carry digit chain (completeness)

`sixDigit`/`sixCarry` are the honest six base-`64` digits and five carries of any six raw column
values, computed by ordinary ripple-carry addition. They satisfy every column identity `square` and
`batchNormalize` assert whenever the raw columns stay under a bound keeping every carry below `C`,
and the last digit is exact once the whole represented value is under `64 ^ 6`. Pure arithmetic, no
field or gadget involved; both `square`'s two-limb carries and `batchNormalize`'s one-limb carries
instantiate the same chain at different `C`. -/

-- spec-side
def sixDigit (col : Fin 6 → ℕ) (m : Fin 6) : ℕ :=
  let c0 := col 0 / 64
  let c1 := (col 1 + c0) / 64
  let c2 := (col 2 + c1) / 64
  let c3 := (col 3 + c2) / 64
  let c4 := (col 4 + c3) / 64
  if (m : ℕ) = 0 then col 0 % 64
  else if (m : ℕ) = 1 then (col 1 + c0) % 64
  else if (m : ℕ) = 2 then (col 2 + c1) % 64
  else if (m : ℕ) = 3 then (col 3 + c2) % 64
  else if (m : ℕ) = 4 then (col 4 + c3) % 64
  else col 5 + c4

-- spec-side
def sixCarry (col : Fin 6 → ℕ) (m : Fin 5) : ℕ :=
  let c0 := col 0 / 64
  let c1 := (col 1 + c0) / 64
  let c2 := (col 2 + c1) / 64
  let c3 := (col 3 + c2) / 64
  let c4 := (col 4 + c3) / 64
  if (m : ℕ) = 0 then c0
  else if (m : ℕ) = 1 then c1
  else if (m : ℕ) = 2 then c2
  else if (m : ℕ) = 3 then c3
  else c4

/-- The honest chain's five per-column equations at the middle columns, plus
the final one at column `5`; column `0`'s equation is `rfl`-close and stated
separately. All are pure `Nat.div_add_mod` facts. -/
theorem sixDigit_sixCarry_eq (col : Fin 6 → ℕ) :
    col 0 = sixDigit col 0 + 64 * sixCarry col 0 ∧
    col 1 + sixCarry col 0 = sixDigit col 1 + 64 * sixCarry col 1 ∧
    col 2 + sixCarry col 1 = sixDigit col 2 + 64 * sixCarry col 2 ∧
    col 3 + sixCarry col 2 = sixDigit col 3 + 64 * sixCarry col 3 ∧
    col 4 + sixCarry col 3 = sixDigit col 4 + 64 * sixCarry col 4 ∧
    col 5 + sixCarry col 4 = sixDigit col 5 := by
  unfold sixDigit sixCarry
  norm_num
  omega

/-- Every one of the honest chain's first five digits is a base-`64` digit. -/
theorem sixDigit_lt_of_le {col : Fin 6 → ℕ} (m : Fin 6) (hm : (m : ℕ) < 5) :
    sixDigit col m < 64 := by
  unfold sixDigit
  have h5 : (m : ℕ) ≠ 5 := by omega
  fin_cases m <;> simp_all <;> omega

/-- Given a bound `col m ≤ 63 * (C + 1)` on every raw column, every carry of
the honest chain is at most `C`. -/
theorem sixCarry_le {col : Fin 6 → ℕ} {C : ℕ} (hcol : ∀ m, col m ≤ 63 * (C + 1))
    (m : Fin 5) : sixCarry col m ≤ C := by
  unfold sixCarry
  have h0 := hcol 0
  have h1 := hcol 1
  have h2 := hcol 2
  have h3 := hcol 3
  have h4 := hcol 4
  fin_cases m <;> simp <;> omega

/-- Given the represented total is below `64 ^ 6`, the honest chain's last
digit is a base-`64` digit too. -/
theorem sixDigit_five_lt {col : Fin 6 → ℕ}
    (htot : (∑ m : Fin 6, col m * 64 ^ (m : ℕ)) < 64 ^ 6) :
    sixDigit col 5 < 64 := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := sixDigit_sixCarry_eq col
  have hkey := batch_column_sum (col := col) (ndig := sixDigit col) (carry := sixCarry col)
    h0 h1 h2 h3 h4 h5
  have hd0 := sixDigit_lt_of_le (col := col) 0 (by norm_num)
  have hd1 := sixDigit_lt_of_le (col := col) 1 (by norm_num)
  have hd2 := sixDigit_lt_of_le (col := col) 2 (by norm_num)
  have hd3 := sixDigit_lt_of_le (col := col) 3 (by norm_num)
  have hd4 := sixDigit_lt_of_le (col := col) 4 (by norm_num)
  simp only [Fin.sum_univ_six] at hkey htot
  norm_num at hkey htot
  omega

/-- **Uniqueness of the honest six-digit representation.** Two base-`64`
six-digit vectors with the same weighted sum agree pointwise: standard
arithmetic, needed to recognize the honest chain's output as a public
constant's own digits. -/
theorem sixDigits_unique {a b : Fin 6 → ℕ} (ha : ∀ m, a m < 64) (hb : ∀ m, b m < 64)
    (heq : ∑ m : Fin 6, a m * 64 ^ (m : ℕ) = ∑ m : Fin 6, b m * 64 ^ (m : ℕ)) :
    ∀ m, a m = b m := by
  have ha0 := ha 0
  have ha1 := ha 1
  have ha2 := ha 2
  have ha3 := ha 3
  have ha4 := ha 4
  have ha5 := ha 5
  have hb0 := hb 0
  have hb1 := hb 1
  have hb2 := hb 2
  have hb3 := hb 3
  have hb4 := hb 4
  have hb5 := hb 5
  simp only [Fin.sum_univ_six] at heq
  norm_num at heq
  have key : a 0 = b 0 ∧ a 1 = b 1 ∧ a 2 = b 2 ∧ a 3 = b 3 ∧ a 4 = b 4 ∧ a 5 = b 5 := by omega
  intro m
  fin_cases m <;> simp [key.1, key.2.1, key.2.2.1, key.2.2.2.1, key.2.2.2.2.1, key.2.2.2.2.2]

/-! ### Honest per-coefficient advice (completeness)

The magnitude digits a coefficient's schoolbook square reads, matching
`limbs`: ordinary base-`64` digits of a natural magnitude, with slot `2`
forced to zero when `hi`. Pure arithmetic. -/

-- spec-side
def honestLimbsNat (hi : Bool) (magNat : ℕ) : Fin 3 → ℕ :=
  fun l => if hi ∧ (l : ℕ) = 2 then 0 else magNat / 64 ^ (l : ℕ) % 64

/-- The masked digits reconstruct the magnitude, given it fits the two-digit
budget when `hi`, and always fits the three-digit budget. -/
theorem honestLimbsNat_sum {hi : Bool} {magNat : ℕ} (hhi : hi = true → magNat < 4096)
    (h3 : magNat < 64 ^ 3) :
    ∑ l : Fin 3, honestLimbsNat hi magNat l * 64 ^ (l : ℕ) = magNat := by
  unfold honestLimbsNat
  cases hi with
  | false =>
    simp only [Bool.false_eq_true, false_and, if_false]
    simp only [Fin.sum_univ_three]
    norm_num
    omega
  | true =>
    have h4 := hhi rfl
    simp only [true_and]
    simp only [Fin.sum_univ_three]
    norm_num
    omega

/-- The honest schoolbook column of a coefficient's masked magnitude digits,
in naturals. -/
-- spec-side
def honestColprodNat (hi : Bool) (magNat : ℕ) (m : Fin 6) : ℕ :=
  ∑ j : Fin 3, ∑ k : Fin 3,
    if (j : ℕ) + k = (m : ℕ) then honestLimbsNat hi magNat j * honestLimbsNat hi magNat k else 0

/-- The schoolbook columns' weighted sum is the exact square of the masked
magnitude: a Cauchy-product identity. -/
theorem honestColprodNat_sum (hi : Bool) (magNat : ℕ) :
    ∑ m : Fin 6, honestColprodNat hi magNat m * 64 ^ (m : ℕ) =
      (∑ l : Fin 3, honestLimbsNat hi magNat l * 64 ^ (l : ℕ)) ^ 2 := by
  unfold honestColprodNat
  simp only [Fin.sum_univ_six, Fin.sum_univ_three]
  norm_num
  ring

/-- **The honest schoolbook columns, written out**: on the masked digits `x`, the columns are
`x₀²`, `2 x₀ x₁`, `2 x₀ x₂ + x₁²`, `2 x₁ x₂`, `x₂²` and `0`. -/
theorem honestColprodNat_apply (hi : Bool) (magNat : ℕ) :
    honestColprodNat hi magNat 0 = honestLimbsNat hi magNat 0 * honestLimbsNat hi magNat 0 ∧
    honestColprodNat hi magNat 1 = 2 * (honestLimbsNat hi magNat 0 * honestLimbsNat hi magNat 1) ∧
    honestColprodNat hi magNat 2 = 2 * (honestLimbsNat hi magNat 0 * honestLimbsNat hi magNat 2) +
      honestLimbsNat hi magNat 1 * honestLimbsNat hi magNat 1 ∧
    honestColprodNat hi magNat 3 = 2 * (honestLimbsNat hi magNat 1 * honestLimbsNat hi magNat 2) ∧
    honestColprodNat hi magNat 4 = honestLimbsNat hi magNat 2 * honestLimbsNat hi magNat 2 ∧
    honestColprodNat hi magNat 5 = 0 := by
  unfold honestColprodNat
  simp only [Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two]
  norm_num
  ring_nf
  trivial

/-- Every masked magnitude digit is a base-`64` digit. -/
theorem honestLimbsNat_lt (hi : Bool) (magNat : ℕ) (l : Fin 3) :
    honestLimbsNat hi magNat l < 64 := by
  unfold honestLimbsNat
  split
  · norm_num
  · exact Nat.mod_lt _ (by norm_num)

/-- **Every carry of the honest schoolbook chain is below `189`**: the columns hold at most one,
two, three, two and one products of digits below `64`. -/
theorem honestColprodNat_carry_lt_189 (hi : Bool) (magNat : ℕ) (m : Fin 5) :
    sixCarry (honestColprodNat hi magNat) m < 189 := by
  obtain ⟨a0, a1, a2, a3, a4, -⟩ := honestColprodNat_apply hi magNat
  have l0 := honestLimbsNat_lt hi magNat 0
  have l1 := honestLimbsNat_lt hi magNat 1
  have l2 := honestLimbsNat_lt hi magNat 2
  have b0 : honestColprodNat hi magNat 0 ≤ 63 * 63 := by rw [a0]; exact Nat.mul_le_mul (by omega) (by omega)
  have b1 : honestColprodNat hi magNat 1 ≤ 2 * (63 * 63) := by
    rw [a1]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
  have b2 : honestColprodNat hi magNat 2 ≤ 2 * (63 * 63) + 63 * 63 := by
    rw [a2]; exact Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega)))
      (Nat.mul_le_mul (by omega) (by omega))
  have b3 : honestColprodNat hi magNat 3 ≤ 2 * (63 * 63) := by
    rw [a3]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
  have b4 : honestColprodNat hi magNat 4 ≤ 63 * 63 := by rw [a4]; exact Nat.mul_le_mul (by omega) (by omega)
  unfold sixCarry
  fin_cases m <;> simp <;> omega

/-! ### Honest complement advice (completeness)

The complement check is the same ripple-carry chain applied to the sum of
the honest total's digits and the public bound's complement digits, with a
Boolean (not table-checked) carry and the top carry forced to zero. -/

/-- The honest complement's raw column: the honest total's digit plus the
digit of the public bound's complement. -/
-- spec-side
def honestDcol (Snat : Fin 6 → ℕ) (m : Fin 6) : ℕ :=
  Snat m + (34034726 - ∑ k : Fin 6, Snat k * 64 ^ (k : ℕ)) / 64 ^ (m : ℕ) % 64

/-- The public bound's own digits reconstruct it exactly. -/
theorem digit_34034726_sum : ∑ m : Fin 6, digit 34034726 (m : ℕ) * 64 ^ (m : ℕ) = 34034726 := by
  simp [digit, Fin.sum_univ_six]

/-- **The honest complement's chain reproduces the bound's digits**: the honest total's digits
plus the complement's sum to `34034726` (`β²`), so the ripple-carry chain of `honestDcol` has the
bound's own digits. -/
theorem honestDcol_sixDigit {Snat : Fin 6 → ℕ} (hSlt : ∀ m, Snat m < 64)
    (hSle : ∑ m : Fin 6, Snat m * 64 ^ (m : ℕ) ≤ 34034726) (m : Fin 6) :
    sixDigit (honestDcol Snat) m = digit 34034726 (m : ℕ) := by
  set Dtotal := 34034726 - ∑ k : Fin 6, Snat k * 64 ^ (k : ℕ) with hDtotal
  have hDrec : ∑ m : Fin 6, (Dtotal / 64 ^ (m : ℕ) % 64) * 64 ^ (m : ℕ) = Dtotal := by
    have : Dtotal < 64 ^ 6 := by
      have : (64 : ℕ) ^ 6 = 68719476736 := by norm_num
      omega
    simp only [Fin.sum_univ_six]
    norm_num
    omega
  have hcolTot : ∑ m : Fin 6, honestDcol Snat m * 64 ^ (m : ℕ) = 34034726 := by
    have hexpand : ∑ m : Fin 6, honestDcol Snat m * 64 ^ (m : ℕ) =
        (∑ m : Fin 6, Snat m * 64 ^ (m : ℕ)) +
          (∑ m : Fin 6, (Dtotal / 64 ^ (m : ℕ) % 64) * 64 ^ (m : ℕ)) := by
      unfold honestDcol
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun m _ => by ring
    rw [hexpand, hDrec]
    omega
  have hcolLt6 : ∑ m : Fin 6, honestDcol Snat m * 64 ^ (m : ℕ) < 64 ^ 6 := by
    rw [hcolTot]; norm_num
  obtain ⟨hd0, hd1, hd2, hd3, hd4, hd5⟩ := sixDigit_sixCarry_eq (honestDcol Snat)
  have hreconstruct := batch_column_sum hd0 hd1 hd2 hd3 hd4 hd5
  exact sixDigits_unique
    (a := sixDigit (honestDcol Snat)) (b := fun m => digit 34034726 (m : ℕ))
    (fun m => by
      rcases lt_or_ge (m : ℕ) 5 with hm | hm
      · exact sixDigit_lt_of_le m hm
      · have hm5 : m = 5 := by omega
        subst hm5; exact sixDigit_five_lt hcolLt6)
    (fun m => Nat.mod_lt _ (by norm_num))
    (by rw [← hreconstruct, hcolTot, digit_34034726_sum]) m

/-- **The honest complement's carries are bits.** -/
theorem honestDcol_sixCarry_le {Snat : Fin 6 → ℕ} (hSlt : ∀ m, Snat m < 64) (m : Fin 5) :
    sixCarry (honestDcol Snat) m ≤ 1 := by
  refine sixCarry_le (C := 1) (fun m => ?_) m
  have h1 := hSlt m
  have h2 : (34034726 - ∑ k : Fin 6, Snat k * 64 ^ (k : ℕ)) / 64 ^ (m : ℕ) % 64 < 64 :=
    Nat.mod_lt _ (by norm_num)
  unfold honestDcol
  omega

/-! ### The honest witness over all `1024` coefficients (completeness of `run`)

Away from any batch boundary, `colValNat` accumulates the honest per-
coefficient digits by an ordinary partial sum; this is the structural fact
that lets the batch-by-batch honest advice below match the fold's own
running state, via `colValNat_inv`.

Batch normalization has the same six-column ripple-carry shape as the per-coefficient square, but
with a single-digit (not two-limb) carry, so a raw column fits under `63 · 64` (a prior digit plus
`63` new coefficients' digits, each below `64`). -/

/-- The centered magnitude of an extracted coefficient. -/
-- spec-side
def honestMagNat (vals : Fin 1024 → ℕ) (i : Fin 1024) : ℕ :=
  (LatticeCrypto.centeredRepr (vals i : ZMod 12289)).natAbs

/-- Coefficient `i`'s honest schoolbook square digit `m`. -/
-- spec-side
def honestSqDigit (vals : Fin 1024 → ℕ) (i : Fin 1024) (m : Fin 6) : ℕ :=
  sixDigit (honestColprodNat (decide (512 ≤ (i : ℕ))) (honestMagNat vals i)) m

/-- The coefficient index starting batch `b` (`0`-indexed): a multiple of
`63`, capped at `1024` (the last batch is short, `16` coefficients). -/
-- spec-side
def startOf (b : ℕ) : ℕ := min (63 * b) 1024

/-- The raw column fed to batch `b`'s normalization: the previous batch's
digits (`0` before the first batch) plus this batch's own coefficients'
square digits. -/
-- spec-side
def honestBatchColAt (vals : Fin 1024 → ℕ) : ℕ → Fin 6 → ℕ
  | 0 => fun _ => 0
  | (b + 1) => fun m => sixDigit (honestBatchColAt vals b) m +
      ∑ k ∈ Finset.Ico (startOf b) (startOf (b + 1)),
        (if h : k < 1024 then honestSqDigit vals ⟨k, h⟩ m else 0)

/-- Batch `b`'s (`0`-indexed) honest digits. -/
-- spec-side
def honestBatchNdig (vals : Fin 1024 → ℕ) (b : ℕ) : Fin 6 → ℕ :=
  sixDigit (honestBatchColAt vals (b + 1))

/-- Every extracted coefficient's centered magnitude is well below the
three-digit budget: at most half the characteristic. -/
theorem honestMagNat_lt3 (vals : Fin 1024 → ℕ) (i : Fin 1024) : honestMagNat vals i < 64 ^ 3 := by
  unfold honestMagNat
  have := LatticeCrypto.centeredRepr_abs_le (vals i : ZMod 12289)
  omega

/-- A coefficient's honest schoolbook square digits reconstruct its centered
magnitude squared. -/
theorem honestColprodNat_sixDigit_sum {hi : Bool} {magNat : ℕ} (hhi : hi = true → magNat < 4096)
    (h3 : magNat < 64 ^ 3) :
    ∑ m : Fin 6, sixDigit (honestColprodNat hi magNat) m * 64 ^ (m : ℕ) = magNat ^ 2 := by
  obtain ⟨h0, h1, h2, h3', h4, h5⟩ := sixDigit_sixCarry_eq (honestColprodNat hi magNat)
  rw [(batch_column_sum h0 h1 h2 h3' h4 h5).symm, honestColprodNat_sum, honestLimbsNat_sum hhi h3]

/-- Every coefficient's honest square digits reconstruct its centered
magnitude squared. -/
theorem honestSqDigit_sum (vals : Fin 1024 → ℕ) (i : Fin 1024)
    (hhi : 512 ≤ (i : ℕ) → honestMagNat vals i < 4096) :
    ∑ m : Fin 6, honestSqDigit vals i m * 64 ^ (m : ℕ) = honestMagNat vals i ^ 2 :=
  honestColprodNat_sixDigit_sum (fun h => hhi (by simpa using h)) (honestMagNat_lt3 vals i)

/-- Every honest square digit is a base-`64` digit, given the coefficient's
magnitude fits the two-digit budget when it is an `s₂` coefficient. -/
theorem honestSqDigit_lt (vals : Fin 1024 → ℕ) (i : Fin 1024)
    (hhi : 512 ≤ (i : ℕ) → honestMagNat vals i < 4096) (m : Fin 6) :
    honestSqDigit vals i m < 64 := by
  unfold honestSqDigit
  rcases lt_or_ge (m : ℕ) 5 with hm | hm
  · exact sixDigit_lt_of_le m hm
  · have hm5 : m = 5 := by omega
    subst hm5
    apply sixDigit_five_lt
    rw [honestColprodNat_sum,
      honestLimbsNat_sum (fun h => hhi (of_decide_eq_true h)) (honestMagNat_lt3 vals i)]
    calc honestMagNat vals i ^ 2 < (64 ^ 3) ^ 2 :=
          Nat.pow_lt_pow_left (honestMagNat_lt3 vals i) (by norm_num)
      _ = 64 ^ 6 := by norm_num

/-- Coefficient `k`'s honest square digit `m`, padded by zero past `1024`: the
summand of `honestBatchColAt`. -/
-- spec-side
def honestSqDigitAt (vals : Fin 1024 → ℕ) (k : ℕ) (m : Fin 6) : ℕ :=
  if h : k < 1024 then honestSqDigit vals ⟨k, h⟩ m else 0

/-- **A batch's square digits, by position in the batch**: batch `b`'s coefficients are
`63 b + s`, `s < 63`, the padded digit `0` past `1024`. -/
theorem sum_batch_honestSqDigitAt (vals : Fin 1024 → ℕ) {b : ℕ} (hb : b < 17) (m : Fin 6) :
    ∑ k ∈ Finset.Ico (startOf b) (startOf (b + 1)), honestSqDigitAt vals k m =
      ∑ s : Fin 63, honestSqDigitAt vals (63 * b + s) m := by
  have h0 : startOf b = 63 * b := by unfold startOf; omega
  have hsub : Finset.Ico (startOf b) (startOf (b + 1)) ⊆ Finset.Ico (63 * b) (63 * b + 63) := by
    intro k hk
    simp only [Finset.mem_Ico, startOf] at hk ⊢
    omega
  rw [Finset.sum_subset hsub fun k hk hk' => by
    simp only [Finset.mem_Ico, startOf] at hk hk'
    unfold honestSqDigitAt
    rw [dif_neg (by omega)], Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left,
    ← Fin.sum_univ_eq_sum_range (fun s => honestSqDigitAt vals (63 * b + s) m)]

/-- Coefficient `k`'s centered magnitude squared, padded by zero past `1024`. -/
-- spec-side
def honestMagSqAt (vals : Fin 1024 → ℕ) (k : ℕ) : ℕ :=
  if h : k < 1024 then honestMagNat vals ⟨k, h⟩ ^ 2 else 0

theorem honestBatchColAt_succ (vals : Fin 1024 → ℕ) (b : ℕ) (m : Fin 6) :
    honestBatchColAt vals (b + 1) m = sixDigit (honestBatchColAt vals b) m +
      ∑ k ∈ Finset.Ico (startOf b) (startOf (b + 1)), honestSqDigitAt vals k m := rfl

/-- Every prefix of the padded squared magnitudes is bounded by the global sum. -/
theorem honestMagSqAt_prefix_le (vals : Fin 1024 → ℕ)
    (hglobal : ∑ i : Fin 1024, honestMagNat vals i ^ 2 ≤ 34034726) {n : ℕ} (hn : n ≤ 1024) :
    ∑ k ∈ Finset.range n, honestMagSqAt vals k ≤ 34034726 := by
  have hfull : ∑ k ∈ Finset.range 1024, honestMagSqAt vals k = ∑ i : Fin 1024, honestMagNat vals i ^ 2 := by
    rw [Finset.sum_range (fun k => honestMagSqAt vals k)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [honestMagSqAt, dif_pos i.isLt]
  calc ∑ k ∈ Finset.range n, honestMagSqAt vals k
      ≤ ∑ k ∈ Finset.range 1024, honestMagSqAt vals k :=
        Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr hn)
    _ ≤ 34034726 := (le_of_eq hfull).trans hglobal

/-- **The honest batch columns.** Jointly by induction on the batch index: every
honest raw batch column fits the single-digit carry bound `63 · 64`, and its
represented value is the sum of the squared magnitudes of the coefficients
before the batch's start. The two parts are proved together, since the bound on
the previous batch's top digit needs its represented value. -/
theorem honestBatchColAt_facts (vals : Fin 1024 → ℕ)
    (hglobal : ∑ i : Fin 1024, honestMagNat vals i ^ 2 ≤ 34034726)
    (hhi : ∀ i : Fin 1024, 512 ≤ (i : ℕ) → honestMagNat vals i < 4096) :
    ∀ c ≤ 17, (∀ m, honestBatchColAt vals c m ≤ 63 * 64) ∧
      ∑ m : Fin 6, honestBatchColAt vals c m * 64 ^ (m : ℕ) =
        ∑ k ∈ Finset.range (startOf c), honestMagSqAt vals k := by
  intro c
  induction c with
  | zero =>
    intro _
    exact ⟨fun m => by simp [honestBatchColAt], by simp [honestBatchColAt, startOf]⟩
  | succ c ih =>
    intro hc
    obtain ⟨-, ihs⟩ := ih (by omega)
    have htot : ∑ m : Fin 6, honestBatchColAt vals c m * 64 ^ (m : ℕ) < 64 ^ 6 := by
      rw [ihs]
      exact lt_of_le_of_lt (honestMagSqAt_prefix_le vals hglobal (by unfold startOf; omega))
        (by norm_num)
    have hdig : ∀ m, sixDigit (honestBatchColAt vals c) m ≤ 63 := by
      intro m
      rcases lt_or_ge (m : ℕ) 5 with hm | hm
      · have := sixDigit_lt_of_le (col := honestBatchColAt vals c) m hm
        omega
      · have hm5 : m = 5 := by omega
        subst hm5
        have := sixDigit_five_lt htot
        omega
    have hlen : startOf (c + 1) - startOf c ≤ 63 := by unfold startOf; omega
    have hIco : ∀ m : Fin 6,
        ∑ k ∈ Finset.Ico (startOf c) (startOf (c + 1)), honestSqDigitAt vals k m ≤ 63 * 63 := by
      intro m
      calc ∑ k ∈ Finset.Ico (startOf c) (startOf (c + 1)), honestSqDigitAt vals k m
          ≤ ∑ _k ∈ Finset.Ico (startOf c) (startOf (c + 1)), 63 := by
            refine Finset.sum_le_sum fun k _ => ?_
            unfold honestSqDigitAt
            split_ifs with h
            · have := honestSqDigit_lt vals ⟨k, h⟩ (hhi _) m
              omega
            · omega
        _ = 63 * (startOf (c + 1) - startOf c) := by
            rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul, _root_.mul_comm]
        _ ≤ 63 * 63 := Nat.mul_le_mul_left _ hlen
    have hswap : ∑ m : Fin 6, (∑ k ∈ Finset.Ico (startOf c) (startOf (c + 1)),
          honestSqDigitAt vals k m) * 64 ^ (m : ℕ) =
        ∑ k ∈ Finset.Ico (startOf c) (startOf (c + 1)), honestMagSqAt vals k := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases h : k < 1024
      · simp only [honestSqDigitAt, honestMagSqAt, dif_pos h]
        exact honestSqDigit_sum vals ⟨k, h⟩ (hhi _)
      · simp [honestSqDigitAt, honestMagSqAt, dif_neg h]
    refine ⟨fun m => ?_, ?_⟩
    · rw [honestBatchColAt_succ]
      have := hdig m
      have := hIco m
      omega
    · have hsplit : ∑ m : Fin 6, honestBatchColAt vals (c + 1) m * 64 ^ (m : ℕ) =
          ∑ m : Fin 6, sixDigit (honestBatchColAt vals c) m * 64 ^ (m : ℕ) +
            ∑ m : Fin 6, (∑ k ∈ Finset.Ico (startOf c) (startOf (c + 1)),
              honestSqDigitAt vals k m) * 64 ^ (m : ℕ) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun m _ => by rw [honestBatchColAt_succ, add_mul]
      obtain ⟨h0, h1, h2, h3, h4, h5⟩ := sixDigit_sixCarry_eq (honestBatchColAt vals c)
      rw [hsplit, ← batch_column_sum h0 h1 h2 h3 h4 h5, ihs, hswap,
        Finset.sum_range_add_sum_Ico _ (by unfold startOf; omega)]

/-- Every honest batch column's represented value is at most `β²`. -/
theorem honestBatchColAt_total_le (vals : Fin 1024 → ℕ)
    (hglobal : ∑ i : Fin 1024, honestMagNat vals i ^ 2 ≤ 34034726)
    (hhi : ∀ i : Fin 1024, 512 ≤ (i : ℕ) → honestMagNat vals i < 4096) {c : ℕ} (hc : c ≤ 17) :
    ∑ m : Fin 6, honestBatchColAt vals c m * 64 ^ (m : ℕ) ≤ 34034726 := by
  rw [(honestBatchColAt_facts vals hglobal hhi c hc).2]
  exact honestMagSqAt_prefix_le vals hglobal (by unfold startOf; omega)

/-- Every honest batch digit is a base-`64` digit. -/
theorem honestBatchNdig_lt (vals : Fin 1024 → ℕ)
    (hglobal : ∑ i : Fin 1024, honestMagNat vals i ^ 2 ≤ 34034726)
    (hhi : ∀ i : Fin 1024, 512 ≤ (i : ℕ) → honestMagNat vals i < 4096) {b : ℕ} (hb : b ≤ 16)
    (m : Fin 6) : honestBatchNdig vals b m < 64 := by
  unfold honestBatchNdig
  rcases lt_or_ge (m : ℕ) 5 with hm | hm
  · exact sixDigit_lt_of_le m hm
  · have hm5 : m = 5 := by omega
    subst hm5
    exact sixDigit_five_lt (lt_of_le_of_lt
      (honestBatchColAt_total_le vals hglobal hhi (by omega)) (by norm_num))

/-- The last batch's honest digits represent the sum of all squared magnitudes. -/
theorem honestBatchNdig_last_sum (vals : Fin 1024 → ℕ)
    (hglobal : ∑ i : Fin 1024, honestMagNat vals i ^ 2 ≤ 34034726)
    (hhi : ∀ i : Fin 1024, 512 ≤ (i : ℕ) → honestMagNat vals i < 4096) :
    ∑ m : Fin 6, honestBatchNdig vals 16 m * 64 ^ (m : ℕ) ≤ 34034726 := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := sixDigit_sixCarry_eq (honestBatchColAt vals 17)
  unfold honestBatchNdig
  rw [← batch_column_sum h0 h1 h2 h3 h4 h5]
  exact honestBatchColAt_total_le vals hglobal hhi le_rfl

/-- A coefficient that ends a batch is the last before the next batch's start. -/
theorem startOf_batchIndex_succ {n : ℕ} (hn : n < 1024) (hb : boundary ⟨n, hn⟩ = true) :
    startOf ((batchIndex ⟨n, hn⟩ : ℕ) + 1) = n + 1 := by
  simp only [boundary, decide_eq_true_eq] at hb
  show min (63 * (n / 63 + 1)) 1024 = n + 1
  omega

end GordieHowe.Falcon512.NativeNorm
