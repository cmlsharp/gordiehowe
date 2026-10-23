-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Gadgets.NativeNorm
public import GordieHowe.Applications.Falcon512.Gadgets.EmulatedEncoding
public import GordieHowe.Foundations.Algebra.ParityReduction
public import GordieHowe.Foundations.Algebra.ReconstructSum
public import GordieHowe.Foundations.Algebra.CheckOps

@[expose] public section

/-!
# Native Falcon encodability of `s₂`

Transcribes `falcon_encoding_native` (`lib/schemes/falcon/falcon_encoding.h`,
`fn-native`). It reuses the native norm's magnitude digits: for an `s₂` coefficient the
digits are `a₀, a₁` and the top slot holds the high part `h`, so the magnitude is
`a₀ + 64·a₁` and `a = 128·h + a₀ + 64·b` with `b = a₁ − 2h`. The gadget asserts `b`
Boolean and requests `h + 48` (so `h < 16`); the budget slack `392 − Σ h` is split into a
committed high digit and a derived low digit, both requested. The norm gadget already
requests `a₀`, `a₁` and `h` in `[0, 64)`; `sound` takes those as a hypothesis supplied by that
gadget.

The conclusion is the emulated arm's `EmulatedEncoding.Lifted` on the two-digit
magnitudes, so the codec bridge (`EncodingBounds`, `compress_exists`) is shared.
-/

namespace GordieHowe.Falcon512.NativeEncoding

variable {F : Type*} [Field F] [DecidableEq F]

/-- The high part stored in the top digit slot of `s₂` coefficient `i`. -/
def high (w : NativeNorm.Wit F) (i : Fin 512) : F := (w.square ⟨512 + i, by omega⟩).a 2

/-- The encoding checks over the norm witness's `s₂` coefficients. -/
def run (w : NativeNorm.Wit F) (slackHi : F) : Check F :=
  let perCoeff := Check.all <| (List.finRange 512).map fun (i : Fin 512) =>
    let s := w.square ⟨512 + i, by omega⟩
    let b := s.a 1 - 2 * s.a 2
    (⟨decide (b * (b - 1) = 0), [s.a 2 + 48]⟩ : Check F)
  let slack : F := 392 - ∑ i, high w i
  let slackLo := slack - 64 * slackHi
  perCoeff.and ⟨true, [slackLo, slackHi]⟩

/-! ### Reading off `run`'s constraints -/

/-- Coefficient `i`'s lookup request lies among `run`'s needles. -/
theorem coeff_needle_mem (w : NativeNorm.Wit F) (slackHi : F) (i : Fin 512) :
    (w.square ⟨512 + i, by omega⟩).a 2 + 48 ∈ (run w slackHi).needles := by
  refine Check.needles_subset_and_left _ _ _ ?_
  rw [Check.all_needles, List.mem_flatMap]
  refine ⟨_, List.mem_map_of_mem (List.mem_finRange i), ?_⟩
  simp

/-- The derived low slack digit lies among `run`'s needles. -/
theorem slackLo_mem_needles (w : NativeNorm.Wit F) (slackHi : F) :
    392 - ∑ i, high w i - 64 * slackHi ∈ (run w slackHi).needles := by
  simp [run, Check.and_needles]

/-- The committed high slack digit lies among `run`'s needles. -/
theorem slackHi_mem_needles (w : NativeNorm.Wit F) (slackHi : F) :
    slackHi ∈ (run w slackHi).needles := by
  simp [run, Check.and_needles]

/-- Coefficient `i`'s Boolean assertion, restated as `ParityReduction.Holds` on its two
low digits. -/
theorem coeff_bit (w : NativeNorm.Wit F) (slackHi : F) (h : (run w slackHi).ok = true)
    (i : Fin 512) :
    ParityReduction.Holds ((w.square ⟨512 + i, by omega⟩).a 1)
      ((w.square ⟨512 + i, by omega⟩).a 2) := by
  simp only [run, Check.and_ok, Bool.and_eq_true_iff, and_true, Check.all_ok,
    List.all_eq_true] at h
  have hm := h _ (List.mem_map_of_mem (List.mem_finRange i))
  simpa [ParityReduction.Holds, ParityReduction.remainder] using hm

/-! ### The two-digit magnitude, in naturals -/

/-- The two-digit magnitude `a0 + 64 * a1`, with `a1 = 2 * h0 + b` for `a0 < 64`,
`b < 2` and `h0 < 16`: it is below the magnitude table `2048`, and its quotient by
the low radix `128` is exactly `h0`. Pure digit arithmetic, no field involved. -/
theorem magnitude_split {a0 a1 h0 b : ℕ} (ha0 : a0 < 64) (hh0 : h0 < 16) (hb : b < 2)
    (ha1 : a1 = 2 * h0 + b) :
    a0 + 64 * a1 < 2048 ∧ (a0 + 64 * a1) / 128 = h0 := by
  subst ha1
  exact ⟨by omega, by omega⟩

/-- Coefficient `i`'s magnitude digits, read off the norm's requests (`hdig`) and this
gadget's own requests and assertion (`hn`, `h`): naturals `a0 < 64` and `h0 < 16` with
the coefficient's raw high digit `a1 = 2 * h0 + b` for some bit `b < 2`. -/
theorem coeff_digits [CharP F 12289] (w : NativeNorm.Wit F) (slackHi : F)
    (hdig : ∀ i l, Range.IsNatBelow 64 ((w.square i).a l))
    (hn : Range.InTable 64 (run w slackHi).needles) (h : (run w slackHi).ok = true)
    (i : Fin 512) :
    ∃ a0 a1 h0 b : ℕ, a0 < 64 ∧ h0 < 16 ∧ b < 2 ∧ a1 = 2 * h0 + b ∧
      (a0 : F) = (w.square ⟨512 + i, by omega⟩).a 0 ∧
      (a1 : F) = (w.square ⟨512 + i, by omega⟩).a 1 ∧
      (h0 : F) = (w.square ⟨512 + i, by omega⟩).a 2 := by
  obtain ⟨a0, ha0, ha0c⟩ := hdig (⟨512 + i, by omega⟩ : Fin 1024) 0
  obtain ⟨a1, ha1, ha1c⟩ := hdig (⟨512 + i, by omega⟩ : Fin 1024) 1
  obtain ⟨h0, hh0, hh0c⟩ := hdig (⟨512 + i, by omega⟩ : Fin 1024) 2
  obtain ⟨n', hn'lt, hn'c⟩ := hn _ (coeff_needle_mem w slackHi i)
  have hh0lt16 : h0 < 16 := by
    have heq : (n' : F) = ((h0 + 48 : ℕ) : F) := by
      rw [hn'c, ← hh0c]; push_cast; ring
    have hnat : n' = h0 + 48 := IntLift.natCast_inj_of_lt (K := F) (by omega) (by omega) heq
    omega
  have hbit : ParityReduction.Holds ((a1 : F)) ((w.square ⟨512 + i, by omega⟩).a 2) := by
    rw [ha1c]; exact coeff_bit w slackHi h i
  have hpar := ParityReduction.sound (F := F) (p := 12289) (Q := 64) (n := a1)
    (by omega) (by omega) ⟨h0, hh0, hh0c⟩ hbit
  have hb : (a1 : F) = ((2 * h0 + a1 % 2 : ℕ) : F) := by
    have heq := hpar
    simp only [ParityReduction.remainder] at heq
    rw [← hh0c] at heq
    push_cast
    linear_combination heq
  have hbnat : a1 = 2 * h0 + a1 % 2 :=
    IntLift.natCast_inj_of_lt (K := F) (by omega) (by omega) hb
  exact ⟨a0, a1, h0, a1 % 2, ha0, hh0lt16, Nat.mod_lt a1 (by norm_num), hbnat, ha0c, ha1c, hh0c⟩

/-! ### Soundness -/

/-- **Soundness of the native encoding check.** With every lookup request in `[0, 64)`
(`hn`) and the norm's digit requests (`hdig`, from the gadget `NativeNorm`), the two-digit
magnitudes of the `s₂` coefficients satisfy the emulated encoding lift: each below
`2048`, cast to the magnitude wire, with `Σ ⌊mag/128⌋ ≤ 392`. `CharP F 12289` is a fact
about the field. -/
theorem sound [CharP F 12289] {w : NativeNorm.Wit F} {slackHi : F}
    (hdig : ∀ i l, Range.IsNatBelow 64 ((w.square i).a l))
    (hn : Range.InTable 64 (run w slackHi).needles) (h : (run w slackHi).ok = true) :
    ∃ mags : Fin falcon512.n → ℕ,
      EmulatedEncoding.Lifted falcon512
        (fun i => NativeNorm.mag true (w.square ⟨512 + i, by simp [falcon512] at i ⊢; omega⟩))
        mags := by
  choose a0 a1 h0 b ha0 hh0 hb ha1eq ha0c ha1c hh0c using coeff_digits w slackHi hdig hn h
  obtain ⟨l, hl, hlc⟩ := hn _ (slackLo_mem_needles w slackHi)
  obtain ⟨hh, hhh, hhc⟩ := hn _ (slackHi_mem_needles w slackHi)
  refine ⟨fun i => a0 i + 64 * a1 i, fun i => ?_, fun i => ?_, ?_⟩
  · rw [Codec.magnitudeBound_eq]
    exact (magnitude_split (ha0 i) (hh0 i) (hb i) (ha1eq i)).1
  · have pf : 512 + (i : ℕ) < 1024 := by simp [falcon512] at i ⊢; omega
    have hf : ∀ m : Fin 3,
        ((if (m : ℕ) = 0 then a0 i else if (m : ℕ) = 1 then a1 i else 0 : ℕ) : F) =
          NativeNorm.limbs true (w.square ⟨512 + (i : ℕ), pf⟩) m := by
      intro m
      fin_cases m <;> simp [NativeNorm.limbs, ha0c i, ha1c i]
    show ((a0 i + 64 * a1 i : ℕ) : F) =
        Range.reconstruct 64 (List.ofFn (NativeNorm.limbs true (w.square ⟨512 + (i : ℕ), pf⟩)))
    rw [Range.reconstruct_natCast _ _ hf]
    have hnateq : a0 i + 64 * a1 i =
        ∑ l : Fin 3,
          (if (l : ℕ) = 0 then a0 i else if (l : ℕ) = 1 then a1 i else 0) * 64 ^ (l : ℕ) := by
      simp only [Fin.sum_univ_three]
      norm_num
      ring
    rw [hnateq]
  · rw [Codec.lowRadix_eq, show falcon512.encodingHighBudget = 392 from by decide]
    have hqval : ∀ i : Fin 512, (a0 i + 64 * a1 i) / 128 = h0 i :=
      fun i => (magnitude_split (ha0 i) (hh0 i) (hb i) (ha1eq i)).2
    have hcastsum : ∑ i : Fin 512, (h0 i : F) = ∑ i : Fin 512, high w i :=
      Finset.sum_congr rfl (fun i _ => hh0c i)
    have hlc' : (l : F) = 392 - ∑ i, high w i - 64 * (hh : F) := by rw [hhc]; exact hlc
    have hsum392 : (l : F) + 64 * (hh : F) + ∑ i : Fin 512, (h0 i : F) = 392 := by
      linear_combination hlc' + hcastsum
    have hsumbound : ∑ i : Fin 512, h0 i ≤ 512 * 15 := by
      calc ∑ i : Fin 512, h0 i ≤ ∑ _i : Fin 512, 15 :=
            Finset.sum_le_sum (fun i _ => by have := hh0 i; omega)
        _ = 512 * 15 := by simp
    have hcast392 : ((l + 64 * hh + ∑ i, h0 i : ℕ) : F) = ((392 : ℕ) : F) := by
      push_cast; linear_combination hsum392
    have hnat392 : l + 64 * hh + ∑ i, h0 i = 392 :=
      IntLift.natCast_inj_of_lt (K := F) (by omega) (by norm_num) hcast392
    calc ∑ i : Fin 512, (a0 i + 64 * a1 i) / 128
        = ∑ i : Fin 512, h0 i := Finset.sum_congr rfl (fun i _ => hqval i)
      _ ≤ 392 := by omega

end GordieHowe.Falcon512.NativeEncoding
