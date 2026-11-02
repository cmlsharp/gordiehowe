-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Ring.Native.HonestA
public import GordieHowe.Applications.MLDSA44.Emulated.HonestValues
public import GordieHowe.Applications.MLDSA44.Ring.Carrier.Frontend.Embed

@[expose] public section

/-!
# GordieHowe: domain `A`'s honest values of the ML-DSA-44 ring carriers

The ML-DSA-44 ring carriers (`MLDSA44.Ring.Carrier.ROMParams`, `MLDSA44.Ring.Carrier.QROMParams`)
hold the emulated ML-DSA-44 program's domain `A` gadgets (`GordieHowe.MLDSA44.Ring.Carrier.CarrierAEmbed`).
This file gives the honest values of those gadgets at a ring input
(`GordieHowe.MLDSA44.Ring.RingIn`), read at the emulated program's value identifiers: the emulated
proof of possession's honest values (`GordieHowe.MLDSA44.Emulated.aVal`) at the signer's key and the
ring input's signature instead of a proof of possession's input. The honest naturals are the
native ring's (`GordieHowe.MLDSA44.Ring.Native.advice`, `offN`, `slN`, `zN`, `wtN`, `w1A`, `cA`;
the emulated program commits the UseHint advice at one digit of base `T^2` as the native one
does).

* **The values** (`aValE`): the hint bits, the challenge's support and sign bits, the UseHint
  output bits and signs, and the layout's digits (`GordieHowe.MLDSA44.Emulated.MldsaELayout`) of
  `w′`, of `z + 130993`, of the UseHint offset and of the slack.
* **UseHint with the wrap** at the honest values (`useHintE`, `UseHint.wrap_complete`), and the
  bounds of the offset and the slack (`offN_slN_le`).
* **The gadget predicates** (`ReadsAE`, `aPredsE`): at any environment of an emulated ML-DSA
  program whose domain `A` reads these values (and whose bound values read their digits), the
  predicates `0, 1, 2, 6 … 9, 11 … 15` hold, through the frontend's converses
  (`GordieHowe/Applications/MLDSA44/Emulated/HonestAlgebra.lean`).
-/

namespace GordieHowe.MLDSA44.Ring.Carrier

open GordieHowe.Bits RealizedProgram
open MLDSA44.NativeAlgebraCircuit (flat outputBits)
open MLDSA44.NativeAlgebraCircuit.Honest (hintBool wCoeff zCentered)
open MLDSA44.Native.Params (T γ₂ r1Bits)
open GordieHowe.MLDSA44.Ring.Native (advice offN slN zN wtN w1A cA zN_le zN_cast wtN_le)
open MLDSA44.Emulated (MldsaELayout aValues MldsaEAlgebra MldsaEmulatedHonest fm fmz rdA bitsA)

set_option linter.unusedSectionVars false

variable {msgLen : ℕ}

/-! ## The honest values -/

section Values

variable (y : RingIn msgLen)

/-- **The honest `w′`** of coefficient `m`: its canonical representative below `q`. -/
-- spec-side
noncomputable def wNR (m : Fin (MLDSA44.Native.Rows.nRows * MLDSA44.Native.Rows.deg)) : ℕ :=
  (flat (wCoeff y.key y.c y.z) m).val

variable (F : Type) [Field F] (L : MldsaELayout) in
/-- **Domain `A`'s honest values at the emulated identifiers** at a digit layout: the hint (`59`),
the challenge bits (`60`), the UseHint output bits (`63`) and signs (`64`), and the layout's
digits (`MLDSA44.Emulated.DigitLayout.digit`) of `w′`, of `z + 130993`, of the offset and of the
slack; `0` elsewhere. The emulated proof of possession's `aVal` at the ring input.

Running time: one `computeWApprox`, `O(k N)` UseHint advice computations and one digit per
coordinate. This running time is argued here, not proved in Lean. -/
-- spec-side
noncomputable def aValE (v j : ℕ) : F :=
  if v = 60 then
    (if h : j < 512 then cA y F ⟨j / 2, by change j / 2 < 256; omega⟩ ⟨j % 2, by omega⟩ else 0)
  else if v = 63 then
    (if h : j < 6144 then outputBits (w1A y F) ⟨j / 6, by change j / 6 < 4 * 256; omega⟩
      ⟨j % 6, by change j % 6 < 6; omega⟩ else 0)
  else if h : j < 1024 then
    if v = 59 then (((flat (hintBool y.h) (fm j h)).toNat : ℕ) : F)
    else if v = 64 then flat (fun a b => (advice y F a b).s) (fm j h)
    else if v ∈ L.w.ids then ((L.w.digit (wNR y (fm j h)) v : ℕ) : F)
    else if v ∈ L.z.ids then ((L.z.digit (zN y (fmz j h)) v : ℕ) : F)
    else if v ∈ L.offset.ids then ((L.offset.digit (offN y (fm j h)) v : ℕ) : F)
    else if v ∈ L.slack.ids then ((L.slack.digit (slN y (fm j h)) v : ℕ) : F)
    else 0
  else 0

end Values

/-! ## `aValE` at each value -/

section Access

variable (y : RingIn msgLen) (F : Type) [Field F] (L : MldsaELayout) {j : ℕ}

theorem aValE_59 (h : j < 1024) :
    aValE y F L 59 j = (((flat (hintBool y.h) (fm j h)).toNat : ℕ) : F) := by
  unfold aValE
  simp only [show (59 : ℕ) ≠ 60 by decide, show (59 : ℕ) ≠ 63 by decide, if_false, dif_pos h,
    if_true]

theorem aValE_64 (h : j < 1024) :
    aValE y F L 64 j = flat (fun a b => (advice y F a b).s) (fm j h) := by
  unfold aValE
  simp only [show (64 : ℕ) ≠ 60 by decide, show (64 : ℕ) ≠ 63 by decide,
    show (64 : ℕ) ≠ 59 by decide, if_false, dif_pos h, if_true]

theorem aValE_60 (h : j < 512) :
    aValE y F L 60 j = cA y F ⟨j / 2, by change j / 2 < 256; omega⟩ ⟨j % 2, by omega⟩ := by
  unfold aValE
  rw [if_pos rfl]
  exact dif_pos h

theorem aValE_63 (h : j < 6144) :
    aValE y F L 63 j = outputBits (w1A y F) ⟨j / 6, by change j / 6 < 4 * 256; omega⟩
      ⟨j % 6, by change j % 6 < 6; omega⟩ := by
  unfold aValE
  rw [if_neg (by decide), if_pos rfl]
  exact dif_pos h

variable {L} (hnd : (aValues L).Nodup)
include hnd

/-- **`w′`'s digit `s`** reads digit `s` of the honest `w′`. -/
theorem aValE_w {s : ℕ} (hs : s < L.w.ids.length) (h : j < 1024) :
    aValE y F L L.w.ids[s] j =
      ((MLDSA44.Emulated.DigitLayout.digitAt L.w.base (wNR y (fm j h)) s : ℕ) : F) := by
  have hv := List.getElem_mem hs
  obtain ⟨h1, h2, h3, h4⟩ := MLDSA44.Emulated.aVal_digit_ne hnd (MLDSA44.Emulated.w_mem_digitValues hv)
  unfold aValE
  rw [if_neg h1, if_neg h2, dif_pos h, if_neg h3, if_neg h4, if_pos hv,
    MLDSA44.Emulated.DigitLayout.digit_getElem (MLDSA44.Emulated.w_nodup hnd)]

/-- **`z + 130993`'s digit `s`** reads digit `s` of the honest shifted `z`. -/
theorem aValE_z {s : ℕ} (hs : s < L.z.ids.length) (h : j < 1024) :
    aValE y F L L.z.ids[s] j =
      ((MLDSA44.Emulated.DigitLayout.digitAt L.z.base (zN y (fmz j h)) s : ℕ) : F) := by
  have hv := List.getElem_mem hs
  obtain ⟨h1, h2, h3, h4⟩ := MLDSA44.Emulated.aVal_digit_ne hnd (MLDSA44.Emulated.z_mem_digitValues hv)
  unfold aValE
  rw [if_neg h1, if_neg h2, dif_pos h, if_neg h3, if_neg h4,
    if_neg (MLDSA44.Emulated.z_not_w hnd hv), if_pos hv,
    MLDSA44.Emulated.DigitLayout.digit_getElem (MLDSA44.Emulated.z_nodup hnd)]

/-- **The offset's digit `s`** reads digit `s` of the honest offset. -/
theorem aValE_offset {s : ℕ} (hs : s < L.offset.ids.length) (h : j < 1024) :
    aValE y F L L.offset.ids[s] j =
      ((MLDSA44.Emulated.DigitLayout.digitAt L.offset.base (offN y (fm j h)) s : ℕ) : F) := by
  have hv := List.getElem_mem hs
  obtain ⟨h1, h2, h3, h4⟩ :=
    MLDSA44.Emulated.aVal_digit_ne hnd (MLDSA44.Emulated.offset_mem_digitValues hv)
  obtain ⟨hw, hz⟩ := MLDSA44.Emulated.offset_not_wz hnd hv
  unfold aValE
  rw [if_neg h1, if_neg h2, dif_pos h, if_neg h3, if_neg h4, if_neg hw, if_neg hz, if_pos hv,
    MLDSA44.Emulated.DigitLayout.digit_getElem (MLDSA44.Emulated.offset_nodup hnd)]

/-- **The slack's digit `s`** reads digit `s` of the honest slack. -/
theorem aValE_slack {s : ℕ} (hs : s < L.slack.ids.length) (h : j < 1024) :
    aValE y F L L.slack.ids[s] j =
      ((MLDSA44.Emulated.DigitLayout.digitAt L.slack.base (slN y (fm j h)) s : ℕ) : F) := by
  have hv := List.getElem_mem hs
  obtain ⟨h1, h2, h3, h4⟩ :=
    MLDSA44.Emulated.aVal_digit_ne hnd (MLDSA44.Emulated.slack_mem_digitValues hv)
  obtain ⟨hw, hz, ho⟩ := MLDSA44.Emulated.slack_not_wzo hnd hv
  unfold aValE
  rw [if_neg h1, if_neg h2, dif_pos h, if_neg h3, if_neg h4, if_neg hw, if_neg hz, if_neg ho,
    if_pos hv, MLDSA44.Emulated.DigitLayout.digit_getElem (MLDSA44.Emulated.slack_nodup hnd)]

/-- **A digit of the layout is a natural's cast.** -/
theorem aValE_digit_natCast {v : ℕ} (hv : v ∈ L.digitValues) (h : j < 1024) :
    ∃ k : ℕ, aValE y F L v j = (k : F) := by
  obtain ⟨h1, h2, h3, h4⟩ := MLDSA44.Emulated.aVal_digit_ne hnd hv
  unfold aValE
  rw [if_neg h1, if_neg h2, dif_pos h, if_neg h3, if_neg h4]
  split_ifs
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨0, by simp⟩

end Access

/-! ## UseHint and the bounds at the honest naturals -/

section Facts

variable (y : RingIn msgLen)

/-- **The honest `w′` lies below `q`.** -/
theorem wNR_lt (m : Fin (MLDSA44.Native.Rows.nRows * MLDSA44.Native.Rows.deg)) :
    wNR y m < 8380417 :=
  ZMod.val_lt _

/-- **The honest UseHint advice passes with the wrap** at coefficient `m` (`UseHint.wrap_complete`
at one digit of base `T^2`, as `GordieHowe.MLDSA44.Emulated.useHint_honest`), the output bits read from
`w1Encode(w1)` (`NativeAlgebraCircuit.Honest.outputBits_honest`). -/
theorem useHintE (F : Type) [Field F] [DecidableEq F] (m : Fin MLDSA44.Native.Params.wDim) :
    UseHint.WrapHolds γ₂ (((flat (hintBool y.h) m).toNat : ℕ) : F) ((wNR y m : ℕ) : F)
      (flat (fun a b => (advice y F a b).s) m) ((offN y m : ℕ) : F) ((slN y m : ℕ) : F)
      (outputBits (w1A y F) m) := by
  have hok := UseHint.wrap_complete (K := F) (γ₂ := γ₂) (B := T * T) (k := 1) (r := r1Bits)
    (by decide) (by decide) (by decide) (by decide) (flat (hintBool y.h) m)
    (flat (wCoeff y.key y.c y.z) m)
  dsimp only at hok
  have hbits : outputBits (w1A y F) m =
      (UseHint.honest (K := F) γ₂ (T * T) 1 r1Bits (flat (hintBool y.h) m)
        (flat (wCoeff y.key y.c y.z) m)).bits :=
    MLDSA44.NativeAlgebraCircuit.Honest.outputBits_honest y.key y.c y.z y.h m
  rw [MLDSA44.Native.reconstruct_fin_one, MLDSA44.Native.reconstruct_fin_one] at hok
  rw [hbits]
  exact hok

/-- **The honest offset and slack are at most `γ₂`** (`MLDSA44.useHintRelation_honest`). -/
theorem offN_slN_le (m : Fin (MLDSA44.Native.Rows.nRows * MLDSA44.Native.Rows.deg)) :
    offN y m ≤ 95232 ∧ slN y m ≤ 95232 := by
  unfold offN slN flat
  dsimp only
  have h := (GordieHowe.MLDSA44.useHintRelation_honest (γ₂ := mldsa44.γ₂) (by decide) (by decide)
    (hintBool y.h (finProdFinEquiv.symm m).1 (finProdFinEquiv.symm m).2)
    (wCoeff y.key y.c y.z (finProdFinEquiv.symm m).1 (finProdFinEquiv.symm m).2)).1
  have hE := GordieHowe.MLDSA44.useHintEndpoint_le_one (UseHint.hiCount mldsa44.γ₂)
    (hintBool y.h (finProdFinEquiv.symm m).1 (finProdFinEquiv.symm m).2)
    (GordieHowe.MLDSA44.useHintSign mldsa44.γ₂ (wCoeff y.key y.c y.z
      (finProdFinEquiv.symm m).1 (finProdFinEquiv.symm m).2))
    (_root_.MLDSA.Concrete.useHintCoeff
      (hintBool y.h (finProdFinEquiv.symm m).1 (finProdFinEquiv.symm m).2)
      (wCoeff y.key y.c y.z (finProdFinEquiv.symm m).1 (finProdFinEquiv.symm m).2) mldsa44.γ₂)
  have hγ : mldsa44.γ₂ = 95232 := rfl
  have hM : UseHint.hiCount mldsa44.γ₂ = (_root_.MLDSA.modulus - 1) / (2 * mldsa44.γ₂) := rfl
  rw [← hM] at h
  constructor
  · exact (Nat.mod_le _ _).trans (by simp only [Fin.val_zero, pow_zero, Nat.div_one]; omega)
  · exact (Nat.mod_le _ _).trans (by simp only [Fin.val_zero, pow_zero, Nat.div_one]; omega)

end Facts

/-! ## The gadget predicates at an environment reading the honest values -/

section Holds

variable {program : RealizedProgram} [MldsaEAlgebra program] {F0 FH : FieldInterp} [AField F0]
  [HField FH]

set_option hygiene false in
local notation "interp" => mldsaInterpOf F0 FH

set_option hygiene false in
local notation "nat" => MLDSA44.Emulated.MldsaEmbed.nat program

set_option hygiene false in
local notation "L" => MldsaEAlgebra.layout program

variable [MLDSA44.MldsaHSample nat]
  [MLDSA44.MldsaHConsts nat FH] [MLDSA44.MldsaHHonest nat]
  [MLDSA44.MldsaHSelHonest nat] [MLDSA44.MldsaHNativeData FH]
  [MLDSA44.MldsaHNodes FH] [hE : MldsaEmulatedHonest program F0 FH]

open MLDSA44.Emulated.MldsaEmulatedHonest

/-- **An environment of an emulated ML-DSA program reads domain `A`'s honest values** of a ring
input: its committed values of domain `A` (`aValues` of the program's layout) read `aValE`, and
its bound values `z` (`58`), `w′` (`61`), the offset (`65`) and the slack (`66`) read their
expressions. -/
structure ReadsAE (e : program.Env interp) (y : RingIn msgLen) : Prop where
  /-- The committed values read the honest values. -/
  cells : ∀ v ∈ aValues L, ∀ j < (program.value v).size, rdA e v j = aValE y F0.K L v j
  /-- The bound values read their expressions. -/
  bound : ∀ v E, (program.value v).kind = .bound E → v ∈ [58, 61, 65, 66] → ∀ j,
    rdA e v j = program.evalE (program.reader e) 0 E j

variable {y : RingIn msgLen} {e : program.Env interp} (hr : ReadsAE e y)
include hr

/-- **A digit of the layout reads its honest value.** -/
theorem rdAE_digit {v : ℕ} (hv : v ∈ (L).digitValues) {m : ℕ} (hm : m < 1024) :
    rdA e v m = aValE y F0.K L v m :=
  hr.cells v (MLDSA44.Emulated.mem_aValues_of_digit hv) m
    (by rw [digitSizes (program := program) v hv]; exact hm)

/-- **A fixed committed value of domain `A` reads its honest value.** -/
theorem rdAE_fixed {v : ℕ} (hv : v ∈ [59, 60, 63, 64]) {j : ℕ}
    (hj : j < (program.value v).size) : rdA e v j = aValE y F0.K L v j :=
  hr.cells v (MLDSA44.Emulated.fixed_mem_aValues hv) j hj

/-- **`w′` reads its honest natural.** -/
theorem rdAE_61 {m : ℕ} (hm : m < 1024) :
    rdA e 61 m = ((wNR y (fm m hm) : ℕ) : (interp 0).K) := by
  rw [hr.bound 61 _ kind62 (by simp)]
  refine MLDSA44.Emulated.evalE_expr_of_digits wFits (wNR_lt y _) _ m fun s hs => ?_
  exact (rdAE_digit hr (MLDSA44.Emulated.w_mem_digitValues (List.getElem_mem hs)) hm).trans
    (aValE_w y _ a_nodup hs hm)

/-- **The offset reads its digits' sum.** -/
theorem rdAE_65 {m : ℕ} (hm : m < 1024) :
    rdA e 65 m = ((offN y (fm m hm) : ℕ) : (interp 0).K) := by
  rw [hr.bound 65 _ kind66 (by simp)]
  refine MLDSA44.Emulated.evalE_expr_of_digits offsetFits
    (Nat.lt_succ_of_le (offN_slN_le y _).1) _ m fun s hs => ?_
  exact (rdAE_digit hr (MLDSA44.Emulated.offset_mem_digitValues (List.getElem_mem hs)) hm).trans
    (aValE_offset y _ a_nodup hs hm)

/-- **The slack reads its digits' sum.** -/
theorem rdAE_66 {m : ℕ} (hm : m < 1024) :
    rdA e 66 m = ((slN y (fm m hm) : ℕ) : (interp 0).K) := by
  rw [hr.bound 66 _ kind67 (by simp)]
  refine MLDSA44.Emulated.evalE_expr_of_digits slackFits
    (Nat.lt_succ_of_le (offN_slN_le y _).2) _ m fun s hs => ?_
  exact (rdAE_digit hr (MLDSA44.Emulated.slack_mem_digitValues (List.getElem_mem hs)) hm).trans
    (aValE_slack y _ a_nodup hs hm)

/-- **`z` reads its centered coefficient.** -/
theorem rdAE_58 {m : ℕ} (hm : m < 1024) :
    rdA e 58 m = ((flat (zCentered y.z) (fmz m hm) : ℤ) : (interp 0).K) := by
  rw [hr.bound 58 _ kind59 (by simp), evalE_add, MLDSA44.Emulated.evalE_negA]
  have hz : program.evalE (program.reader e) 0 (L).z.expr m =
      ((zN y (fmz m hm) : ℕ) : (interp 0).K) :=
    MLDSA44.Emulated.evalE_expr_of_digits zFits (by have := zN_le y (fmz m hm); omega) _ m
      fun s hs => (rdAE_digit hr (MLDSA44.Emulated.z_mem_digitValues (List.getElem_mem hs)) hm).trans
        (aValE_z y _ a_nodup hs hm)
  change _ + -rdA _ 62 m = _
  rw [hz, MLDSA44.Emulated.rdA_63 _ hm, zN_cast]
  ring

/-- **The UseHint output bits read the honest output bits.** -/
theorem bitsAE {m : ℕ} (hm : m < 1024) :
    bitsA e m = outputBits (w1A y F0.K) (fm m hm) := by
  funext b
  have hb := b.isLt
  change (b : ℕ) < 6 at hb
  unfold bitsA
  rw [rdAE_fixed hr (by simp) (by rw [size64 (program := program)]; omega), aValE_63 y _ _ (by omega)]
  have e1 : (⟨(6 * m + b) / 6, by change (6 * m + b) / 6 < 4 * 256; omega⟩ :
      Fin (MLDSA44.Native.Rows.nRows * MLDSA44.Native.Rows.deg)) = fm m hm :=
    Fin.ext (by simp only [fm]; omega)
  have e2 : (⟨(6 * m + b) % 6, by change (6 * m + b) % 6 < 6; omega⟩ : Fin mldsa44.r1_bits) = b :=
    Fin.ext (by simp only; omega)
  rw [e1, e2]

theorem w1BitsE_bool : ∀ m < 1024, ∀ t < 6, rdA e 63 (6 * m + t) = 0 ∨ rdA e 63 (6 * m + t) = 1 :=
  fun m hm t ht => by
    have h := congrFun (bitsAE hr hm) ⟨t, ht⟩
    unfold bitsA at h
    rw [h]
    unfold outputBits w1A
    exact Falcon512.HashCircuit.wiresOfByteVec_allBool _ _

theorem h59E_bool : ∀ m < 1024, rdA e 59 m = 0 ∨ rdA e 59 m = 1 := fun m hm => by
  rw [rdAE_fixed hr (by simp) (by rw [size60 (program := program)]; exact hm), aValE_59 y _ _ hm]
  cases flat (hintBool y.h) (fm m hm) <;> simp

theorem h64E_bool : ∀ m < 1024, rdA e 64 m = 0 ∨ rdA e 64 m = 1 := fun m hm => by
  rw [rdAE_fixed hr (by simp) (by rw [size65 (program := program)]; exact hm), aValE_64 y _ _ hm]
  change ((MLDSA44.useHintSign γ₂ _).toNat : F0.K) = 0 ∨ ((MLDSA44.useHintSign γ₂ _).toNat : F0.K) = 1
  cases MLDSA44.useHintSign γ₂ _ <;> simp

theorem h60E_bool : ∀ s < 512, rdA e 60 s = 0 ∨ rdA e 60 s = 1 := fun s hs => by
  rw [rdAE_fixed hr (by simp) (by rw [size61 (program := program)]; exact hs), aValE_60 y _ _ hs]
  unfold cA
  rcases Nat.mod_two_eq_zero_or_one s with h | h
  · simp only [h]
    exact (MLDSA44.Native.ternaryBits_bool _).1
  · simp only [h]
    exact (MLDSA44.Native.ternaryBits_bool _).2

theorem useHintE_at {m : ℕ} (hm : m < 1024) :
    UseHint.WrapHolds mldsa44.γ₂ (rdA e 59 m) (rdA e 61 m) (rdA e 64 m) (rdA e 65 m) (rdA e 66 m)
      (bitsA e m) := by
  rw [rdAE_fixed hr (v := 59) (by simp) (by rw [size60 (program := program)]; exact hm),
    rdAE_fixed hr (v := 64) (by simp) (by rw [size65 (program := program)]; exact hm),
    rdAE_61 hr hm, rdAE_65 hr hm, rdAE_66 hr hm, bitsAE hr hm, aValE_59 y _ _ hm, aValE_64 y _ _ hm]
  exact useHintE y (interp 0).K (fm m hm)

theorem offsetE_nat : ∀ m < 1024, ∃ k : ℕ, k < (L).offsetBound ∧ rdA e 65 m = k :=
  fun m hm => ⟨_, by have := (offN_slN_le y (fm m hm)).1; have := offsetRoom (program := program); omega,
    rdAE_65 hr hm⟩

theorem slackE_nat : ∀ m < 1024, ∃ k : ℕ, k < (L).offsetBound ∧ rdA e 66 m = k :=
  fun m hm => ⟨_, by have := (offN_slN_le y (fm m hm)).2; have := offsetRoom (program := program); omega,
    rdAE_66 hr hm⟩

/-- **The weight of the honest hint** reads the number of set hint bits. -/
theorem weightE_sum : ∑ t : Fin 1024, rdA e 59 t = ((wtN y : ℕ) : (interp 0).K) := by
  unfold wtN
  rw [Nat.cast_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [rdAE_fixed hr (by simp) (by rw [size60 (program := program)]; exact t.isLt),
    aValE_59 y _ _ t.isLt]
  rfl

/-- **Domain `A`'s gadget predicates hold** at an environment reading the honest values: the
predicates of `GordieHowe.MLDSA44.Ring.Carrier.aSource` (`0, 1, 2, 6 … 9, 11 … 15`). -/
theorem aPredsE {q : ℕ} (hq : q ∈ aSource) :
    program.HoldsWith (program.reader e) (program.predicate q).body := by
  have h60 := size60 (program := program)
  have h61 := size61 (program := program)
  have h64 := size64 (program := program)
  have h65 := size65 (program := program)
  obtain ⟨b6, b7, b8, b9⟩ := MLDSA44.Emulated.boolChecks (program := program)
  simp only [aSource, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact MLDSA44.Emulated.w1bound0_of _ (w1BitsE_bool hr) fun _ hm => (useHintE_at hr hm).le
  · exact MLDSA44.Emulated.decompose1_of (w1BitsE_bool hr) fun _ hm => (useHintE_at hr hm).wrap
  · exact MLDSA44.Emulated.interval2_of _ (w1BitsE_bool hr) (h59E_bool hr) (h64E_bool hr)
      (offsetE_nat hr) (slackE_nat hr) fun _ hm => (useHintE_at hr hm).interval
  · exact MLDSA44.Emulated.boolA_of _ b6 fun j hj => h59E_bool hr j (h60 ▸ hj)
  · exact MLDSA44.Emulated.boolA_of _ b7 fun j hj => h60E_bool hr j (h61 ▸ hj)
  · refine MLDSA44.Emulated.boolA_of _ b8 fun j hj => ?_
    rw [h64] at hj
    have := w1BitsE_bool hr (j / 6) (by omega) (j % 6) (by omega)
    rwa [Nat.div_add_mod] at this
  · exact MLDSA44.Emulated.boolA_of _ b9 fun j hj => h64E_bool hr j (h65 ▸ hj)
  · exact MLDSA44.Emulated.w11_of _ fun m hm => ⟨_, by have := wNR_lt y (fm m hm); omega,
      rdAE_61 hr hm⟩
  · exact MLDSA44.Emulated.norm12_of _ fun m hm => ⟨zN y (fmz m hm), by
      have := zN_le y (fmz m hm); omega, by rw [rdAE_58 hr hm, zN_cast]⟩
  · exact MLDSA44.Emulated.offset13_of _ (offsetE_nat hr)
  · exact MLDSA44.Emulated.slack14_of _ (slackE_nat hr)
  · exact MLDSA44.Emulated.weight15_of _ ⟨wtN y, by have := wtN_le y; omega,
      weightE_sum hr⟩

end Holds

end GordieHowe.MLDSA44.Ring.Carrier
