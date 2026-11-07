-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Ring.HonestInput
public import GordieHoweCerts.Applications.MLDSA44.Native.HonestValues

@[expose] public section

/-!
# GordieHowe: domain `A`'s honest values of the native ML-DSA ring programs

The honest values of the native ML-DSA ring programs' domain `A` gadgets, read at the native
ML-DSA program's value identifiers (`GordieHowe.MLDSA44.Native.AValues`, the identifiers the
ring programs hold through their renaming, `GordieHowe.MLDSA44.Ring.Native.MldsaRingEmbed`): the native
proof of possession's honest values (`GordieHowe.MLDSA44.Native.aVal`) at the signer's key and the
ring input's signature (`GordieHowe.MLDSA44.Ring.RingIn`) instead of a proof of possession's input.

* **The honest naturals** (`advice`, `offN`, `slN`, `zN`, `wtN`, `w1A`) and **values** (`aValR`):
  the hint bits, the challenge's support and sign bits, `w′`, the UseHint output bits and signs,
  the base-`512` digits of `z + 130993`, of the UseHint offset and of the slack
  (`lib/gordiehowe/examples/mldsa/mldsa_gadgets.h`, the C++ `UseHint` advice).
* **UseHint at the honest values** (`useHint_ring`, `UseHint.native_complete`), the norm bound
  (`zN_le`) and the hint weight (`wtN_le`) from the input's verification (`RingIn.checks`).
* **The gadget predicates** (`ReadsA`, `w1bound_ring` … `weight_ring`): at any environment of a
  native ML-DSA program whose domain `A` reads these values (and whose bound values read their
  digits), the predicates `1, 2, 3, 6 … 9, 11 … 14` hold, through the frontend's converses
  (`GordieHoweCerts/Applications/MLDSA44/Honest/A.lean`).
-/

namespace GordieHowe.MLDSA44.Ring.Native

open GordieHowe.Bits RealizedProgram
open MLDSA44.NativeAlgebraCircuit (flat outputBits)
open MLDSA44.NativeAlgebraCircuit.Honest (hintBool wCoeff zCentered)
open MLDSA44.Native.Params (T γ₂ r1Bits)

set_option linter.unusedSectionVars false

variable {msgLen : ℕ}

/-! ## The honest naturals of domain `A` -/

section Naturals

variable (y : RingIn msgLen)

/-- **The honest UseHint advice** of coefficient `(i, k)` (`mldsa_gadgets.h`, the C++ `UseHint`
advice; `UseHint.honest` at one digit of base `T^2`): the sign, the offset and the slack, at the
signer's key and the ring input's challenge, `z` and hint. -/
-- spec-side
noncomputable def advice (F : Type) [Field F] (i : Fin MLDSA44.Native.Params.nRows)
    (k : Fin MLDSA44.Native.Params.N) : UseHint.Advice F 1 r1Bits :=
  UseHint.honest γ₂ (T * T) 1 r1Bits (hintBool y.h i k) (wCoeff y.key y.c y.z i k)

/-- **The honest UseHint offset** of coefficient `m`, as committed: its base-`T^2` digit. -/
-- spec-side
noncomputable def offN (m : Fin (MLDSA44.Native.Rows.nRows * MLDSA44.Native.Rows.deg)) : ℕ :=
  flat (fun a b => GordieHowe.MLDSA44.useHintOffset mldsa44.γ₂ (hintBool y.h a b)
    (wCoeff y.key y.c y.z a b) / (T * T) ^ ((0 : Fin 1) : ℕ) % (T * T)) m

/-- **The honest UseHint slack** of coefficient `m`, as committed: its base-`T^2` digit. -/
-- spec-side
noncomputable def slN (m : Fin (MLDSA44.Native.Rows.nRows * MLDSA44.Native.Rows.deg)) : ℕ :=
  flat (fun a b =>
    (mldsa44.γ₂ - 1 + GordieHowe.MLDSA44.useHintEndpoint (UseHint.hiCount mldsa44.γ₂)
      (hintBool y.h a b) (GordieHowe.MLDSA44.useHintSign mldsa44.γ₂ (wCoeff y.key y.c y.z a b))
      (_root_.MLDSA.Concrete.useHintCoeff (hintBool y.h a b) (wCoeff y.key y.c y.z a b)
        mldsa44.γ₂) -
      GordieHowe.MLDSA44.useHintOffset mldsa44.γ₂ (hintBool y.h a b) (wCoeff y.key y.c y.z a b)) /
      (T * T) ^ ((0 : Fin 1) : ℕ) % (T * T)) m

/-- **The honest shifted `z`** of coefficient `m`: `z + 130993`, a natural below `261987`
(`zN_le`). -/
-- spec-side
def zN (m : Fin (MLDSA44.Native.Rows.nCols * MLDSA44.Native.Rows.deg)) : ℕ :=
  flat (fun a b => (zCentered y.z a b + 130993).toNat) m

/-- **The honest hint weight**: the number of set hint bits. -/
-- spec-side
def wtN : ℕ :=
  ∑ m : Fin (MLDSA44.Native.Rows.nRows * MLDSA44.Native.Rows.deg), (flat (hintBool y.h) m).toNat

/-- **The honest UseHint output bits**: the bits of `w1Encode(w1)` at `w1 = UseHint(h, w′)`. -/
-- spec-side
noncomputable def w1A (F : Type) [Field F] : BitWires F (8 * 768) :=
  Falcon512.HashCircuit.wiresOfByteVec fun p =>
    (MLDSA44.PoP.Compose.honestW1Bytes y.key y.c y.z y.h p).toNat

/-- **The honest challenge bits**: the support and the sign of coefficient `k`. -/
-- spec-side
def cA (F : Type) [Field F] (k : Fin MLDSA44.Native.Params.N) (t : Fin 2) : F :=
  ![(HashCircuit.ternaryBits (K := F) (y.c k)).1, (HashCircuit.ternaryBits (K := F) (y.c k)).2] t

variable (F : Type) [Field F] in
/-- **Domain `A`'s honest values at the native identifiers**: the hint (`58`), the challenge bits
(`59`), `w′` (`60`), the UseHint output bits (`62`) and signs (`63`); the digits of `z + 130993`
(`575`, `576`), of the offset (`580`, `581`) and of the slack (`582`, `583`); `0` elsewhere. The
native proof of possession's `aVal` at the ring input.

Running time: one `computeWApprox` and `O(k N)` UseHint advice computations. This running time
is argued here, not proved in Lean. -/
-- spec-side
noncomputable def aValR (v j : ℕ) : F :=
  if v = 59 then
    (if h : j < 512 then cA y F ⟨j / 2, by change j / 2 < 256; omega⟩ ⟨j % 2, by omega⟩ else 0)
  else if v = 62 then
    (if h : j < 6144 then outputBits (w1A y F) ⟨j / 6, by change j / 6 < 4 * 256; omega⟩
      ⟨j % 6, by change j % 6 < 6; omega⟩ else 0)
  else if h : j < 1024 then
    if v = 58 then (((flat (hintBool y.h) (Native.fm j h)).toNat : ℕ) : F)
    else if v = 60 then (((flat (wCoeff y.key y.c y.z) (Native.fm j h)).val : ℕ) : F)
    else if v = 63 then flat (fun a b => (advice y F a b).s) (Native.fm j h)
    else if v = 575 then ((zN y (Native.fmz j h) % 512 : ℕ) : F)
    else if v = 576 then ((zN y (Native.fmz j h) / 512 : ℕ) : F)
    else if v = 580 then ((offN y (Native.fm j h) % 512 : ℕ) : F)
    else if v = 581 then ((offN y (Native.fm j h) / 512 : ℕ) : F)
    else if v = 582 then ((slN y (Native.fm j h) % 512 : ℕ) : F)
    else if v = 583 then ((slN y (Native.fm j h) / 512 : ℕ) : F)
    else 0
  else 0

end Naturals

/-! ## The honest values at each value -/

section Access

variable (y : RingIn msgLen) (F : Type) [Field F] {j : ℕ}

theorem aValR_58 (h : j < 1024) :
    aValR y F 58 j = (((flat (hintBool y.h) (Native.fm j h)).toNat : ℕ) : F) := by
  unfold aValR
  simp only [show (58 : ℕ) ≠ 59 by decide, show (58 : ℕ) ≠ 62 by decide, if_false, dif_pos h,
    if_true]

theorem aValR_60 (h : j < 1024) :
    aValR y F 60 j = (((flat (wCoeff y.key y.c y.z) (Native.fm j h)).val : ℕ) : F) := by
  unfold aValR
  simp only [show (60 : ℕ) ≠ 59 by decide, show (60 : ℕ) ≠ 62 by decide,
    show (60 : ℕ) ≠ 58 by decide, if_false, dif_pos h, if_true]

theorem aValR_63 (h : j < 1024) :
    aValR y F 63 j = flat (fun a b => (advice y F a b).s) (Native.fm j h) := by
  unfold aValR
  simp only [show (63 : ℕ) ≠ 59 by decide, show (63 : ℕ) ≠ 62 by decide,
    show (63 : ℕ) ≠ 58 by decide, show (63 : ℕ) ≠ 60 by decide, if_false, dif_pos h, if_true]

theorem aValR_59 (h : j < 512) :
    aValR y F 59 j = cA y F ⟨j / 2, by change j / 2 < 256; omega⟩ ⟨j % 2, by omega⟩ := by
  unfold aValR
  rw [if_pos rfl]
  exact dif_pos h

theorem aValR_62 (h : j < 6144) :
    aValR y F 62 j = outputBits (w1A y F) ⟨j / 6, by change j / 6 < 4 * 256; omega⟩
      ⟨j % 6, by change j % 6 < 6; omega⟩ := by
  unfold aValR
  rw [if_neg (by decide), if_pos rfl]
  exact dif_pos h

/-- **The digits of domain `A`** at a coefficient. -/
theorem aValR_digits (h : j < 1024) :
    aValR y F 575 j = ((zN y (Native.fmz j h) % 512 : ℕ) : F) ∧
    aValR y F 576 j = ((zN y (Native.fmz j h) / 512 : ℕ) : F) ∧
    aValR y F 580 j = ((offN y (Native.fm j h) % 512 : ℕ) : F) ∧
    aValR y F 581 j = ((offN y (Native.fm j h) / 512 : ℕ) : F) ∧
    aValR y F 582 j = ((slN y (Native.fm j h) % 512 : ℕ) : F) ∧
    aValR y F 583 j = ((slN y (Native.fm j h) / 512 : ℕ) : F) := by
  unfold aValR
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [dif_pos h, Nat.reduceEqDiff, if_false, if_true]

end Access

/-! ## UseHint, the norm and the weight at the honest naturals -/

section Facts

variable (y : RingIn msgLen)

/-- **The honest UseHint advice passes** at coefficient `m` (`UseHint.native_complete` at one
digit of base `T^2`), with the honest output bits read from `w1Encode(w1)`
(`NativeAlgebraCircuit.Honest.outputBits_honest`). -/
theorem useHint_ring (F : Type) [Field F] [DecidableEq F] [CharP F _root_.MLDSA.modulus]
    (m : Fin MLDSA44.Native.Params.wDim) :
    MLDSA44.Native.UseHintHolds (((flat (hintBool y.h) m).toNat : ℕ) : F)
      (((flat (wCoeff y.key y.c y.z) m).val : ℕ) : F)
      (flat (fun a b => (advice y F a b).s) m) (((offN y m : ℕ) : F)) (((slN y m : ℕ) : F))
      (outputBits (w1A y F) m) := by
  obtain ⟨hok, -⟩ := UseHint.native_complete (K := F) (γ₂ := γ₂) (B := T * T) (k := 1)
    (r := r1Bits) (by decide) (by decide) (by decide) (by decide)
    (flat (hintBool y.h) m) (flat (wCoeff y.key y.c y.z) m)
  obtain ⟨hle, -, hint, hdec⟩ := UseHint.native_ok_iff.mp hok
  have hbits : outputBits (w1A y F) m =
      (UseHint.honest (K := F) γ₂ (T * T) 1 r1Bits (flat (hintBool y.h) m)
        (flat (wCoeff y.key y.c y.z) m)).bits :=
    MLDSA44.NativeAlgebraCircuit.Honest.outputBits_honest y.key y.c y.z y.h m
  rw [MLDSA44.Native.reconstruct_fin_one, MLDSA44.Native.reconstruct_fin_one] at hint
  rw [MLDSA44.Native.reconstruct_fin_one] at hdec
  rw [hbits]
  exact ⟨hle, hint, hdec⟩

/-- An honest centered `z` coefficient is below `γ₁ − β` in magnitude (Algorithm 8's norm
check, `RingIn.checks`). -/
theorem zCentered_natAbs_lt (j : Fin MLDSA44.Native.Params.nCols) (k : Fin MLDSA44.Native.Params.N) :
    (zCentered y.z j k).natAbs < MLDSA44.Native.Params.normBound :=
  (MLDSA44.natAbs_centeredRepr_le_polyVecNorm y.z j k).trans_lt y.checks.1

theorem zN_le (m : Fin (MLDSA44.Native.Rows.nCols * MLDSA44.Native.Rows.deg)) : zN y m ≤ 261986 := by
  unfold zN flat
  dsimp only
  have := zCentered_natAbs_lt y (finProdFinEquiv.symm m).1 (finProdFinEquiv.symm m).2
  change _ < 130994 at this
  omega

theorem zN_cast (F : Type) [Field F] (m : Fin (MLDSA44.Native.Rows.nCols * MLDSA44.Native.Rows.deg)) :
    ((zN y m : ℕ) : F) = ((flat (zCentered y.z) m : ℤ) : F) + ((130993 : ℕ) : F) := by
  unfold zN flat
  have := zCentered_natAbs_lt y (finProdFinEquiv.symm m).1 (finProdFinEquiv.symm m).2
  change _ < 130994 at this
  have h0 : 0 ≤ zCentered y.z (finProdFinEquiv.symm m).1 (finProdFinEquiv.symm m).2 + 130993 := by
    omega
  rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]
  push_cast
  ring

theorem wtN_le : wtN y ≤ 80 := by
  have h := MLDSA44.NativeAlgebraCircuit.Honest.card_hintBool_le y.h y.checks.2.2
  unfold wtN
  rw [Finset.card_filter] at h
  refine le_of_eq_of_le (Finset.sum_congr rfl fun m _ => ?_) h
  cases flat (hintBool y.h) m <;> rfl

theorem offN_lt (m : Fin (MLDSA44.Native.Rows.nRows * MLDSA44.Native.Rows.deg)) : offN y m < 262144 :=
  Nat.mod_lt _ (by norm_num [T])

theorem slN_lt (m : Fin (MLDSA44.Native.Rows.nRows * MLDSA44.Native.Rows.deg)) : slN y m < 262144 :=
  Nat.mod_lt _ (by norm_num [T])

/-- The honest challenge is ternary. -/
theorem c_ternary (k : Fin MLDSA44.Native.Params.N) : y.c k = 0 ∨ y.c k = 1 ∨ y.c k = -1 :=
  MLDSA44.PoP.challenge_ternary _ _ k

end Facts

/-! ## The gadget predicates at an environment reading the honest values -/

section Holds

variable {program : RealizedProgram} [Native.MldsaAAlgebra program] {F0 FH : FieldInterp} [QField F0]
  [HField FH] [hN : Native.MldsaNativeHonest program F0 FH]

set_option hygiene false in
local notation "interp" => mldsaInterpOf F0 FH

open Native.MldsaNativeHonest

/-- **An environment of a native ML-DSA program reads domain `A`'s honest values** of a ring
input: its committed values of domain `A` (`AValues`) read `aValR`, and its bound values `z`
(`57`), the offset (`64`) and the slack (`65`) read their expressions. -/
structure ReadsA (e : program.Env interp) (y : RingIn msgLen) : Prop where
  /-- The committed values read the honest values. -/
  cells : ∀ v ∈ Native.AValues, ∀ j < (program.value v).size, Native.rdA e v j = aValR y F0.K v j
  /-- The bound values read their expressions. -/
  bound : ∀ v E, (program.value v).kind = .bound E → v ∈ [57, 64, 65] → ∀ j,
    Native.rdA e v j = program.evalE (program.reader e) 0 E j

variable {y : RingIn msgLen} {e : program.Env interp} (hr : ReadsA e y)
include hr

/-- **The offset reads its digits' sum**: the honest offset. -/
theorem rdA_65 {m : ℕ} (hm : m < 1024) :
    Native.rdA e 64 m = ((offN y (Native.fm m hm) : ℕ) : (interp 0).K) := by
  obtain ⟨-, h65, -⟩ := (Native.MldsaNativeHonest.a_kinds (program := program))
  obtain ⟨-, -, -, -, -, -, hs, -⟩ := (Native.MldsaNativeHonest.a_bound (program := program))
  rw [hr.bound 64 _ h65 (by simp), evalE_add, evalE_scale_const, Native.decode_fq6 (by norm_num)]
  change Native.rdA _ 580 m + _ * Native.rdA _ 581 m = _
  rw [hr.cells 580 (by decide) m (by rw [hs 580 (by decide)]; exact hm),
    hr.cells 581 (by decide) m (by rw [hs 581 (by decide)]; exact hm),
    (aValR_digits y F0.K hm).2.2.1, (aValR_digits y F0.K hm).2.2.2.1]
  rw [← Nat.cast_mul, ← Nat.cast_add]
  congr 1
  omega

/-- **The slack reads its digits' sum**: the honest slack. -/
theorem rdA_66 {m : ℕ} (hm : m < 1024) :
    Native.rdA e 65 m = ((slN y (Native.fm m hm) : ℕ) : (interp 0).K) := by
  obtain ⟨-, -, h66⟩ := (Native.MldsaNativeHonest.a_kinds (program := program))
  obtain ⟨-, -, -, -, -, -, hs, -⟩ := (Native.MldsaNativeHonest.a_bound (program := program))
  rw [hr.bound 65 _ h66 (by simp), evalE_add, evalE_scale_const, Native.decode_fq6 (by norm_num)]
  change Native.rdA _ 582 m + _ * Native.rdA _ 583 m = _
  rw [hr.cells 582 (by decide) m (by rw [hs 582 (by decide)]; exact hm),
    hr.cells 583 (by decide) m (by rw [hs 583 (by decide)]; exact hm),
    (aValR_digits y F0.K hm).2.2.2.2.1, (aValR_digits y F0.K hm).2.2.2.2.2]
  rw [← Nat.cast_mul, ← Nat.cast_add]
  congr 1
  omega

/-- **The UseHint output bits read the honest output bits.** -/
theorem bitsA_ring {m : ℕ} (hm : m < 1024) :
    Native.bitsA e m = outputBits (w1A y F0.K) (Native.fm m hm) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h63, -⟩ := (Native.MldsaNativeHonest.a_bound (program := program))
  funext b
  have hb := b.isLt
  change (b : ℕ) < 6 at hb
  unfold Native.bitsA
  rw [hr.cells 62 (by decide) _ (by rw [h63]; omega), aValR_62 y F0.K (by omega)]
  have e1 : (⟨(6 * m + b) / 6, by change (6 * m + b) / 6 < 4 * 256; omega⟩ :
      Fin (MLDSA44.Native.Rows.nRows * MLDSA44.Native.Rows.deg)) = Native.fm m hm :=
    Fin.ext (by simp only [Native.fm]; omega)
  have e2 : (⟨(6 * m + b) % 6, by change (6 * m + b) % 6 < 6; omega⟩ : Fin mldsa44.r1_bits) = b :=
    Fin.ext (by simp only; omega)
  rw [e1, e2]

theorem w1Bits_bool : ∀ m < 1024, ∀ t < 6, Native.rdA e 62 (6 * m + t) = 0 ∨ Native.rdA e 62 (6 * m + t) = 1 :=
  fun m hm t ht => by
    have h := congrFun (bitsA_ring hr hm) ⟨t, ht⟩
    unfold Native.bitsA at h
    rw [h]
    unfold outputBits w1A
    exact Falcon512.HashCircuit.wiresOfByteVec_allBool _ _

theorem useHint_at {m : ℕ} (hm : m < 1024) :
    MLDSA44.Native.UseHintHolds (Native.rdA e 58 m) (Native.rdA e 60 m) (Native.rdA e 63 m) (Native.rdA e 64 m) (Native.rdA e 65 m)
      (Native.bitsA e m) := by
  obtain ⟨-, -, -, -, -, -, -, h59, -, h61, -, h64, -⟩ := (Native.MldsaNativeHonest.a_bound (program := program))
  rw [hr.cells 58 (by decide) m (by rw [h59]; exact hm), hr.cells 60 (by decide) m (by rw [h61]; exact hm),
    hr.cells 63 (by decide) m (by rw [h64]; exact hm), rdA_65 hr hm, rdA_66 hr hm, bitsA_ring hr hm,
    aValR_58 y F0.K hm, aValR_60 y F0.K hm, aValR_63 y F0.K hm]
  exact useHint_ring y (interp 0).K (Native.fm m hm)

/-- **`hint.w1_bound` holds** at the honest values. -/
theorem w1bound_ring : program.HoldsWith (program.reader e) (program.predicate 1).body :=
  MLDSA44.w1bound1_of _ (w1Bits_bool hr) fun _ hm => (useHint_at hr hm).le

/-- **`hint.decompose` holds** at the honest values. -/
theorem decompose_ring : program.HoldsWith (program.reader e) (program.predicate 2).body :=
  MLDSA44.decompose2_of (w1Bits_bool hr) fun _ hm => (useHint_at hr hm).decompose

theorem h59_bool : ∀ m < 1024, Native.rdA e 58 m = 0 ∨ Native.rdA e 58 m = 1 := fun m hm => by
  obtain ⟨-, -, -, -, -, -, -, h59, -⟩ := (Native.MldsaNativeHonest.a_bound (program := program))
  rw [hr.cells 58 (by decide) m (by rw [h59]; exact hm), aValR_58 y F0.K hm]
  cases flat (hintBool y.h) (Native.fm m hm) <;> simp

theorem h64_bool : ∀ m < 1024, Native.rdA e 63 m = 0 ∨ Native.rdA e 63 m = 1 := fun m hm => by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h64, -⟩ := (Native.MldsaNativeHonest.a_bound (program := program))
  rw [hr.cells 63 (by decide) m (by rw [h64]; exact hm), aValR_63 y F0.K hm]
  change ((MLDSA44.useHintSign γ₂ _).toNat : F0.K) = 0 ∨ ((MLDSA44.useHintSign γ₂ _).toNat : F0.K) = 1
  cases MLDSA44.useHintSign γ₂ _ <;> simp

theorem h60_bool : ∀ s < 512, Native.rdA e 59 s = 0 ∨ Native.rdA e 59 s = 1 := fun s hs => by
  obtain ⟨-, -, -, -, -, -, -, -, h60, -⟩ := (Native.MldsaNativeHonest.a_bound (program := program))
  rw [hr.cells 59 (by decide) s (by rw [h60]; exact hs), aValR_59 y F0.K hs]
  unfold cA
  rcases Nat.mod_two_eq_zero_or_one s with h | h
  · simp only [h]
    exact (MLDSA44.Native.ternaryBits_bool _).1
  · simp only [h]
    exact (MLDSA44.Native.ternaryBits_bool _).2

theorem offset_nat : ∀ m < 1024, ∃ k : ℕ, k < 262144 ∧ Native.rdA e 64 m = k :=
  fun m hm => ⟨_, offN_lt y (Native.fm m hm), rdA_65 hr hm⟩

theorem slack_nat : ∀ m < 1024, ∃ k : ℕ, k < 262144 ∧ Native.rdA e 65 m = k :=
  fun m hm => ⟨_, slN_lt y (Native.fm m hm), rdA_66 hr hm⟩

/-- **`hint.interval` holds** at the honest values. -/
theorem interval_ring : program.HoldsWith (program.reader e) (program.predicate 3).body :=
  MLDSA44.interval3_of _ (w1Bits_bool hr) (h59_bool hr) (h64_bool hr)
    (offset_nat hr) (slack_nat hr) fun _ hm => (useHint_at hr hm).interval

/-- **`hint.offset` holds** at the honest values. -/
theorem offset_ring : program.HoldsWith (program.reader e) (program.predicate 12).body :=
  MLDSA44.offset12_of _ (offset_nat hr)

/-- **`hint.slack` holds** at the honest values. -/
theorem slack_ring : program.HoldsWith (program.reader e) (program.predicate 13).body :=
  MLDSA44.slack13_of _ (slack_nat hr)

/-- **The type checks of `A` hold** at the honest values (`h`, `c`, `w1`, the signs). -/
theorem bools_ring {q : ℕ} (hq : q ∈ [6, 7, 8, 9]) :
    program.HoldsWith (program.reader e) (program.predicate q).body := by
  obtain ⟨-, -, -, -, -, -, -, h59, h60, -, h63, h64, -⟩ := (Native.MldsaNativeHonest.a_bound (program := program))
  obtain ⟨b6, b7, b8, b9⟩ := MLDSA44.Native.boolChecks (program := program)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact MLDSA44.boolA_of _ b6 fun j hj => h59_bool hr j (h59 ▸ hj)
  · exact MLDSA44.boolA_of _ b7 fun j hj => h60_bool hr j (h60 ▸ hj)
  · refine MLDSA44.boolA_of _ b8 fun j hj => ?_
    rw [h63] at hj
    have := w1Bits_bool hr (j / 6) (by omega) (j % 6) (by omega)
    rwa [Nat.div_add_mod] at this
  · exact MLDSA44.boolA_of _ b9 fun j hj => h64_bool hr j (h64 ▸ hj)

/-- **`z` reads its centered coefficient** at the honest values. -/
theorem rdA_58 {m : ℕ} (hm : m < 1024) :
    Native.rdA e 57 m = ((flat (zCentered y.z) (Native.fmz m hm) : ℤ) : (interp 0).K) := by
  obtain ⟨h58, -, -⟩ := (Native.MldsaNativeHonest.a_kinds (program := program))
  obtain ⟨-, -, -, -, -, -, hs, -⟩ := (Native.MldsaNativeHonest.a_bound (program := program))
  rw [hr.bound 57 _ h58 (by simp), evalE_add, evalE_add, evalE_scale_const, evalE_scale_const,
    Native.decode_fq6 (by norm_num), Native.decode_fq6 (by norm_num)]
  change Native.rdA _ 575 m + _ * Native.rdA _ 576 m + _ * Native.rdA _ 61 m = _
  rw [hr.cells 575 (by decide) m (by rw [hs 575 (by decide)]; exact hm),
    hr.cells 576 (by decide) m (by rw [hs 576 (by decide)]; exact hm),
    MLDSA44.Native.rdA_62 _ hm, (aValR_digits y F0.K hm).1, (aValR_digits y F0.K hm).2.1]
  have hz := zN_cast y F0.K (Native.fmz m hm)
  have hd : ((zN y (Native.fmz m hm) % 512 : ℕ) : (interp 0).K) + ((512 : ℕ) : (interp 0).K) *
      ((zN y (Native.fmz m hm) / 512 : ℕ) : (interp 0).K) = ((zN y (Native.fmz m hm) : ℕ) : (interp 0).K) := by
    rw [← Nat.cast_mul, ← Nat.cast_add]
    congr 1
    omega
  have hq : ((8380417 : ℕ) : (interp 0).K) = 0 := CharP.cast_eq_zero _ _
  push_cast at hz hd hq ⊢
  linear_combination hd + hz + 130993 * hq

/-- **`norm.z` holds** at the honest values. -/
theorem norm_ring : program.HoldsWith (program.reader e) (program.predicate 11).body :=
  MLDSA44.norm11_of _ fun m hm => ⟨zN y (Native.fmz m hm), by
    have := zN_le y (Native.fmz m hm); omega, by rw [rdA_58 hr hm, zN_cast]⟩

/-- **`hint_weight.weight` holds** at the honest values. -/
theorem weight_ring : program.HoldsWith (program.reader e) (program.predicate 14).body := by
  obtain ⟨-, -, -, -, -, -, -, h59, -⟩ := (Native.MldsaNativeHonest.a_bound (program := program))
  refine MLDSA44.weight14_of _ ⟨wtN y, by have := wtN_le y; omega, ?_⟩
  unfold wtN
  rw [Nat.cast_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [hr.cells 58 (by decide) t (by rw [h59]; exact t.isLt), aValR_58 y F0.K t.isLt]
  rfl

/-- **Domain `A`'s gadget predicates hold** at an environment reading the honest values: the
predicates of `GordieHowe.MLDSA44.Ring.Native.aSource` (`1, 2, 3, 6 … 9, 11 … 14`). -/
theorem aPreds_ring {q : ℕ} (hq : q ∈ [1, 2, 3, 6, 7, 8, 9, 11, 12, 13, 14]) :
    program.HoldsWith (program.reader e) (program.predicate q).body := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact w1bound_ring hr
  · exact decompose_ring hr
  · exact interval_ring hr
  · exact bools_ring hr (by simp)
  · exact bools_ring hr (by simp)
  · exact bools_ring hr (by simp)
  · exact bools_ring hr (by simp)
  · exact norm_ring hr
  · exact offset_ring hr
  · exact slack_ring hr
  · exact weight_ring hr

end Holds

end GordieHowe.MLDSA44.Ring.Native
