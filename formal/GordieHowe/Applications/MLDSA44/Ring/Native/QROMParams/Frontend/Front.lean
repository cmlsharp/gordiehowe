-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Generated.MLDSA44.Native.QROMParams.Interp
public import GordieHowe.Applications.MLDSA44.Ring.Native.Frontend.Basic
public import GordieHowe.Applications.MLDSA44.Ring.Native.QROMParams.Frontend.Embed
public import GordieHowe.Applications.MLDSA44.Ring.Native.QROMParams.Frontend.RelationFacts
public import GordieHowe.Applications.MLDSA44.Ring.Native.QROMParams.Frontend.Table
public import GordieHowe.Applications.MLDSA44.Native.QROMParams.Frontend.Basic
public import GordieHowe.Applications.MLDSA44.Native.QROMParams.Frontend.Shape
public import GordieHowe.Generated.MLDSA44.Ring.Native.QROMParams.Interp

@[expose] public section

/-!
# GordieHowe frontend: `MLDSA44.Ring.Native.QROMParams`, the frontend's facts and its soundness

The program facts of the native ML-DSA-44 ring program's frontend at the QROM parameters
(`GordieHowe.Generated.MLDSA44.Ring.Native.QROMParams.Program.program`), decided here:
`MldsaRingStmt` (`ring.keys` value `52`, `ring.mu` value `53`; the frontend does not read `ring.tr`,
value `51`), `MldsaRingFront` (`member.mu` `56`, `h` `60`, `hint.w1` `64`, domain `H`'s `mu` `69`
and `w1` `71`, the crossing `mac.equal` of the shared expressions `513` and `50`), and the native
program's `MldsaAAlgebra`, `MldsaHSample`, `MldsaHHashCore`, `MldsaHConsts` and `MldsaHConstsSelect`
at the native program the ring holds. With the native frontend's hash view
(`MLDSA44.hashViewCore`) and SampleInBall's view (`MLDSA44.sampleView`, at the
native program at the QROM parameters), `source_rbr_knowledge_soundness` is the frontend's
round-by-round knowledge soundness of `Π_P₀` (`Ring.Native.rbr_of_views`).
-/

namespace GordieHowe.MLDSA44.Ring.Native.QROMParams

open Generated.MLDSA44.Ring.Native.QROMParams.Program RealizedProgram IOP

/-- The native ML-DSA ring program at the ROM parameters has the statement values' facts. -/
instance : MldsaRingStmt program where
  keys := 52
  mu := 53
  keysKind := rfl
  muKind := rfl
  fields := by decide +kernel
  keys_ne := by decide

/-- The native program the ring holds has domain `A`'s facts. -/
instance : MLDSA44.Native.MldsaAAlgebra (MldsaRingEmbed.nat program) :=
  inferInstanceAs (MLDSA44.Native.MldsaAAlgebra nat)

/-- The native program the ring holds has SampleInBall's facts. -/
instance : MLDSA44.MldsaHSample (MldsaRingEmbed.nat program) :=
  inferInstanceAs (MLDSA44.MldsaHSample nat)

/-- The native program the ring holds has the hash core's facts. -/
instance : MLDSA44.MldsaHHashCore (MldsaRingEmbed.nat program) :=
  inferInstanceAs (MLDSA44.MldsaHHashCore nat)

/-- The native program the ring holds has the memory check's constants in `GF(2^256)`. -/
instance : MLDSA44.MldsaHConsts (MldsaRingEmbed.nat program)
    RealizedProgram.gf256 :=
  inferInstanceAs (MLDSA44.MldsaHConsts nat RealizedProgram.gf256)

/-- The native program the ring holds has the selection's constants in `GF(2^256)`. -/
instance : MLDSA44.MldsaHConstsSelect (MldsaRingEmbed.nat program)
    RealizedProgram.gf256 :=
  inferInstanceAs (MLDSA44.MldsaHConstsSelect nat RealizedProgram.gf256)

/-! The crossing's index maps: `x` reads `μ ‖ w1` below `6656`, then the support and the sign of
each coefficient alternately; `y` reads its parts in order. -/

theorem idx163_lo' : ∀ a < 104, ∀ b < 64, idx163.entry (64 * a + b) = 64 * a + b := by
  decide +kernel
theorem idx163_lo : ∀ t < 6656, idx163.entry t = t := fun t ht => by
  have h := idx163_lo' (t / 64) (by omega) (t % 64) (by omega)
  rwa [Nat.div_add_mod] at h
theorem idx163_even : ∀ k < 256, idx163.entry (6656 + 2 * k) = 6656 + k := by decide +kernel
theorem idx163_odd : ∀ k < 256, idx163.entry (6656 + (2 * k + 1)) = 6912 + k := by decide +kernel
theorem idx106_eq : idx106 = [(0, 1, 7168)] := by decide +kernel

/-- The challenge facts of the ring and the native program. -/
theorem chalLens : program.challenges.length = 5 ∧ nat.challenges.length = 4 := by decide +kernel

set_option maxRecDepth 8192 in
/-- The native ML-DSA ring program at the ROM parameters has the frontend's facts. -/
instance : MldsaRingFront program where
  muA := 56
  hA := 60
  w1A := 64
  muH := 69
  w1H := 71
  shape := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  domains := by decide +kernel
  lt513 := by decide +kernel
  expr0 := rfl
  expr1 := rfl
  muSize := by decide +kernel
  muBool := by decide +kernel
  cross := ⟨by decide +kernel, by decide +kernel, _, rfl⟩
  exprH := ⟨idx163, rfl, idx163_lo, idx163_even, idx163_odd⟩
  exprA := ⟨idx106, rfl, fun t ht => by rw [idx106_eq, IndexMap.entry_step_one ht, Nat.zero_add]⟩
  lens := by decide +kernel
  bitViews := by decide +kernel
  vals := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  typedCore := by decide +kernel
  chalSucc _ := rfl
  chal0 := by decide +kernel
  chalIff j := by
    rcases lt_or_ge j 4 with hj | hj
    · interval_cases j <;> decide +kernel
    · refine iff_of_false (fun h => ?_) (fun h => ?_)
      · have h1 : j + 1 < program.challenges.length := h.1
        rw [chalLens.1] at h1
        omega
      · have h1 : j < nat.challenges.length := h.1
        rw [chalLens.2] at h1
        omega
  chalShape j hj := by
    have hj4 : j < 4 := lt_of_lt_of_eq hj.1 chalLens.2
    revert hj
    interval_cases j <;> decide +kernel
  projReads := by decide +kernel

open Generated.MLDSA44.Native.QROMParams (interp)

/-- **Round-by-round knowledge soundness of `Π_P₀` for `MLDSA44.Ring.Native.QROMParams`**
(`Ring.Native.rbr_of_views` at the native frontend's `sampleView` and `hashViewCore`): the
relation `Ring.Native.rel`, the extractor `Ring.Native.extractor` and the errors
`Ring.Native.ringEps` (`5143/|F_q^11|` at `member.table.gamma`, SampleInBall's `264/2^256` and
`295/2^256` at the ring's challenges `1`, `2`). -/
theorem source_rbr_knowledge_soundness :
    rbrKnowledgeSoundness (rel (program := program) (F0 := RealizedProgram.fq11)
        (FH := RealizedProgram.gf256)) (program.sourceVerifier interp) extractor
      (program.eventState interp rel proj (ringEvent MLDSA44.sampleView)
        (ringEvent_use MLDSA44.sampleView)
        (sound_of_views MLDSA44.sampleView
          MLDSA44.hashViewCore))
      (program.roundError interp (ringEps (program := program) (F0 := RealizedProgram.fq11)
        (FH := RealizedProgram.gf256) MLDSA44.sampleView)) :=
  rbr_of_views MLDSA44.sampleView MLDSA44.hashViewCore

end GordieHowe.MLDSA44.Ring.Native.QROMParams
