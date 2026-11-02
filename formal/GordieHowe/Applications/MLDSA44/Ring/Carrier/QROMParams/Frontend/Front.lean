-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Ring.Carrier.Frontend.Basic
public import GordieHowe.Applications.MLDSA44.Ring.Carrier.Frontend.SelSound
public import GordieHowe.Applications.MLDSA44.Ring.Carrier.QROMParams.Frontend.Embed
public import GordieHowe.Applications.MLDSA44.Ring.Carrier.QROMParams.Frontend.RelationFacts
public import GordieHowe.Applications.MLDSA44.Ring.Carrier.QROMParams.Frontend.Table
public import GordieHowe.Applications.MLDSA44.Native.QROMParams.Frontend.Basic
public import GordieHowe.Applications.MLDSA44.Native.QROMParams.Frontend.Shape
public import GordieHowe.Applications.MLDSA44.Emulated.QROMParams.Frontend.Basic
public import GordieHowe.Generated.MLDSA44.Ring.Carrier.QROMParams.Interp

@[expose] public section

/-!
# GordieHowe frontend: `MLDSA44.Ring.Carrier.QROMParams`, the frontend's facts and its soundness

The program facts of the ML-DSA-44 ring carrier's frontend at the QROM parameters
(`GordieHowe.Generated.MLDSA44.Ring.Carrier.QROMParams.Program.program`, fields Goldilocks⁴ and
`GF(2^256)`), decided here: `Native.MldsaRingStmt` (`ring.keys` value `53`, `ring.mu` value `54`;
the frontend does not read `ring.tr`, value `52`), `MldsaCarrierFront` (the record,
`member.mu` `57`, the crossing `mac.equal` of the shared expressions `505` and `42`), the native
program's `MldsaHSample`,
`MldsaHHashCore`, `MldsaHConsts` and `MldsaHConstsSelect` at the native program
whose domain `H` core the carrier holds, and the emulated program's `MldsaEAlgebra` (with its
native program's `MldsaHHash`, `MldsaHSample`, `MldsaHConsts`) at the emulated program whose
domain `A` gadgets the carrier holds. With the native frontend's hash view
(`MLDSA44.hashViewCore`) and SampleInBall's view (`MLDSA44.sampleView`, at the
native program at the QROM parameters), `source_rbr_knowledge_soundness` is the frontend's
round-by-round knowledge soundness of `Π_P₀` (`Ring.Carrier.rbr_of_views`), and `selSound` the
selections' error bound the proof system takes (`Ring.Carrier.selSound_carrier`).
-/

namespace GordieHowe.MLDSA44.Ring.Carrier.QROMParams

open Generated.MLDSA44.Ring.Carrier.QROMParams.Program RealizedProgram IOP

/-- The carrier at the QROM parameters has the statement values' facts. -/
instance : Native.MldsaRingStmt program where
  keys := 53
  mu := 54
  keysKind := rfl
  muKind := rfl
  fields := by decide +kernel
  keys_ne := by decide

/-- The native program the carrier holds has SampleInBall's facts. -/
instance : MLDSA44.MldsaHSample (CarrierHEmbed.nat program) :=
  inferInstanceAs (MLDSA44.MldsaHSample nat)

/-- The native program the carrier holds has the hash core's facts. -/
instance : MLDSA44.MldsaHHashCore (CarrierHEmbed.nat program) :=
  inferInstanceAs (MLDSA44.MldsaHHashCore nat)

/-- The native program the carrier holds has the memory check's constants in `GF(2^256)`. -/
instance : MLDSA44.MldsaHConsts (CarrierHEmbed.nat program)
    RealizedProgram.gf256 :=
  inferInstanceAs (MLDSA44.MldsaHConsts nat RealizedProgram.gf256)

/-- The native program the carrier holds has the selection's constants in `GF(2^256)`. -/
instance : MLDSA44.MldsaHConstsSelect (CarrierHEmbed.nat program)
    RealizedProgram.gf256 :=
  inferInstanceAs (MLDSA44.MldsaHConstsSelect nat RealizedProgram.gf256)

/-- The emulated program the carrier holds has domain `A`'s facts. -/
instance : Emulated.MldsaEAlgebra (CarrierAEmbed.emu program) :=
  inferInstanceAs (Emulated.MldsaEAlgebra emu)

/-- The emulated program's native program has the hash's facts. -/
instance : MLDSA44.MldsaHHash
    (Emulated.MldsaEmbed.nat (CarrierAEmbed.emu program)) :=
  inferInstanceAs (MLDSA44.MldsaHHash (Emulated.MldsaEmbed.nat emu))

/-- The emulated program's native program has SampleInBall's facts. -/
instance : MLDSA44.MldsaHSample
    (Emulated.MldsaEmbed.nat (CarrierAEmbed.emu program)) :=
  inferInstanceAs (MLDSA44.MldsaHSample (Emulated.MldsaEmbed.nat emu))

/-- The emulated program's native program has the memory check's constants in `GF(2^256)`. -/
instance : MLDSA44.MldsaHConsts
    (Emulated.MldsaEmbed.nat (CarrierAEmbed.emu program)) RealizedProgram.gf256 :=
  inferInstanceAs
    (MLDSA44.MldsaHConsts (Emulated.MldsaEmbed.nat emu) RealizedProgram.gf256)

/-! The crossing's index maps: `x` reads `μ ‖ w1` below `6656`, then the support and the sign of
each coefficient alternately; `y` reads its parts in order. -/

theorem idx161_lo' : ∀ a < 104, ∀ b < 64, idx161.entry (64 * a + b) = 64 * a + b := by
  decide +kernel
theorem idx161_lo : ∀ t < 6656, idx161.entry t = t := fun t ht => by
  have h := idx161_lo' (t / 64) (by omega) (t % 64) (by omega)
  rwa [Nat.div_add_mod] at h
theorem idx161_even : ∀ k < 256, idx161.entry (6656 + 2 * k) = 6656 + k := by decide +kernel
theorem idx161_odd : ∀ k < 256, idx161.entry (6656 + (2 * k + 1)) = 6912 + k := by decide +kernel
theorem idx104_eq : idx104 = [(0, 1, 7168)] := by decide +kernel

/-- The challenge facts of the carrier and the native program. -/
theorem chalLens : program.challenges.length = 5 ∧ nat.challenges.length = 4 := by decide +kernel

set_option maxRecDepth 8192 in
/-- The carrier at the QROM parameters has the frontend's facts. -/
instance : MldsaCarrierFront program where
  shape := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  domains := by decide +kernel
  lt505 := by decide +kernel
  expr0 := rfl
  expr1 := rfl
  muSize := by decide +kernel
  muBool := by decide +kernel
  cross := ⟨by decide +kernel, by decide +kernel, _, rfl⟩
  exprH := ⟨idx161, rfl, idx161_lo, idx161_even, idx161_odd⟩
  expr504 := rfl
  exprA := ⟨idx104, rfl, fun t ht => by rw [idx104_eq, IndexMap.entry_step_one ht, Nat.zero_add]⟩
  lens := by decide +kernel
  bitViews := by decide +kernel
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

open Generated.MLDSA44.Emulated.QROMParams (interp)

/-- **The selections' error** (`RealizedProgram.SelSound`): the one selection the product form's
kernel reads is `carrierSel`, whose event implies the public table's event
(`Ring.Carrier.selSound_carrier`; the selections, the reads and the selection error decided). -/
theorem selSound : program.SelSound interp :=
  selSound_carrier (by decide +kernel) Generated.MLDSA44.Ring.Carrier.QROMParams.Valid.wellFormed rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- **Round-by-round knowledge soundness of `Π_P₀` for `MLDSA44.Ring.Carrier.QROMParams`**
(`Ring.Carrier.rbr_of_views` at the native frontend's `sampleView` and `hashViewCore`): the
relation `Ring.Carrier.rel`, the extractor `Ring.Carrier.extractor` and the errors
`Ring.Carrier.ringEps` (`5143/|Goldilocks⁴|` at `member.table.gamma`, SampleInBall's `264/2^256` and
`295/2^256` at the carrier's challenges `1`, `2`). -/
theorem source_rbr_knowledge_soundness :
    rbrKnowledgeSoundness (rel (program := program) (F0 := RealizedProgram.gold4)
        (FH := RealizedProgram.gf256)) (program.sourceVerifier interp) extractor
      (program.eventState interp rel proj (ringEvent MLDSA44.sampleView)
        (ringEvent_use MLDSA44.sampleView)
        (sound_of_views MLDSA44.sampleView
          MLDSA44.hashViewCore))
      (program.roundError interp (ringEps (program := program) (F0 := RealizedProgram.gold4)
        (FH := RealizedProgram.gf256) MLDSA44.sampleView)) :=
  rbr_of_views MLDSA44.sampleView MLDSA44.hashViewCore

end GordieHowe.MLDSA44.Ring.Carrier.QROMParams
