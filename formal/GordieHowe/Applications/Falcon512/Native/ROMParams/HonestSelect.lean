-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Native.ROMParams.HonestHash

@[expose] public section

/-!
# GordieHowe: the honest selection of a native Falcon program

The honest values of `h2p.select` (`selVal`): the selected words (`select.raw.words`) the packed
samples of the honest input, the counter and the completion flags the honest route of the
selection model (`Model.hashToPointRoute`) on Falcon's candidate stream, in the selection's field
(`selF`). At the source environment of honest values, the stream is the candidate stream
(`natOfBits_selSample_hash`), so the gadget holds at every `δ` (`SelectFirstN.complete`) and with
it the four predicates (`SelectMatches.holds_of_run`). Generic in the program (`FalconHSelHonest`:
the selection's committed values, decided per program) and the fields.
-/

namespace GordieHowe.Falcon512.Native.ROMParams

open Generated.Falcon512.Native.ROMParams.Program hiding program
open GordieHowe.Bits GordieHowe.Keccak GordieHowe.KeccakTrace

/-- **The selection's committed values** (each program instantiates them by `decide`): the selected
words (`539`) with their bit view (`540`, the identity `idx3` on `512` words), the counter (`541`)
and the completion flags (`542`), committed cells of field `0`. -/
class FalconHSelHonest (program : RealizedProgram) : Prop where
  /-- The selection's committed values, decided. -/
  sel_checks : program.privCellB 539 = true ∧ program.privCellB 541 = true ∧
    program.privCellB 542 = true ∧ program.isBitsB 540 539 idx3 = true ∧
    program.valueField 539 = 0 ∧ program.valueField 540 = 0 ∧ program.valueField 541 = 0 ∧
    program.valueField 542 = 0 ∧ (program.value 539).size = 512 ∧ (program.value 540).size = 8192 ∧
    (program.value 541).size = 639 ∧ (program.value 542).size = 127 ∧ idx3.size = 512 ∧
    (∀ j < 512, idx3.entry j = j) ∧ (program.value 539).type.nodeName = some "GF(2^16)"

open FalconHSelHonest

set_option linter.unusedSectionVars false

variable {program : RealizedProgram} [FalconHHonest program] [FalconHSelHonest program]
  {FH FA : RealizedProgram.FieldInterp} [HField FH] [AField FA] [FalconHBase program]
  [FalconHConsts program FH] [FalconSelField program FH FA]

set_option hygiene false in
local notation "interp" => RealizedProgram.falconInterpOf FH FA

section Values

variable {L : ℕ} (y : Falcon512.PoP.HonestInput L)

/-- **Falcon's candidate stream** of the honest input's nonce and message. -/
-- spec-side
noncomputable def hStream : Fin falcon512.S → ℕ :=
  Falcon512.streamCandidates falcon512 shake256 (List.ofFn y.nonce) (List.ofFn y.message)

variable (program FH FA) in
/-- **The honest route** of the selection: the model's route on the candidate stream, in the
selection's field. -/
-- spec-side
noncomputable def hRoute : Fin 639 → Route (interp (RealizedProgram.SelectShape.field program selShape)).K :=
  SelectFirstN.Model.hashToPointRoute 512 (selF (program := program) (FH := FH) (FA := FA)) 61445
    (hStream y)

variable (program FH FA) in
/-- **The honest values of the selection**: the selected words (value `539`) pack the samples' bits
(`Bits.constBit`), the counter (value `541`) and the completion flags (value `542`) are the honest
route's, read from the selection's field; `0` elsewhere.

Running time: computing these values takes one SHAKE256 call (the stream) and a scan of its `639`
candidates. This running time is argued here, not proved in Lean. -/
-- spec-side
noncomputable def selVal (v i : ℕ) : (interp (program.valueField v)).K :=
  if v = 539 then
    RealizedProgram.castElt (a := 0) (PackedClaim.pack (HField.packing (FH := FH)) fun b =>
      decide (Bits.constBit (K := FH.K) (if h : i < 512 then y.samples ⟨i, h⟩ else 0) b = 1))
  else if v = 541 then RealizedProgram.castElt (a := RealizedProgram.SelectShape.field program selShape)
    (if h : i < 639 then (hRoute program FH FA y ⟨i, h⟩).count_enc else 0)
  else if v = 542 then RealizedProgram.castElt (a := RealizedProgram.SelectShape.field program selShape)
    (if h : i < 127 then (hRoute program FH FA y ⟨512 + i, by omega⟩).full else 0)
  else 0

end Values

/-- **A checked committed value of domain `H` reads its honest values in the selection's field.** -/
theorem evalE_selF {val x : program.Valuation interp} {c : ∀ k, (program.layout interp).Ch k}
    {π : (program.layout interp).Pads} {v : ℕ} (h : program.privCellB v = true)
    (hf : program.valueField v = 0) {z : (interp (RealizedProgram.SelectShape.field program selShape)).K} {i : ℕ}
    (hval : val v i = RealizedProgram.castElt (a := RealizedProgram.SelectShape.field program selShape) z)
    (hi : i < (program.value v).size) :
    program.evalE (program.reader (program.srcEnv interp x val c π))
      (RealizedProgram.SelectShape.field program selShape) (.leaf v) i = z := by
  rw [RealizedProgram.evalE_leaf, RealizedProgram.reader_srcEnv_of_privCellB x val c π h hi, hval]
  exact RealizedProgram.castElt_castElt_of_eq (hf.trans (selField (program := program)).symm).symm z

section Holds

variable {L : ℕ} {y : Falcon512.PoP.HonestInput L} {val x : program.Valuation interp}
  {c : ∀ k, (program.layout interp).Ch k} {π : (program.layout interp).Pads}

/-- **The selected words read the samples' bits** at the source environment. -/
theorem selWord_honest (h : ∀ v ∈ [539, 541, 542], val v = selVal program FH FA y v)
    (j : Fin 512) :
    selWord (program.srcEnv interp x val c π) j =
      fun b : Fin 16 =>
        Bits.constBit (K := (interp (RealizedProgram.SelectShape.field program selShape)).K) (y.samples j) b := by
  obtain ⟨h539, -, -, hb540, hf539, hf540, -, -, hs539, hs540, -, -, hi3, he3, hn539⟩ :=
    sel_checks (program := program)
  funext b
  have hq : ((j : ℕ) * 16 + b) / (8192 / 512) = j := by omega
  have hr : ((j : ℕ) * 16 + b) % (8192 / 512) = b := by omega
  simp only [selWord, RealizedProgram.SelectShape.word, RealizedProgram.wordAt]
  rw [RealizedProgram.evalE_leaf, RealizedProgram.reader_srcEnv_bits x val c π hb540 h539 (by
    rw [hs540, hi3, hq, he3 _ j.isLt, hs539]; exact j.isLt), hs540, hi3, hq, he3 _ j.isLt, hr,
    h 539 (by simp), hn539]
  unfold selVal
  rw [if_pos rfl, dif_pos j.isLt, coord_castElt hf539]
  erw [HField.coord_pack]
  rw [castElt_ofBool (hf540.trans (selField (program := program)).symm)]
  have hb2 : (b : ℕ) % 16 = b := Nat.mod_eq_of_lt b.isLt
  simp only [hb2, Fin.eta]
  generalize hn : y.samples ⟨(j : ℕ), j.isLt⟩ = n
  have hn' : y.samples j = n := hn
  rw [hn']
  unfold RealizedProgram.FieldInterp.ofBool Bits.constBit
  split_ifs <;> simp_all

/-- **The route reads the honest route** at the source environment. -/
theorem selRoute_honest (h : ∀ v ∈ [539, 541, 542], val v = selVal program FH FA y v) :
    selRoute (program.srcEnv interp x val c π) = hRoute program FH FA y := by
  obtain ⟨-, h541, h542, -, -, -, hf541, hf542, -, -, hs541, hs542, -⟩ :=
    sel_checks (program := program)
  funext i
  have e1 : program.evalE (program.reader (program.srcEnv interp x val c π))
      (RealizedProgram.SelectShape.field program selShape) (.leaf 541) i = (hRoute program FH FA y i).count_enc := by
    refine evalE_selF h541 hf541 ?_ (by rw [hs541]; exact i.isLt)
    rw [h 541 (by simp)]
    unfold selVal
    rw [if_neg (by norm_num), if_pos rfl]
    simp only [i.isLt, ↓reduceDIte]
  simp only [selRoute, RealizedProgram.SelectShape.route]
  rw [e1]
  by_cases hi : 512 ≤ (i : ℕ)
  · rw [if_pos hi]
    have e2 : program.evalE (program.reader (program.srcEnv interp x val c π))
        (RealizedProgram.SelectShape.field program selShape) (.leaf 542) (i - 512) =
          (hRoute program FH FA y i).full := by
      refine evalE_selF h542 hf542 ?_ (by rw [hs542]; omega)
      rw [h 542 (by simp)]
      unfold selVal
      rw [if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]
      have hlt : (i : ℕ) - 512 < 127 := by omega
      have hfin : (⟨512 + ((i : ℕ) - 512), by omega⟩ : Fin 639) = i := Fin.ext (by simp only; omega)
      simp only [hlt, ↓reduceDIte, hfin]
    rw [e2]
  · rw [if_neg hi]
    have := SelectFirstN.Model.hashToPointRoute_full_zero 512
      (selF (program := program) (FH := FH) (FA := FA)) 61445 (hStream y) i (by omega)
    exact congrArg (fun f => (⟨(hRoute program FH FA y i).count_enc, f⟩ : Route _)) this.symm

/-- **The honest selection holds**: at the source environment of honest values (`hashVal` on the
hash's inputs, `selVal` on the selection's), the predicates `h2p.select.start`, `.step`, `.done`
and `.route` hold at every `δ`. -/
theorem select_holds (hL : L ≤ 32) (hy : y.Valid)
    (hh : ∀ v, IsHashValue v → val v = hashVal (program := program) y v)
    (hsel : ∀ v ∈ [539, 541, 542], val v = selVal program FH FA y v) :
    program.HoldsAt (program.srcEnv interp x val c π) (program.predicate 246).body ∧
      program.HoldsAt (program.srcEnv interp x val c π) (program.predicate 247).body ∧
      program.HoldsAt (program.srcEnv interp x val c π) (program.predicate 248).body ∧
      program.HoldsAt (program.srcEnv interp x val c π) (program.predicate 249).body := by
  set e := program.srcEnv interp x val c π
  have hs : HashSat e := hashSat_honest hL hh
  have hstream : (fun i => Bits.natOfBits (selSample e i)) = hStream y := by
    funext i
    have := natOfBits_selSample_hash hs i
    rw [(bytes_honest hL hy hh).1, (bytes_honest hL hy hh).2] at this
    exact this
  have hword : (fun j => Bits.natOfBits (selWord e j)) = y.samples := by
    funext j
    rw [selWord_honest hsel, Bits.natOfBits_constBit,
      Nat.mod_eq_of_lt (Emulated.samples_lt hy j)]
  have hout : firstAccepted (fun v => decide (v < 61445)) (fun i => Bits.natOfBits (selSample e i))
      512 = some fun j => Bits.natOfBits (selWord e j) := by
    rw [hstream, hword]
    exact hy.samples
  have hrun := SelectFirstN.complete selF (bound := 61445) (by norm_num)
    (selectMatches.stream_allBool FalconHBase.refsOrdered selConsts e)
    (selectMatches.out_allBool e) hout (selShape.deltaAt program (program.reader e))
  rw [hstream] at hrun
  change SelectFirstN.run (selF (program := program) (FH := FH) (FA := FA)) 61445 _ _
    (hRoute program FH FA y) _ = true at hrun
  rw [← selRoute_honest hsel] at hrun
  exact selectMatches.holds_of_run FalconHBase.refsOrdered selConsts (by norm_num) (by decide) hrun

end Holds

end GordieHowe.Falcon512.Native.ROMParams
