-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Honest.HashVal
public import GordieHowe.Applications.MLDSA44.Honest.Select

@[expose] public section

/-!
# GordieHowe: SampleInBall at the honest values of a native ML-DSA program's domain `H`

The honest stream of a native ML-DSA program's domain `H` (the program's views of the trace) is the
honest stream of `GordieHowe.MLDSA44.PoP.Native` (`GordieHowe.MLDSA44.Native.streamOf`, at domain `H`'s `GordieHowe.MLDSA44.PoP.Native` field data
`GordieHowe.MLDSA44.Native.ROMParams.MldsaHNativeData`), so its candidates select the input's positions (`GordieHowe.MLDSA44.Native.selects_honest`), and
the selection gadget passes at the honest low threshold bits (`SelectFirstTau.complete`); the memory
check passes at the honest memory trace (`SampleInBall.checks_honestCells`). Stated at any
environment reading the honest committed values of domain `H` (`GordieHowe.RealizedProgram.ReadsCells`), so the facts
hold at the source environment of each native program and, read through the renaming, of each
emulated one. The committed cells of SampleInBall are program facts (`MldsaHSelHonest`), decided per
program.
-/

namespace GordieHowe.MLDSA44.Native.ROMParams

open Generated.MLDSA44.Native.ROMParams.Program
open GordieHowe.Bits GordieHowe.Keccak GordieHowe.KeccakTrace

/-- **An honest input of an ML-DSA-44 proof of possession**: a message of at most `32` bytes, its
key, `c̃`, positions and signature (`MLDSA44.PoP.HonestInput`), valid. -/
structure _root_.GordieHowe.MLDSA44.HonestInput where
  /-- The message length. -/
  L : ℕ
  /-- At most `32` bytes. -/
  hL : L ≤ 32
  /-- The input. -/
  y : MLDSA44.PoP.HonestInput 0 L
  /-- The input is valid. -/
  valid : y.Valid

/-- **The honest input of a pair of the paper's relation** `MLDSA44.PoP.relUpTo 32`: the
witness's message length and the honest input `MLDSA44.PoP.HonestInput.ofWitness` of the
statement and the witness, valid by `MLDSA44.PoP.HonestInput.valid_ofWitness`.

Running time: that of `MLDSA44.PoP.HonestInput.ofWitness`. -/
def _root_.GordieHowe.MLDSA44.HonestInput.ofRel (x : MLDSA44.PoP.Statement 0)
    (w : MLDSA44.PoP.VarWitness 32) (h : (x, w) ∈ MLDSA44.PoP.relUpTo 32) : MLDSA44.HonestInput :=
  ⟨w.1, Nat.lt_succ_iff.mp w.1.isLt, MLDSA44.PoP.HonestInput.ofWitness x w.2,
    MLDSA44.PoP.HonestInput.valid_ofWitness h⟩

/-- The honest input of a pair is at the pair's statement. -/
@[simp] theorem _root_.GordieHowe.MLDSA44.HonestInput.ofRel_pk (x : MLDSA44.PoP.Statement 0)
    (w : MLDSA44.PoP.VarWitness 32) (h : (x, w) ∈ MLDSA44.PoP.relUpTo 32) :
    (MLDSA44.HonestInput.ofRel x w h).y.pk = x :=
  rfl

/-- **The program facts of SampleInBall's honest cells** (`MldsaHShuffle` and): the selection's
committed threshold words (`558`, their bit view `559`) and selected bytes (`557`), and the memory
check's committed cells (`561`–`566`), in domain `H`'s field with their sizes. Each native program
instantiates it by `decide`. -/
class MldsaHSelHonest (program : RealizedProgram) : Prop where
  /-- The selection's committed cells. -/
  sel_cells : program.isBitsB 559 558 idx5 = true ∧ program.privCellB 558 = true ∧
    program.valueField 559 = 1 ∧ program.valueField 558 = 1 ∧ (program.value 559).size = 1584 ∧
    (program.value 558).size = 99 ∧ (program.value 558).type.nodeName = some "GF(2^16)" ∧
    RealizedProgram.IndexMap.size idx5 = 99 ∧ (∀ i < 99, idx5.entry i = i) ∧ program.privCellB 557 = true ∧
    program.valueField 557 = 1 ∧ (program.value 557).size = 312
  /-- The memory check's committed cells. -/
  mem_cells : (∀ v ∈ [561, 562, 563, 564, 565, 566], program.privCellB v = true ∧
    program.valueField v = 1) ∧ (program.value 561).size = 39 ∧ (program.value 562).size = 234 ∧
    (program.value 563).size = 256 ∧ (program.value 564).size = 256 ∧
    (program.value 565).size = 39 ∧ (program.value 566).size = 39

set_option maxRecDepth 4096 in
/-- The native program at the ROM parameters has these facts. -/
instance : MldsaHSelHonest program where
  sel_cells := by decide +kernel
  mem_cells := by decide +kernel

/-- **The nodes of domain `H`'s field** the honest values lie in: the selection subfield and the
packed words lie in the node `GF(2^16)`, and the node `bit` is `{0, 1}`. Facts about the field
interpretation, instantiated for `GF(2^128)` and `GF(2^256)`. -/
class MldsaHNodes (FH : RealizedProgram.FieldInterp) [HField FH] : Prop where
  /-- The selection subfield lies in the node `GF(2^16)`. -/
  node_of_sel : ∀ x ∈ (HField.sel (FH := FH)).E, x ∈ FH.node "GF(2^16)"
  /-- A packed word lies in the node `GF(2^16)`. -/
  pack_mem : ∀ b : Fin (2 ^ 4) → Bool, PackedClaim.pack HField.packing b ∈ FH.node "GF(2^16)"
  /-- The node `bit` is `{0, 1}`. -/
  bit_iff : ∀ x : FH.K, x ∈ FH.node "bit" ↔ x = 0 ∨ x = 1

/-- `GF(2^128)`'s nodes. -/
instance : MldsaHNodes RealizedProgram.gf128 where
  node_of_sel _ h := show _ ∈ RelativePacking.fixedField GF2_128 2 16 from
    (RelativePacking.mem_fixedField_iff_pow).2 (mem_gf2_128Subfield.1 h)
  pack_mem b := show _ ∈ RelativePacking.fixedField GF2_128 2 16 from
    (RelativePacking.mem_fixedField_iff_pow).2 (mem_gf2_128Subfield.1
      (PackedClaim.pack_mem gf2_128PackedBasis b))
  bit_iff x := by
    change x ∈ RealizedProgram.gf2Node "bit" ↔ _
    rw [RealizedProgram.gf2Node, if_neg (by decide), if_pos rfl]
    exact RealizedProgram.mem_fixedField_two_one

/-- `GF(2^256)`'s nodes. -/
instance : MldsaHNodes RealizedProgram.gf256 where
  node_of_sel _ h := show _ ∈ RelativePacking.fixedField GF2_256 2 16 from
    (RelativePacking.mem_fixedField_iff_pow).2 (mem_gf2_256Subfield.1 h)
  pack_mem b := show _ ∈ RelativePacking.fixedField GF2_256 2 16 from
    (RelativePacking.mem_fixedField_iff_pow).2 (mem_gf2_256Subfield.1
      (PackedClaim.pack_mem gf2_256PackedBasis b))
  bit_iff x := by
    change x ∈ RealizedProgram.gf256Node "bit" ↔ _
    rw [RealizedProgram.gf256Node, if_neg (by decide), if_pos rfl]
    exact RealizedProgram.mem_fixedField_two_one_iff

set_option linter.unusedSectionVars false

section Defs

variable {FH : RealizedProgram.FieldInterp} [HField FH] [MldsaHNativeData FH]

variable (FH) in
/-- **`Native`'s honest assignment** of an honest input, at domain `H`'s `Native` field
data (its domain-`H` part is the honest hash trace and selection). -/
-- spec-side
noncomputable abbrev nativeH (i : MLDSA44.HonestInput) :=
  Native.honestAssignment (F := MldsaHNativeData.F FH) (MldsaHNativeData.D (FH := FH)).packing i.y

variable (FH) in
/-- **The honest candidates' naturals**: the candidates of `Native`'s honest stream. -/
-- spec-side
noncomputable def candNat (i : MLDSA44.HonestInput) (k : Fin 264) : ℕ :=
  natOfBits (Native.streamOf (MldsaHNativeData.D (FH := FH)) (nativeH FH i) k)

variable (FH) in
/-- **The honest low threshold bits**, flat: bit `b` of position `k` at `6 k + b`. -/
-- spec-side
noncomputable def lowF (i : MLDSA44.HonestInput) (n : ℕ) : FH.K :=
  if h : n < 1584 then constBit (SelectFirstTau.honestThr 39 (candNat FH i) ⟨n / 6, by omega⟩) (n % 6)
  else 0

variable (FH) in
/-- **The honest selected bytes' bits**, flat: bit `b` of step `t` at `8 t + b`. -/
-- spec-side
noncomputable def jF (i : MLDSA44.HonestInput) (n : ℕ) : FH.K :=
  if h : n < 312 then constBit (i.y.positions ⟨n / 8, by change n / 8 < 39; omega⟩) (n % 8) else 0

end Defs

variable {program : RealizedProgram} [MldsaHHonest program] [MldsaHShuffle program]
  [MldsaHSelHonest program] {F0 FH : RealizedProgram.FieldInterp} [HField FH] [MldsaHConsts program FH]
  [MldsaHNativeData FH]

set_option hygiene false in
local notation "interp" => RealizedProgram.mldsaInterpOf F0 FH

variable (program F0 FH) in
/-- SampleInBall's step count is the signature's `τ`. -/
theorem samM_τ_eq : (samM program F0 FH).τ = mldsa44.τ := rfl

variable (program F0 FH) in
/-- **The honest signs**: bits `0 … 38` of `Native`'s honest stream, indexed by SampleInBall's
steps. -/
-- spec-side
noncomputable def sgB (i : MLDSA44.HonestInput) (t : Fin (samM program F0 FH).τ) : Bool :=
  decide (Native.signsOf (MldsaHNativeData.D (FH := FH)) (nativeH FH i)
    (Fin.cast (samM_τ_eq program F0 FH) t) = 1)

variable (program F0 FH) in
/-- **The input's positions**, indexed by SampleInBall's steps. -/
-- spec-side
noncomputable def posN (i : MLDSA44.HonestInput) (t : Fin (samM program F0 FH).τ) : ℕ :=
  i.y.positions (Fin.cast (samM_τ_eq program F0 FH) t)

variable (program F0 FH) in
/-- **The honest memory trace** of SampleInBall's shuffle (`MemoryShuffle.honestWit`) on the
input's positions and the honest signs. -/
-- spec-side
noncomputable def honestMemW (i : MLDSA44.HonestInput) :
    MemoryShuffle.Wit (interp 1).K (samM program F0 FH).N
      (samM program F0 FH).τ :=
  MemoryShuffle.honestWit (samM program F0 FH).field
    (samM program F0 FH).Θ (posN program F0 FH i) (sgB program F0 FH i)

variable (program F0 FH) in
/-- **The honest cells of SampleInBall's memory check**, flat per value (`561`–`566`): the read
values, the read origins' bits, the final cells, the final origins, the units, the origins. -/
-- spec-side
noncomputable def memF (i : MLDSA44.HonestInput) (v n : ℕ) : (interp 1).K :=
  if v = 561 then (if h : n < 39 then ((honestMemW program F0 FH i).read ⟨n, h⟩).value else 0)
  else if v = 562 then
    (if h : n < 234 then ((honestMemW program F0 FH i).read ⟨n / 6, by change n / 6 < 39; omega⟩).origin ⟨n % 6, by omega⟩ else 0)
  else if v = 563 then (if h : n < 256 then (honestMemW program F0 FH i).cEnc ⟨n, h⟩ else 0)
  else if v = 564 then (if h : n < 256 then (honestMemW program F0 FH i).finalOrigin ⟨n, h⟩ else 0)
  else if v = 565 then (if h : n < 39 then
      MemoryShuffle.unit (samM program F0 FH).Θ ((honestMemW program F0 FH i).signs ⟨n, h⟩)
      else 0)
  else if v = 566 then (if h : n < 39 then (samM program F0 FH).originOf
      ((honestMemW program F0 FH i).read ⟨n, h⟩).origin else 0)
  else 0

/-- The honest trace's final cells encode the shuffle (`MemoryShuffle.memoryTrace_cell_eq_shuffle`). -/
theorem honestWit_cEnc {K : Type*} [Field K] [DecidableEq K] [CharP K 2] {S N τ : ℕ}
    (F : SelectionField K S) (Θ : MemoryShuffle.Theta K) (pos : Fin τ → ℕ) (sg : Fin τ → Bool)
    (k : Fin N) :
    (MemoryShuffle.honestWit (N := N) F Θ pos sg).cEnc k =
      MemoryShuffle.encode Θ (MemoryShuffle.shuffle N τ pos sg k) :=
  MemoryShuffle.memoryTrace_cell_eq_shuffle Θ pos sg k

section Agree

variable {i : MLDSA44.HonestInput} {e : program.Env interp} {val : program.Valuation interp}
  (hr : program.ReadsCells 1 e val)
  (hh : ∀ v, IsHashValue v → val v = hashVal (program := program) (F0 := F0) (FH := FH) i.y v)

set_option hygiene false in
local notation "RD" => program.reader e

include hr hh

/-- **The honest candidates are `Native`'s honest stream's.** -/
theorem candBits_honest (k : Fin 264) (b : Fin 8) :
    candBits RD k b = Native.streamOf (MldsaHNativeData.D (FH := FH)) (nativeH FH i) k b := by
  have hk := k.isLt
  have hb := b.isLt
  have hs := sibBits_honest hr hh ⟨8 * (8 + k) + b, by omega⟩
  unfold candBits HashCircuit.candidates sibByte Falcon512.HashCircuit.byteWires
  rw [hs]
  unfold Native.streamOf HashCircuit.candidates Native.sibBytes nativeH
  rw [Native.honestAssignment, sibOut_honest_bit i.y i.hL ⟨8 + k, by change _ < 272; omega⟩ b]
  simp only
  by_cases h136 : 8 + (k : ℕ) < 136
  · rw [if_pos (show 8 * (8 + (k : ℕ)) + b < 1088 by omega), if_pos h136,
      show (8 * (8 + (k : ℕ)) + b) % 1088 = 8 * ((8 + (k : ℕ)) % 136) + b by omega]
  · rw [if_neg (show ¬ (8 * (8 + (k : ℕ)) + b < 1088) by omega), if_neg h136,
      show (8 * (8 + (k : ℕ)) + b) % 1088 = 8 * ((8 + (k : ℕ)) % 136) + b by omega]

set_option maxRecDepth 8192 in
/-- **SampleInBall's selection predicates hold at honest values**: the hash values, the selected
bytes the input's positions (`jF`) and the threshold words the honest low threshold bits packed
(`lowF`). -/
theorem select_holds_honest
    (h557 : ∀ v, v = 557 → ∀ n < 312, RealizedProgram.castElt (b := 1) (val v n) = jF FH i n)
    (h558 : ∀ v, v = 558 → ∀ w < 99, RealizedProgram.castElt (b := 1) (val v w) =
      packWord (FH := FH) (lowF FH i) w)
    {q : ℕ} (hq : q ∈ [264, 265, 266]) :
    program.HoldsWith RD (program.predicate q).body := by
  obtain ⟨hb9, hp8, hf9, hf8, hs9, hs8, hn8, hsel, he, hp7, hf7, hs7⟩ := MldsaHSelHonest.sel_cells (program := program)
  have hc : candBits RD = Native.streamOf (MldsaHNativeData.D (FH := FH)) (nativeH FH i) :=
    funext fun k => funext fun b => candBits_honest hr hh k b
  have hj : jBits RD = (nativeH FH i).j := by
    funext t b
    have ht := t.isLt
    have hb := b.isLt
    unfold jBits
    rw [RealizedProgram.evalE_leaf, hr hp7 hf7 (by rw [hs7]; omega),
      h557 _ rfl _ (by omega)]
    unfold jF
    rw [dif_pos (by omega)]
    change constBit _ _ = constBit _ _
    congr 2
    · exact Fin.ext (show (8 * (t : ℕ) + b) / 8 = t by omega)
    · omega
  have hlow : lowThr RD = SelectFirstTau.honestLow 39 fun k => natOfBits (candBits RD k) := by
    funext k b
    have hk := k.isLt
    have hb : (b : ℕ) < 6 := b.isLt
    unfold lowThr
    have hbool : ∀ n, lowF FH i n = 0 ∨ lowF FH i n = 1 := fun n => by
      unfold lowF
      split_ifs
      · exact constBit_bool _ _
      · exact Or.inl rfl
    rw [evalE_bitview hr hbool hb9 hp8 hf9 hf8 (by rw [hs9]) hs8 hn8 hsel he
      (fun w hw => by rw [← RealizedProgram.castElt_castElt_of_eq (I := interp) hf8 (val 558 w)]; exact congrArg _ (h558 _ rfl w hw)) (by omega)]
    unfold lowF SelectFirstTau.honestLow
    rw [dif_pos (by omega)]
    rw [hc]
    congr 2
    · exact Fin.ext (show (6 * (k : ℕ) + b) / 6 = k by omega)
    · omega
  have hsel' := Native.selects_honest (MldsaHNativeData.D (FH := FH)) i.valid
  have hrun : SelectFirstTau.run selF 39 (candBits RD) (jBits RD) (lowThr RD) (selDelta RD) = true := by
    rw [hlow]
    refine SelectFirstTau.complete selF (by norm_num) (by decide) (fun k => ?_) (fun t => ?_) ?_ _
    · rw [hc]
      exact hsel'.streamBool k
    · rw [hj]
      exact hsel'.outBool t
    · rw [hc, hj]
      exact hsel'.first
  exact select_holds_of_run _ hrun hq

/-- **The honest signs are `Native`'s honest stream's.** -/
theorem signsH_honest (t : Fin 39) :
    signsH RD t = Native.signsOf (MldsaHNativeData.D (FH := FH)) (nativeH FH i) t := by
  have ht : (t : ℕ) < 39 := t.isLt
  have hs := sibBits_honest hr hh ⟨8 * ((t : ℕ) / 8) + (t : ℕ) % 8, by omega⟩
  unfold signsH HashCircuit.signWires sibByte Falcon512.HashCircuit.byteWires
  rw [hs]
  unfold Native.signsOf HashCircuit.signWires Native.sibBytes nativeH
  rw [Native.honestAssignment, sibOut_honest_bit i.y i.hL ⟨(t : ℕ) / 8, by change _ < 272; omega⟩
    ⟨(t : ℕ) % 8, by omega⟩]
  simp only
  rw [if_pos (show 8 * ((t : ℕ) / 8) + (t : ℕ) % 8 < 1088 by omega),
    if_pos (show (t : ℕ) / 8 < 136 by omega),
    show (8 * ((t : ℕ) / 8) + (t : ℕ) % 8) % 1088 = 8 * ((t : ℕ) / 8 % 136) + (t : ℕ) % 8 by omega]

set_option maxRecDepth 8192 in
/-- **SampleInBall's memory check predicates hold at honest values**: the hash values, the selected
bytes, and the memory cells the honest trace's (`memF`). -/
theorem mem_holds_honest (h557 : ∀ v, v = 557 → ∀ n < 312, RealizedProgram.castElt (b := 1) (val v n) = jF FH i n)
    (hm : ∀ v, v ∈ [561, 562, 563, 564, 565, 566] → ∀ n < (program.value v).size,
      RealizedProgram.castElt (b := 1) (val v n) = memF program F0 FH i v n)
    {q : ℕ} (hq : q ∈ [267, 268, 269, 270]) :
    program.HoldsWith RD (program.predicate q).body := by
  obtain ⟨hcell, h1, h2, h3, h4, h5, h6⟩ := MldsaHSelHonest.mem_cells (program := program)
  obtain ⟨-, -, -, -, -, -, -, -, -, hp7, hf7, hs7⟩ := MldsaHSelHonest.sel_cells (program := program)
  have rd : ∀ v, v ∈ [561, 562, 563, 564, 565, 566] → ∀ n < (program.value v).size,
      program.evalE RD 1 (.leaf v) n = memF program F0 FH i v n := fun v hv n hn => by
    rw [RealizedProgram.evalE_leaf, hr (hcell v hv).1 (hcell v hv).2 hn]
    exact hm v hv n hn
  have hjb : ∀ (t : Fin 39) (b : Fin 8), jBits RD t b = constBit (i.y.positions t) b := by
    intro t b
    have ht := t.isLt
    have hb := b.isLt
    unfold jBits
    rw [RealizedProgram.evalE_leaf, hr hp7 hf7 (by rw [hs7]; omega),
      h557 _ rfl _ (by omega)]
    unfold jF
    rw [dif_pos (by omega)]
    congr 2
    · exact Fin.ext (show (8 * (t : ℕ) + b) / 8 = t by omega)
    · omega
  have hlt := fun t => (MLDSA44.acceptedCandidates_le mldsa44 i.valid.positions t)
  have hpos : ∀ t : Fin 39, natOfBits (jBits RD t) = i.y.positions t := fun t => by
    rw [show jBits RD t = fun b : Fin 8 => constBit (K := (interp 1).K) (i.y.positions t) b from
      funext (hjb t),
      natOfBits_constBit, Nat.mod_eq_of_lt]
    have ha := hlt t
    have hb : (t : ℕ) < 39 := t.isLt
    change i.y.positions t ≤ 256 - 39 + (t : ℕ) at ha
    change i.y.positions t < 256
    omega
  have hsgb : ∀ t : Fin 39, Native.signsOf (MldsaHNativeData.D (FH := FH)) (nativeH FH i) t = 0 ∨
      Native.signsOf (MldsaHNativeData.D (FH := FH)) (nativeH FH i) t = 1 := fun t =>
    (Native.hashConstraints_honest (MldsaHNativeData.D (FH := FH)).packing i.y).sibOut_allBool _ _
  have hsg : ∀ t : Fin (samM program F0 FH).τ,
      (samM program F0 FH).signs e t =
        if sgB program F0 FH i t then 1 else 0 := fun t => by
    rw [samM_signs]
    change signsH RD (Fin.cast (samM_τ_eq program F0 FH) t) = _
    rw [signsH_honest hr hh (Fin.cast (samM_τ_eq program F0 FH) t), sgB]
    have key : ∀ z : (interp 1).K, (z = 0 ∨ z = 1) → z = if decide (z = 1) = true then 1 else 0 := by
      intro z hz
      rcases hz with rfl | rfl
      · simp
      · simp
    exact key _ (hsgb (Fin.cast (samM_τ_eq program F0 FH) t))
  have hB : SampleInBall.signBoolsOf
      ((samM program F0 FH).signs e) =
      sgB program F0 FH i := by
    funext t
    unfold SampleInBall.signBoolsOf
    rw [hsg t]
    cases sgB program F0 FH i t <;> simp
  have hP : (fun t => natOfBits
      ((samM program F0 FH).positions e t)) =
      posN program F0 FH i := by
    funext t
    rw [samM_positions]
    exact hpos (Fin.cast (samM_τ_eq program F0 FH) t)
  have hTr : (samM program F0 FH).honestTrace
      e = honestMemW program F0 FH i := by
    unfold SampleInBall.honestTrace honestMemW SampleInBall.signBools
    rw [hP, hB]
  have hL : samLowered e =
      (samM program F0 FH).honestCells e := by
    unfold samLowered SampleInBall.honestCells
    rw [hTr, SampleInBall.Lowered.mk.injEq]
    refine ⟨rfl, funext fun t => ?_, funext fun t => funext fun b => ?_, funext fun k => ?_,
      funext fun k => ?_, funext fun t => ?_, funext fun t => ?_⟩
    · have ht : (t : ℕ) < 39 := t.isLt
      rw [rd 561 (by simp) t (by rw [h1]; exact ht)]
      unfold memF
      rw [if_pos rfl, dif_pos ht]
    · have ht : (t : ℕ) < 39 := t.isLt
      have hb : (b : ℕ) < 6 := b.isLt
      rw [rd 562 (by simp) _ (by rw [h2]; omega)]
      unfold memF
      rw [if_neg (by decide), if_pos rfl, dif_pos (by omega)]
      have e1 : (⟨(6 * (t : ℕ) + b) / 6, by change _ < 39; omega⟩ : Fin (samM program F0 FH).τ) = t := Fin.ext (by simp only; omega)
      have e2 : (⟨(6 * (t : ℕ) + b) % 6, by omega⟩ : Fin 6) = b := Fin.ext (by simp only; omega)
      rw [e1, e2]
    · have hk : (k : ℕ) < 256 := k.isLt
      rw [rd 563 (by simp) k (by rw [h3]; exact hk)]
      unfold memF
      rw [if_neg (by decide), if_neg (by decide), if_pos rfl, dif_pos hk]
    · have hk : (k : ℕ) < 256 := k.isLt
      rw [rd 564 (by simp) k (by rw [h4]; exact hk)]
      unfold memF
      rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl, dif_pos hk]
    · have ht : (t : ℕ) < 39 := t.isLt
      rw [rd 565 (by simp) t (by rw [h5]; exact ht)]
      unfold memF
      rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl,
        dif_pos ht]
      change _ = MemoryShuffle.unit _
        ((samM program F0 FH).signs e t)
      rw [hsg t]
      rfl
    · have ht : (t : ℕ) < 39 := t.isLt
      rw [rd 566 (by simp) t (by rw [h6]; exact ht)]
      unfold memF
      rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
        if_neg (by decide), if_pos rfl, dif_pos ht]
  have hpz : SampleInBall.Positioned 256
      ((samM program F0 FH).positions e)
      ((samM program F0 FH).signs e) := by
    refine ⟨fun t b => ?_, fun t => ?_, fun t => ?_⟩
    · rw [samM_positions, hjb t b]
      exact constBit_bool _ _
    · rw [samM_positions, hpos t]
      exact hlt t
    · rw [hsg t]
      cases sgB program F0 FH i t
      · exact Or.inl rfl
      · exact Or.inr rfl
  have hS : (samM program F0 FH).HonestShuffles
      e := by
    refine ⟨hpz, fun k => ?_⟩
    have hd := decodeRow (program := program) (F0 := F0) (FH := FH)
      e k
    rw [samLowered_base] at hd
    have hk : (k : ℕ) < 256 := k.isLt
    have hce : (samLowered e).cEnc k = (honestMemW program F0 FH i).cEnc k := by
      rw [samLowered_cEnc, rd 563 (by simp) k (by rw [h3]; exact hk)]
      unfold memF
      rw [if_neg (by decide), if_neg (by decide), if_pos rfl, dif_pos hk]
    have hsh : (samM program F0 FH).shuffle e =
        MemoryShuffle.shuffle _ _ (posN program F0 FH i) (sgB program F0 FH i) := by
      unfold SampleInBall.shuffle SampleInBall.shuffleOf
      rw [hP, hB]
    rw [hd, hce, honestMemW, honestWit_cEnc, hsh]
  refine mem_holds_of_checks (program := program) (F0 := F0) (FH := FH)
    e ?_ (fun t ht b hb => ?_) hq
  · rw [hL]
    exact SampleInBall.checks_honestCells _ hS _
  · rw [rd 562 (by simp) _ (by rw [h2]; omega)]
    unfold memF
    rw [if_neg (by decide), if_pos rfl, dif_pos (by omega)]
    exact constBit_bool _ _

end Agree

/-! ## The honest committed values of domain `H` -/

variable (program F0 FH) in
/-- **The honest committed values of domain `H`** on an honest input: the hash's inputs
(`hashVal`), the selected bytes' bits (`557`), the threshold words (`558`) and the memory cells
(`561`–`566`); `0` elsewhere.

Running time: a prover computing these values would take the time of `hashVal` (ten Keccak-f
permutations) and of SampleInBall's honest memory trace (`39` steps over `256` cells).
This running time is argued here, not proved in Lean. -/
-- spec-side
noncomputable def hVal (i : MLDSA44.HonestInput) (v j : ℕ) : (interp (program.valueField v)).K :=
  if IsHashValue v then hashVal (program := program) (F0 := F0) (FH := FH) i.y v j
  else if v = 557 then RealizedProgram.castElt (a := 1) (jF FH i j)
  else if v = 558 then RealizedProgram.castElt (a := 1) (packWord (FH := FH) (lowF FH i) j)
  else if v ∈ [561, 562, 563, 564, 565, 566] then RealizedProgram.castElt (a := 1) (memF program F0 FH i v j)
  else 0

/-- The selection's and the memory's committed values are no hash values, decided. -/
theorem h_classes : ¬ IsHashValue 557 ∧ ¬ IsHashValue 558 ∧
    ∀ v ∈ [561, 562, 563, 564, 565, 566], ¬ IsHashValue v := by
  decide +kernel

section HVal

variable (i : MLDSA44.HonestInput)

theorem hVal_hash : ∀ v, IsHashValue v →
    hVal program F0 FH i v = hashVal (program := program) (F0 := F0) (FH := FH) i.y v :=
  fun v hv => funext fun j => by
    unfold hVal
    rw [if_pos hv]

theorem hVal_557 : ∀ v, v = 557 → ∀ n, RealizedProgram.castElt (b := 1) (hVal program F0 FH i v n) = jF FH i n := by
  rintro v rfl n
  obtain ⟨n7, -, -⟩ := h_classes
  have h7 := (MldsaHSelHonest.sel_cells (program := program)).2.2.2.2.2.2.2.2.2.2.1
  unfold hVal
  rw [if_neg n7, if_pos rfl]
  exact RealizedProgram.castElt_castElt_of_eq h7.symm _

theorem hVal_558 : ∀ v, v = 558 → ∀ w, RealizedProgram.castElt (b := 1) (hVal program F0 FH i v w) =
    packWord (FH := FH) (lowF FH i) w := by
  rintro v rfl w
  obtain ⟨-, n8, -⟩ := h_classes
  have h8 := (MldsaHSelHonest.sel_cells (program := program)).2.2.2.1
  unfold hVal
  rw [if_neg n8, if_neg (by decide), if_pos rfl, RealizedProgram.castElt_castElt_of_eq h8.symm]

theorem hVal_mem : ∀ v, v ∈ [561, 562, 563, 564, 565, 566] → ∀ n,
    RealizedProgram.castElt (b := 1) (hVal program F0 FH i v n) = memF program F0 FH i v n := by
  intro v hv n
  obtain ⟨-, -, nm⟩ := h_classes
  have hf := (MldsaHSelHonest.mem_cells (program := program)).1 v hv
  have h7 : v ≠ 557 := by rintro rfl; simp at hv
  have h8 : v ≠ 558 := by rintro rfl; simp at hv
  unfold hVal
  rw [if_neg (nm v hv), if_neg h7, if_neg h8, if_pos hv, RealizedProgram.castElt_castElt_of_eq hf.2.symm]

end HVal

/-! ## The honest values of domain `H` in their nodes -/

/-- A bit lies in every subfield. -/
theorem bit_mem_subfield {K : Type*} [Field K] {E : Subfield K} {x : K} (h : x = 0 ∨ x = 1) :
    x ∈ E := by
  rcases h with rfl | rfl
  · exact E.zero_mem
  · exact E.one_mem

section Nodes

variable [MldsaHNodes FH] (i : MLDSA44.HonestInput)

theorem mem_castElt_of_eqH {a b : ℕ} (h : a = b) {S : String} {z : (interp a).K}
    (hz : z ∈ (interp a).node S) : (RealizedProgram.castElt z : (interp b).K) ∈ (interp b).node S := by
  subst h
  rwa [RealizedProgram.castElt_self]

/-- **SampleInBall's honest memory cells lie in `GF(2^16)`.** -/
theorem memF_mem {v : ℕ} (n : ℕ) (hv : v ∈ [561, 563, 564, 565, 566]) :
    memF program F0 FH i v n ∈ (interp 1).node "GF(2^16)" := by
  have hθ := (samM program F0 FH).θ_mem
  have zero : (0 : (interp 1).K) ∈ (interp 1).node "GF(2^16)" := zero_mem _
  have sel : ∀ z ∈ (samM program F0 FH).field.E, z ∈ (interp 1).node "GF(2^16)" := by
    rw [samM_field]
    exact MldsaHNodes.node_of_sel
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  unfold memF
  rcases hv with rfl | rfl | rfl | rfl | rfl
  · rw [if_pos rfl]
    split_ifs
    · exact sel _ (MemoryShuffle.honestWit_read_value_mem _ _ _ _ hθ _)
    · exact zero
  · rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
    split_ifs
    · exact sel _ (MemoryShuffle.honestWit_cEnc_mem _ _ _ _ hθ _)
    · exact zero
  · rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
    split_ifs
    · exact sel _ (MemoryShuffle.honestWit_finalOrigin_mem _ _ _ _ _)
    · exact zero
  · rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
    split_ifs
    · refine sel _ ?_
      unfold MemoryShuffle.unit
      refine Subfield.add_mem _ (Subfield.one_mem _) (Subfield.mul_mem _
        (Subfield.add_mem _ hθ (Subfield.one_mem _)) ?_)
      change (if sgB program F0 FH i _ then 1 else 0) ∈ _
      split_ifs
      · exact Subfield.one_mem _
      · exact Subfield.zero_mem _
    · exact zero
  · rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
      if_neg (by decide), if_pos rfl]
    split_ifs
    · refine sel _ ?_
      unfold SampleInBall.originOf SelectionField.embedBits
      refine Subfield.sum_mem _ fun k _ => Subfield.mul_mem _ ?_ (SelectionField.e_mem _ _)
      exact bit_mem_subfield (constBit_bool _ _)
    · exact zero

/-- **The honest values of domain `H` read as words lie in `GF(2^16)`**: the trace words, `w1`'s
and `μ`'s words, the threshold words and the memory cells. -/
theorem hVal_mem_gf16 {v : ℕ} (hf : program.valueField v = 1)
    (hv : (wordsOwner? v).isSome ∨ v ∈ [70, 120, 558, 561, 563, 564, 565, 566]) (j : ℕ) :
    hVal program F0 FH i v j ∈ (interp (program.valueField v)).node "GF(2^16)" := by
  obtain ⟨n7, n8, nm⟩ := h_classes
  obtain ⟨-, w68, w69, w70, w120⟩ := wordsOwner_checks
  have pack := MldsaHNodes.pack_mem (FH := FH)
  rcases hv with hw | hw
  · have hH : IsHashValue v := Or.inr (Or.inr (Or.inr (Or.inr hw)))
    rw [hVal_hash i v hH]
    have hne : v ≠ 68 ∧ v ≠ 69 ∧ v ≠ 70 ∧ v ≠ 120 := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> simp_all
    unfold hashVal
    rw [if_neg hne.1, if_neg hne.2.1, if_neg hne.2.2.1, if_neg hne.2.2.2]
    split
    · exact mem_castElt_of_eqH (a := 1) hf.symm (pack _)
    · exact zero_mem _
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | hm
    · rw [hVal_hash i 70 (Or.inr (Or.inr (Or.inl rfl)))]
      unfold hashVal
      rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
      exact mem_castElt_of_eqH (a := 1) hf.symm (pack _)
    · rw [hVal_hash i 120 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]
      unfold hashVal
      rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
      exact mem_castElt_of_eqH (a := 1) hf.symm (pack _)
    · unfold hVal
      rw [if_neg n8, if_neg (by decide), if_pos rfl]
      exact mem_castElt_of_eqH (a := 1) hf.symm (pack _)
    · have hm' : v ∈ [561, 562, 563, 564, 565, 566] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
        omega
      unfold hVal
      rw [if_neg (nm v hm'), if_neg (by rintro rfl; simp at hm),
        if_neg (by rintro rfl; simp at hm), if_pos hm']
      exact mem_castElt_of_eqH (a := 1) hf.symm (memF_mem i j (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
        omega))

/-- **The honest values of domain `H` read as bits lie in the node `bit`**: the buffer, the flags,
the selected bytes' bits and the read origins' bits. -/
theorem hVal_mem_bit {v : ℕ} (hf : program.valueField v = 1) (hv : v ∈ [68, 69, 557, 562])
    (j : ℕ) : hVal program F0 FH i v j ∈ (interp (program.valueField v)).node "bit" := by
  obtain ⟨n7, -, nm⟩ := h_classes
  have bit : ∀ z : (interp 1).K, z = 0 ∨ z = 1 → z ∈ (interp 1).node "bit" :=
    fun z h => (MldsaHNodes.bit_iff (FH := FH) z).2 h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl
  · rw [hVal_hash i 68 (Or.inl rfl)]
    unfold hashVal
    rw [if_pos rfl]
    exact mem_castElt_of_eqH (a := 1) hf.symm (bit _ ((honestData_bool i.y).buf j))
  · rw [hVal_hash i 69 (Or.inr (Or.inl rfl))]
    unfold hashVal
    rw [if_neg (by decide), if_pos rfl]
    refine mem_castElt_of_eqH (a := 1) hf.symm (bit _ ?_)
    unfold flagNat
    split_ifs
    · exact Or.inr Nat.cast_one
    · exact Or.inl Nat.cast_zero
  · unfold hVal
    rw [if_neg n7, if_pos rfl]
    refine mem_castElt_of_eqH (a := 1) hf.symm (bit _ ?_)
    unfold jF
    split_ifs
    · exact constBit_bool _ _
    · exact Or.inl rfl
  · unfold hVal
    rw [if_neg (nm 562 (by simp)), if_neg (by decide), if_neg (by decide), if_pos (by simp)]
    refine mem_castElt_of_eqH (a := 1) hf.symm (bit _ ?_)
    unfold memF
    rw [if_neg (by decide), if_pos rfl]
    split_ifs
    · exact constBit_bool _ _
    · exact Or.inl rfl

end Nodes

/-! ## Domain `H`'s predicates at the honest values -/

section Holds

variable (i : MLDSA44.HonestInput) {e : program.Env interp} (hr : program.ReadsCells 1 e (hVal program F0 FH i))
  (htr : ∀ j < 512, (RealizedProgram.castElt (b := 1) (e.stmt 67 j) : (interp 1).K) =
    (honestData (K := FH.K) i.y).tr j)

include hr htr

/-- **The hash's predicates hold** at the honest values: the rounds and `μ`'s padding. -/
theorem hash_holds {q : ℕ} (h18 : 18 ≤ q) (h264 : q < 264) :
    program.HoldsWith (program.reader e) (program.predicate q).body := by
  have hh := hVal_hash (program := program) (F0 := F0) (FH := FH) i
  by_cases hp : q ∈ [42, 43, 44, 45, 46, 47]
  · exact pad_holds_hashVal hr hh i.hL htr hp
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hp
    by_cases h42 : q < 42
    · have := rounds_holds_honest hr hh htr 0 ⟨q - 18, by omega⟩
      have hq : roundPred 0 ⟨q - 18, by omega⟩ = q := by
        unfold roundPred
        simp only [Fin.val_zero, if_true]
        omega
      rwa [hq] at this
    · have := rounds_holds_honest hr hh htr ⟨(q - 48) / 24 + 1, by omega⟩ ⟨(q - 48) % 24, by omega⟩
      have hq : roundPred ⟨(q - 48) / 24 + 1, by omega⟩ ⟨(q - 48) % 24, by omega⟩ = q := by
        unfold roundPred
        simp only [show (q - 48) / 24 + 1 ≠ 0 by omega, if_false]
        omega
      rwa [hq] at this

omit htr in
/-- **SampleInBall's predicates hold** at the honest values. -/
theorem sample_holds {q : ℕ} (hq : q ∈ [264, 265, 266, 267, 268, 269, 270]) :
    program.HoldsWith (program.reader e) (program.predicate q).body := by
  have hh := hVal_hash (program := program) (F0 := F0) (FH := FH) i
  by_cases hs : q ∈ [264, 265, 266]
  · exact select_holds_honest hr hh (fun v hv n _ => hVal_557 i v hv n)
      (fun v hv w _ => hVal_558 i v hv w) hs
  · have hm : q ∈ [267, 268, 269, 270] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq hs ⊢
      omega
    exact mem_holds_honest hr hh (fun v hv n _ => hVal_557 i v hv n)
      (fun v hv n _ => hVal_mem i v hv n) hm

/-- **Domain `H`'s predicates `18 … 270` hold** at the honest values: the hash's and
SampleInBall's. -/
theorem hPreds_holds {q : ℕ} (h18 : 18 ≤ q) (h270 : q ≤ 270) :
    program.HoldsWith (program.reader e) (program.predicate q).body := by
  by_cases h : q < 264
  · exact hash_holds i hr htr h18 h
  · exact sample_holds i hr (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)

end Holds

/-! ## Domain `H`'s crossing operand at the honest values -/

section Crossing

variable (i : MLDSA44.HonestInput)

/-- **The honest shuffle is the challenge**: SampleInBall's shuffle on the input's positions and
the honest signs. -/
theorem shuffle_honest (k : Fin 256) :
    MemoryShuffle.shuffle 256 (samM program F0 FH).τ (posN program F0 FH i) (sgB program F0 FH i) k =
      i.y.c k := by
  have hy := i.valid
  have hsign : SampleInBall.signBoolsOf
      (Native.signsOf (MldsaHNativeData.D (FH := FH)) (nativeH FH i)) =
      fun s : Fin mldsa44.τ => MLDSA44.sampleInBallSign (MLDSA44.PoP.stream i.y.ctilde) s := by
    rw [Native.signsOf, Native.signBoolsOf_signWires
      (out := Native.sibBytes (MldsaHNativeData.D (FH := FH)) (nativeH FH i))
      ((Native.hashConstraints_honest (MldsaHNativeData.D (FH := FH)).packing i.y).sibOut_allBool),
      Native.sibStream_honest (MldsaHNativeData.D (FH := FH)) hy]
  have hsh : SampleInBall.shuffleOf 256 (nativeH FH i).j
      (Native.signsOf (MldsaHNativeData.D (FH := FH)) (nativeH FH i)) = i.y.c := by
    rw [SampleInBall.shuffleOf, hsign,
      funext (Native.natOfBits_positions (D := MldsaHNativeData.D (FH := FH)) hy)]
    rfl
  have hk := congrFun hsh k
  rw [← hk]
  unfold SampleInBall.shuffleOf
  congr 1
  funext t
  exact (Native.natOfBits_positions (D := MldsaHNativeData.D (FH := FH)) hy
    (Fin.cast (samM_τ_eq program F0 FH) t)).symm

/-- The challenge's degree is `256`. -/
theorem cdeg : (256 : ℕ) = mldsa44.N := rfl

/-- **The final cells encode the challenge** at the honest memory trace. -/
theorem honestMemW_cEnc (k : ℕ) (hk : k < 256) :
    (honestMemW program F0 FH i).cEnc ⟨k, hk⟩ =
      MemoryShuffle.encode (samM program F0 FH).Θ (i.y.c (Fin.cast cdeg ⟨k, hk⟩)) := by
  have h1 := honestWit_cEnc (samM program F0 FH).field (samM program F0 FH).Θ
    (posN program F0 FH i) (sgB program F0 FH i) (⟨k, hk⟩ : Fin (samM program F0 FH).N)
  have h2 := shuffle_honest (program := program) (F0 := F0) (FH := FH) i ⟨k, hk⟩
  exact h1.trans (congrArg _ h2)

/-- **H's decoded challenge** is `decodeTernary` of the final cell (`decodeRow`, read at natural
coordinates). -/
theorem chalPair_eq (e : program.Env interp) (k : Fin 256) :
    chalPair (program.reader e) k = MemoryShuffle.decodeTernary (samM program F0 FH).Θ
      (program.evalE (program.reader e) 1 (.leaf 563) k) := by
  obtain ⟨c, -, he, hc0⟩ := MldsaHConsts.theta (program := program) (FH := FH)
  have hc : (interp 1).decode c = (samM program F0 FH).Θ.θ + 1 := hc0
  unfold chalPair MemoryShuffle.decodeTernary
  rw [RealizedProgram.evalE_ref MldsaHCross.refsOrdered _ _
      (by have := (refsMem (program := program)); omega),
    he, RealizedProgram.evalE_add, RealizedProgram.evalE_scale_const, hc,
    RealizedProgram.evalE_ref MldsaHCross.refsOrdered _ _
      (by have := (refsMem (program := program)); omega),
    (expr522 (program := program)), RealizedProgram.evalE_add, RealizedProgram.evalE_mul, sq]

/-- **H's decoded challenge is the challenge's ternary bits** at the honest values. -/
theorem chalPair_honest {e : program.Env interp}
    (hr : program.ReadsCells 1 e (hVal program F0 FH i)) (k : Fin 256) :
    chalPair (program.reader e) k =
      HashCircuit.ternaryBits (K := (interp 1).K) (i.y.c (Fin.cast cdeg k)) := by
  obtain ⟨hcell, -, -, h3, -⟩ := MldsaHSelHonest.mem_cells (program := program)
  rw [chalPair_eq, RealizedProgram.evalE_leaf,
    hr (hcell 563 (by simp)).1 (hcell 563 (by simp)).2 (by rw [h3]; exact k.isLt)]
  rw [hVal_mem i 563 (by simp)]
  unfold memF
  rw [if_neg (by decide), if_neg (by decide), if_pos rfl, dif_pos k.isLt, honestMemW_cEnc]
  exact MemoryShuffle.decodeTernary_encode _ _ (Native.c_ternary i.y _)

/-- The integer reading of a bit constant in domain `H`'s field. -/
theorem toNatH_ite (p : Prop) [Decidable p] :
    (interp 1).toNat (if p then (1 : (interp 1).K) else 0) = if p then 1 else 0 := by
  split_ifs
  · exact HField.toNat_one (FH := FH)
  · exact HField.toNat_zero (FH := FH)

theorem tern1_H (z : ℤ) : (interp 1).toNat (HashCircuit.ternaryBits (K := (interp 1).K) z).1 =
    if z = 0 then 0 else 1 := by
  rw [show (HashCircuit.ternaryBits (K := (interp 1).K) z).1 = if z = 0 then 0 else 1 from rfl]
  split_ifs
  · exact HField.toNat_zero (FH := FH)
  · exact HField.toNat_one (FH := FH)

theorem tern2_H (z : ℤ) : (interp 1).toNat (HashCircuit.ternaryBits (K := (interp 1).K) z).2 =
    if z = -1 then 1 else 0 := by
  rw [show (HashCircuit.ternaryBits (K := (interp 1).K) z).2 = if z = -1 then 1 else 0 from rfl]
  split_ifs
  · exact HField.toNat_one (FH := FH)
  · exact HField.toNat_zero (FH := FH)

variable {e : program.Env interp} (hr : program.ReadsCells 1 e (hVal program F0 FH i))
include hr

/-- **The crossing's H operand below `6144`** is the bit of `w1Encode(w1)` at the honest values. -/
theorem xH_lo
    (htr : ∀ j < 512, (RealizedProgram.castElt (b := 1) (e.stmt 67 j) : (interp 1).K) =
      (honestData (K := FH.K) i.y).tr j) {j : ℕ} (hj : j < 6144) :
    program.evalE (program.reader e) 1 (.ref 525) j =
      constBit (K := (interp 1).K) (w1Nat i.y (j / 8)) (j % 8) := by
  have hia := inputsAgree_of_hashVal hr (hVal_hash (program := program) (F0 := F0) (FH := FH) i) htr
  rw [x_lo _ hj, hia.w1 j hj]
  rfl

/-- **The crossing's H operand at `6144 + 2 k`** is the support bit of the challenge's
coefficient `k` at the honest values. -/
theorem xH_even {k : ℕ} (hk : k < 256) :
    program.evalE (program.reader e) 1 (.ref 525) (6144 + 2 * k) =
      (HashCircuit.ternaryBits (K := (interp 1).K) (i.y.c (Fin.cast cdeg ⟨k, hk⟩))).1 := by
  rw [x_even _ hk]
  have hp := congrArg Prod.fst (chalPair_honest i hr ⟨k, hk⟩)
  unfold chalPair at hp
  exact hp

/-- **The crossing's H operand at `6144 + 2 k + 1`** is the sign bit of the challenge's
coefficient `k` at the honest values. -/
theorem xH_odd {k : ℕ} (hk : k < 256) :
    program.evalE (program.reader e) 1 (.ref 525) (6144 + (2 * k + 1)) =
      (HashCircuit.ternaryBits (K := (interp 1).K) (i.y.c (Fin.cast cdeg ⟨k, hk⟩))).2 := by
  rw [x_odd _ hk]
  have hp := congrArg Prod.snd (chalPair_honest i hr ⟨k, hk⟩)
  unfold chalPair at hp
  exact hp

/-- **The crossing's H operand reads bits** at the honest values. -/
theorem xH_bits {j : ℕ} (hj : j < 6656) :
    program.evalE (program.reader e) 1 (.ref 525) j = 0 ∨
      program.evalE (program.reader e) 1 (.ref 525) j = 1 := by
  by_cases hlo : j < 6144
  · rw [x_lo _ hlo]
    exact w1H_bool _ j
  · obtain ⟨k, hk, rfl | rfl⟩ : ∃ k < 256, j = 6144 + 2 * k ∨ j = 6144 + (2 * k + 1) :=
      ⟨(j - 6144) / 2, by omega, by omega⟩
    · rw [xH_even i hr hk, show (HashCircuit.ternaryBits (K := (interp 1).K)
        (i.y.c (Fin.cast cdeg ⟨k, hk⟩))).1 = if i.y.c (Fin.cast cdeg ⟨k, hk⟩) = 0 then 0 else 1
          from rfl]
      split_ifs
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rw [xH_odd i hr hk, show (HashCircuit.ternaryBits (K := (interp 1).K)
        (i.y.c (Fin.cast cdeg ⟨k, hk⟩))).2 = if i.y.c (Fin.cast cdeg ⟨k, hk⟩) = -1 then 1 else 0
          from rfl]
      split_ifs
      · exact Or.inr rfl
      · exact Or.inl rfl

end Crossing

end GordieHowe.MLDSA44.Native.ROMParams
