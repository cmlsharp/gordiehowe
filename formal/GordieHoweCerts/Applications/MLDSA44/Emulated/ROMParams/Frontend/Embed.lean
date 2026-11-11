-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweCerts.Applications.MLDSA44.Emulated.ROMParams.Frontend.Reads
public import GordieHoweCerts.Applications.MLDSA44.Emulated.Frontend.Embed
public import GordieHoweCerts.Generated.MLDSA44.Emulated.ROMParams.Program
public import GordieHoweCerts.Generated.MLDSA44.Emulated.ROMParams.Plan
public import GordieHoweCerts.Generated.MLDSA44.Emulated.ROMParams.Certified
public import GordieHowe.ProofSystem.Program.FieldHonest

@[expose] public section

/-!
# GordieHowe frontend: `MLDSA44.Emulated.ROMParams` holds `MLDSA44.Native.ROMParams`'s domain `H`

The emulated ML-DSA program at the ROM parameters (`GordieHowe.Generated.MLDSA44.Emulated.ROMParams.Program.program`, export
`c825eb05`) holds the native one's domain `H` under the renaming of its checked embedding data
(`MldsaEmbed`, decided here), and its domain `A` is Goldilocks² (`GordieHowe.RealizedProgram.PrimeCastField`).
-/

namespace GordieHowe.MLDSA44.Emulated.ROMParams

open Generated.MLDSA44.Emulated.ROMParams.Program (program)

/-- The native ML-DSA program at the ROM parameters, whose domain `H` the emulated one holds. -/
abbrev nat : RealizedProgram := Generated.MLDSA44.Native.ROMParams.Program.program

/-- **The checked embedding data** of the native program's domain `H`. -/
abbrev embedData : RealizedProgram.EmbedData := Generated.MLDSA44.Emulated.ROMParams.Shapes.embedding_native_2eH_data

/-- **The renaming**, the data's (`EmbedData.renamingAfter`). -/
abbrev σ : RealizedProgram.Renaming := embedData.renamingAfter

/-- **The emulated predicate of each held native predicate**, from the data's pairs. -/
def heldPred (k : ℕ) : ℕ := (embedData.equals.lookup k).getD k

theorem holds : embedData.Holds program σ :=
  Generated.MLDSA44.Emulated.ROMParams.ShapeFacts.embedding_native_2eH_holds σ embedData.agrees_renamingAfter

/-- **The emulated program holds the native program's domain `H`** (`RealizedProgram.Embedding`). -/
theorem embedding : nat.Embedding program σ embedData.V embedData.R :=
  holds.embedding_at rfl rfl rfl

/-- **Native predicate `k` of domain `H` is emulated predicate `heldPred k`**, renamed. -/
theorem predCorr : ∀ k, hPredLo ≤ k → k ≤ hPredHi →
    nat.equalCorrB program σ embedData.V embedData.R (nat.predicate k).body
      (program.predicate (heldPred k)).body = true ∧
      heldPred k < program.predicates.length ∧
      program.inSource (program.predicate (heldPred k)) = true := by
  have hm : ∀ k ∈ List.range' 18 253, (k, heldPred k) ∈ embedData.equals := by decide +kernel
  exact fun k h1 h2 => holds.equals_at rfl rfl rfl (hm k (by simp only [corePredLo, hPredLo, hPredHi, List.mem_range'_1] at *; omega))

/-- **Every held value is one identifier larger** at this program. -/
theorem shift : ∀ v ∈ embedData.V, σ.val v = v + 1 := by decide +kernel

/-- Where the renaming puts the crossing's operand of domain `H` at this program. -/
theorem ref525 : σ.ref 525 = 527 := by decide +kernel

/-- **The values the frontend reads by their node types** are renamed to node-typed source
values. -/
theorem typedCorr : ∀ v ∈ MLDSA44.hTyped, v ∈ embedData.V ∧
    σ.val v < program.values.length ∧ program.IsSourceValue (σ.val v) ∧
    (program.value (σ.val v)).typeSource = .node := by
  intro v hv
  simp only [MLDSA44.hTyped, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    refine ⟨by decide +kernel, ?_⟩
    rw [shift _ (by decide +kernel)]
    simp only [Nat.reduceAdd]
    shape_decide

/-- The data's challenge images: `0 … 3`. -/
theorem chals_eq : embedData.chals = List.range' 0 (3 + 1) := by decide +kernel

/-- **The challenges keep their identifiers.** -/
theorem chalId : ∀ j, σ.chal j = j := fun j =>
  (MLDSA44.renamingAfter_chal_of_range chals_eq j).trans (Nat.add_zero j)

/-- **The emulated program at the ROM parameters holds the native program's domain `H`.** -/
instance : Emulated.MldsaEmbed program where
  nat := nat
  σ := σ
  V := embedData.V
  R := embedData.R
  pred := heldPred
  embedding := embedding
  predCorr := predCorr
  typedCorr := typedCorr
  chalId := chalId
  readV := by decide +kernel
  held := embedData.equals
  pred_held := by decide +kernel

/-- Goldilocks² has domain `A`'s field facts. -/
instance instPrimeCastFieldGold2PGold : RealizedProgram.PrimeCastField RealizedProgram.gold2 pGold where
  charP := inferInstanceAs (CharP GoldilocksExt2 pGold)
  char_spec := rfl
  decode_lt c hc := RealizedProgram.gold2_model.decode_natCast c hc
  toNat_natCast k hk := by
    change (goldilocksExt2Coords (k : GoldilocksExt2) 0).val = k
    rw [goldilocksExt2Coords_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hk]


end GordieHowe.MLDSA44.Emulated.ROMParams
