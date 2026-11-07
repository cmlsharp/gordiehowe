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
`c825eb05`) holds the native one's domain `H` under the renaming `Emulated.σ`
(`MldsaEmbed`, decided here), and its domain `A` is Goldilocks² (`GordieHowe.RealizedProgram.PrimeCastField`).
-/

namespace GordieHowe.MLDSA44.Emulated.ROMParams

open Generated.MLDSA44.Emulated.ROMParams.Program (program)

/-- The native ML-DSA program at the ROM parameters, whose domain `H` the emulated one holds. -/
abbrev nat : RealizedProgram := Generated.MLDSA44.Native.ROMParams.Program.program

/-- The renaming (`Emulated.σ`). -/
abbrev σ : RealizedProgram.Renaming := Emulated.σ

/-- The native shared expressions of domain `H`'s part (`Emulated.hR`). -/
abbrev hR : List ℕ := Emulated.hR

theorem agrees : Generated.MLDSA44.Emulated.ROMParams.Shapes.embedding_native_2eH_data.Agrees σ :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem holds : Generated.MLDSA44.Emulated.ROMParams.Shapes.embedding_native_2eH_data.Holds program σ :=
  Generated.MLDSA44.Emulated.ROMParams.ShapeFacts.embedding_native_2eH_holds σ agrees

/-- **The emulated program holds the native program's domain `H`** (`RealizedProgram.Embedding`). -/
theorem embedding : nat.Embedding program σ Emulated.hV hR :=
  holds.embedding_at rfl (by decide +kernel) (by decide +kernel)

/-- **Native predicate `k` of domain `H` is emulated predicate `k + 2`**, renamed. -/
theorem predCorr : ∀ k, 18 ≤ k → k ≤ 270 →
    nat.equalCorrB program σ Emulated.hV hR (nat.predicate k).body
      (program.predicate (k + 2)).body = true ∧
      k + 2 < program.predicates.length ∧ program.inSource (program.predicate (k + 2)) = true := by
  have hm : ∀ k, 18 ≤ k → k ≤ 270 →
      (k, k + 2) ∈ Generated.MLDSA44.Emulated.ROMParams.Shapes.embedding_native_2eH_data.equals := by
    decide +kernel
  exact fun k h1 h2 => holds.equals_at rfl (by decide +kernel) (by decide +kernel) (hm k h1 h2)

/-- **The values the frontend reads by their node types** are renamed to node-typed source
values. -/
theorem typedCorr : ∀ v ∈ MLDSA44.hTyped, v ∈ Emulated.hV ∧
    σ.val v < program.values.length ∧ program.IsSourceValue (σ.val v) ∧
    (program.value (σ.val v)).typeSource = .node := by
  intro v hv
  simp only [MLDSA44.hTyped, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    refine ⟨by decide +kernel, ?_⟩
    simp only [σ, Emulated.σ, Nat.reduceAdd]
    shape_decide

/-- **The emulated program at the ROM parameters holds the native program's domain `H`.** -/
instance : Emulated.MldsaEmbed program where
  nat := nat
  embedding := embedding
  predCorr := predCorr
  typedCorr := typedCorr

/-- Goldilocks² has domain `A`'s field facts. -/
instance instPrimeCastFieldGold2PGold : RealizedProgram.PrimeCastField RealizedProgram.gold2 pGold where
  charP := inferInstanceAs (CharP GoldilocksExt2 pGold)
  char_spec := rfl
  decode_lt c hc := RealizedProgram.gold2_model.decode_natCast c hc
  toNat_natCast k hk := by
    change (goldilocksExt2Coords (k : GoldilocksExt2) 0).val = k
    rw [goldilocksExt2Coords_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hk]


end GordieHowe.MLDSA44.Emulated.ROMParams
