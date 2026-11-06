-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Emulated.QROMParams.Frontend.Reads
public import GordieHowe.Applications.MLDSA44.Emulated.Frontend.Algebra
public import GordieHowe.Applications.MLDSA44.Native.QROMParams.Frontend.Shape
public import GordieHowe.Generated.MLDSA44.Emulated.QROMParams.Certified
public import GordieHowe.ProofSystem.Program.FieldHonest
public import GordieHowe.Generated.MLDSA44.Emulated.QROMParams.ShapeFacts

@[expose] public section

/-!
# GordieHowe frontend: `MLDSA44.Emulated.QROMParams`

The emulated ML-DSA frontend (`GordieHowe.MLDSA44.Emulated`) at the emulated ML-DSA-44 program at the QROM parameters
(`GordieHowe.Generated.MLDSA44.Emulated.QROMParams.Program.program`, export `c825eb05`): it holds the native
program's domain `H` under `Emulated.σ` (`MldsaEmbed`), its program facts (`MldsaEMain`,
`MldsaECross`, `MldsaEAlgebra`) are decided here, domain `A` is Goldilocks⁴ (`GordieHowe.RealizedProgram.PrimeCastField`), domain
`H` is `GF(2^256)` (`gf256`).
-/

namespace GordieHowe.MLDSA44.Emulated.QROMParams

open Generated.MLDSA44.Emulated.QROMParams.Program (program)
open Generated.MLDSA44.Emulated.QROMParams (interp)
open GordieHowe.Bits IOP
open scoped NNReal ENNReal

/-- The native ML-DSA program at the QROM parameters, whose domain `H` the emulated one holds. -/
abbrev nat : RealizedProgram := Generated.MLDSA44.Native.QROMParams.Program.program

/-- The renaming (`Emulated.σ`). -/
abbrev σ : RealizedProgram.Renaming := Emulated.σ

/-- The native shared expressions of domain `H`'s part (`Emulated.hR`). -/
abbrev hR : List ℕ := Emulated.hR

theorem agrees : Generated.MLDSA44.Emulated.QROMParams.Shapes.embedding_native_2eH_data.Agrees σ :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem holds : Generated.MLDSA44.Emulated.QROMParams.Shapes.embedding_native_2eH_data.Holds program σ :=
  Generated.MLDSA44.Emulated.QROMParams.ShapeFacts.embedding_native_2eH_holds σ agrees

/-- **The emulated program holds the native program's domain `H`** (`RealizedProgram.Embedding`). -/
theorem embedding : nat.Embedding program σ Emulated.hV hR :=
  holds.embedding_at rfl (by decide +kernel) (by decide +kernel)

/-- **Native predicate `k` of domain `H` is emulated predicate `k + 2`**, renamed. -/
theorem predCorr : ∀ k, 18 ≤ k → k ≤ 270 →
    nat.equalCorrB program σ Emulated.hV hR (nat.predicate k).body
      (program.predicate (k + 2)).body = true ∧
      k + 2 < program.predicates.length ∧ program.inSource (program.predicate (k + 2)) = true := by
  have hm : ∀ k, 18 ≤ k → k ≤ 270 →
      (k, k + 2) ∈ Generated.MLDSA44.Emulated.QROMParams.Shapes.embedding_native_2eH_data.equals := by
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

/-- **The emulated program at the QROM parameters holds the native program's domain `H`.** -/
instance : Emulated.MldsaEmbed program where
  nat := nat
  embedding := embedding
  predCorr := predCorr
  typedCorr := typedCorr

/-- Goldilocks⁴ has domain `A`'s field facts. -/
instance : RealizedProgram.PrimeCastField RealizedProgram.gold4 pGold where
  charP := inferInstanceAs (CharP GoldilocksExt4 pGold)
  char_spec := rfl
  decode_lt c hc := RealizedProgram.gold4_model.decode_natCast c hc
  toNat_natCast k hk := by
    change (goldilocksExt4Coords (k : GoldilocksExt4) 0).val = k
    rw [goldilocksExt4Coords_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hk]

set_option maxRecDepth 4096 in
/-- The emulated program at the QROM parameters has the composition's facts. -/
instance : Emulated.MldsaEMain program where
  chal_phase := by
    intro j
    rcases lt_or_ge j 4 with hj | hj
    · exact (holds).chalPhase j hj
    · have h1 : program.challenges.length = 4 :=
        Generated.MLDSA44.Emulated.QROMParams.ShapeFacts.challenges_length
      have h2 : (Emulated.MldsaEmbed.nat program).challenges.length = 4 := (holds).chalCount
      simp only [RealizedProgram.challenge, List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_none (by rw [h1]; exact hj), List.getElem?_eq_none (by rw [h2]; exact hj)]
  isSourceChal_iff := fun {j} => by
    rw [program.isSourceChal_iff_mem_sourceChallengeIds
      Generated.MLDSA44.Emulated.QROMParams.conditions.wellFormed,
      Generated.MLDSA44.Emulated.QROMParams.ShapeFacts.source_challenges]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
  chalFacts := ⟨Reads.chalSize0, Reads.chalSampler0, Reads.chalField0, Reads.chalSize1,
    Reads.chalSampler1, Reads.chalField1, MLDSA44.Native.QROMParams.Reads.chalField0, MLDSA44.Native.QROMParams.Reads.chalField1⟩
  kinds59_60 := by shape_decide
  trFields := ⟨MLDSA44.Native.QROMParams.Reads.field66, Reads.field67⟩
  projReadsN := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact MLDSA44.Native.QROMParams.Reads.reads67
    · exact MLDSA44.Native.QROMParams.Reads.reads68
    · exact MLDSA44.Native.QROMParams.Reads.reads457

set_option maxRecDepth 4096 in
/-- The emulated program at the QROM parameters has the crossing's facts. -/
instance : Emulated.MldsaECross program where
  expr6 := Generated.MLDSA44.Emulated.QROMParams.ShapeFacts.expr_mac_2eequal_2eshape_2eright_eq
  refsOrdered := Generated.MLDSA44.Emulated.QROMParams.conditions.wellFormed.refsOrdered
  crossData := by
    shape_decide
  crossPred := Generated.MLDSA44.Emulated.QROMParams.ShapeFacts.predicate_mac_2eequal_body

/-- **The digit layout of `MLDSA44.Emulated.QROMParams`**: `w'`, `z + 130993`, the offset and the slack in
two base-`4096` digits each (`577`, `578`; `579`, `580`; `584`, `585`; `586`, `587`); the offset's
and the slack's bound `2^24`. -/
def layout : Emulated.MldsaELayout where
  w := ⟨4096, [577, 578]⟩
  z := ⟨4096, [579, 580]⟩
  offset := ⟨4096, [584, 585]⟩
  slack := ⟨4096, [586, 587]⟩
  offsetBound := 16777216

set_option maxRecDepth 4096 in
/-- The emulated program at the QROM parameters has domain `A`'s facts. -/
instance : Emulated.MldsaEAlgebra program where
  layout := layout
  offsetBound_lt := by decide
  lenWeight := by shape_decide
  lenSigL := by shape_decide
  pred0 := Generated.MLDSA44.Emulated.QROMParams.ShapeFacts.predicate_hint_2ew1_5fbound_body
  pred1 := Generated.MLDSA44.Emulated.QROMParams.ShapeFacts.predicate_hint_2edecompose_body
  pred2 := Generated.MLDSA44.Emulated.QROMParams.ShapeFacts.predicate_hint_2einterval_body
  pred11 := Generated.MLDSA44.Emulated.QROMParams.ShapeFacts.predicate_signature_2ew_body
  pred12 := Generated.MLDSA44.Emulated.QROMParams.ShapeFacts.predicate_norm_2ez_body
  pred13 := Generated.MLDSA44.Emulated.QROMParams.ShapeFacts.predicate_hint_2eoffset_body
  pred14 := Generated.MLDSA44.Emulated.QROMParams.ShapeFacts.predicate_hint_2eslack_body
  pred15 := Generated.MLDSA44.Emulated.QROMParams.ShapeFacts.predicate_hint_5fweight_2eweight_body
  pred274 := by
    obtain ⟨r, h, hf, -⟩ := Generated.MLDSA44.Emulated.QROMParams.ShapeFacts.predicate_signature_2erelation_2esource_body
    exact ⟨r, h, by rw [hf]; rfl⟩
  expr7 := Generated.MLDSA44.Emulated.QROMParams.ShapeFacts.expr_signature_2erelation_2eshape_2eleft_2efirst_2esecond_2efirst_2efirst_eq
  expr8 := Generated.MLDSA44.Emulated.QROMParams.ShapeFacts.expr_signature_2erelation_2eshape_2eleft_2esecond_2efirst_2efirst_eq
  expr0 := Generated.MLDSA44.Emulated.QROMParams.ShapeFacts.expr_hint_2einterval_2eshape_2eright_2efirst_2eshared_2esecond_2eshared_2efirst_eq
  expr1 := Generated.MLDSA44.Emulated.QROMParams.ShapeFacts.expr_hint_2edecompose_2eshape_2eleft_2efirst_2eshared_2efirst_2efirst_2esecond_2efirst_2efirst_2efirst_2efirst_2esecond_2efirst_eq
  expr2 := Generated.MLDSA44.Emulated.QROMParams.ShapeFacts.expr_hint_2einterval_2eshape_2eright_2efirst_2eshared_2efirst_2esecond_eq
  expr3 := Generated.MLDSA44.Emulated.QROMParams.ShapeFacts.expr_hint_2einterval_2eshape_2eright_2efirst_2eshared_2esecond_eq
  expr4 := Generated.MLDSA44.Emulated.QROMParams.ShapeFacts.expr_hint_2einterval_2eshape_2eright_2efirst_eq
  expr5 := Generated.MLDSA44.Emulated.QROMParams.ShapeFacts.expr_hint_2edecompose_2eshape_2eleft_2efirst_eq
  inSource_A := by
    shape_decide
  lensA := by
    shape_decide
  boolChecks := by
    shape_decide
  constsA := by
    shape_decide
  constsU := by
    shape_decide
  refsA := by shape_decide
  lensU := by
    shape_decide
  valsU := by
    shape_decide
  sigData := by
    shape_decide
  boundZW := by
    shape_decide

/-- The native program's domain `H` facts at the emulated program's native program. -/
instance : MLDSA44.MldsaHHash (Emulated.MldsaEmbed.nat program) :=
  inferInstanceAs (MLDSA44.MldsaHHash nat)

/-- The native program's SampleInBall facts at the emulated program's native program. -/
instance : MLDSA44.MldsaHSample (Emulated.MldsaEmbed.nat program) :=
  inferInstanceAs (MLDSA44.MldsaHSample nat)

/-- The native program's constants over `GF(2^256)` at the emulated program's native program. -/
instance : MLDSA44.MldsaHConsts (Emulated.MldsaEmbed.nat program) RealizedProgram.gf256 :=
  inferInstanceAs (MLDSA44.MldsaHConsts nat RealizedProgram.gf256)

/-- **The round errors of SampleInBall's challenges** over `GF(2^256)`: `264/2^256` and
`295/2^256` (`MLDSA44.sampleEpsOf 256`). -/
noncomputable def sampleEps (j : ℕ) : NNReal := MLDSA44.sampleEpsOf 256 j

/-- **The statement holds a key's preprocessing** (`Emulated.KeyOf`). -/
abbrev KeyOf (pk : MLDSA44.PublicKey44) (x : program.Valuation interp) : Prop :=
  Emulated.KeyOf pk x

/-- **The relation of the theorem at the realized program of `MLDSA44.Emulated.QROMParams`** (`Emulated.rel`). -/
abbrev rel : Set (program.Valuation interp × MLDSA44.VarWitness) :=
  Emulated.rel

/-- **The witness extracted from a statement and a committed assignment** (`Emulated.proj`).

Running time: `Emulated.proj`'s paragraph (polynomial in the program's size).
This running time is argued here, not proved in Lean. -/
-- spec-side
def proj (x : program.Valuation interp) (a : program.Assignment interp) :
    MLDSA44.VarWitness :=
  Emulated.proj x a

/-- **The extractor of `Π_P₀`** for `MLDSA44.Emulated.QROMParams` (`RealizedProgram.sourceExtractor` at `proj`).

Running time: one read of the transcript's first round and one call of `proj` (polynomial,
`proj`'s paragraph). This running time is argued here, not proved in Lean. -/
def extractor :
    Extractor (program.sourceSpec interp) (program.Valuation interp) MLDSA44.VarWitness :=
  program.sourceExtractor interp proj

/-- **The crossing wherever the source program holds** (`Emulated.CrossSound`). -/
abbrev CrossSound : Prop := Emulated.CrossSound (program := program)
  (F0 := RealizedProgram.gold4) (FH := RealizedProgram.gf256)

/-- **Domain `A`'s obligation** (`Emulated.AlgebraSound`). -/
abbrev AlgebraSound : Prop := Emulated.AlgebraSound (program := program)
  (F0 := RealizedProgram.gold4) (FH := RealizedProgram.gf256)

/-- **SampleInBall's events** (`Emulated.sampleEvent`). -/
abbrev sampleEvent (j : ℕ) (e : program.Env interp) : Prop :=
  Emulated.sampleEvent j e

/-- **The challenge-use rule** (`Emulated.sampleEvent_use`). -/
theorem sampleEvent_use : RealizedProgram.ChallengeUseAt program interp sampleEvent :=
  Emulated.sampleEvent_use

/-- **The relation from the source program without an event** (`Emulated.sound_of_views`). -/
theorem sound_of_views (hx : CrossSound) (hA : AlgebraSound) :
    ∀ e : program.Env interp, program.StatementOk interp e.stmt → program.SourceSatAt e →
      (∀ j, program.IsSourceChal j → ¬ sampleEvent j e) → (e.stmt, proj e.stmt e.asg) ∈ rel :=
  Emulated.sound_of_views hx hA

/-- **Round-by-round knowledge soundness of `Π_P₀` for `MLDSA44.Emulated.QROMParams`**, given the
crossing and the algebra (`Emulated.rbr_of_views`): SampleInBall's events with errors
`264/2^256` and `295/2^256`. -/
theorem rbr_of_views (hx : CrossSound) (hA : AlgebraSound) :
    rbrKnowledgeSoundness rel (program.sourceVerifier interp) extractor
      (program.eventState interp rel proj sampleEvent sampleEvent_use (sound_of_views hx hA))
      (program.roundError interp sampleEps) :=
  Emulated.rbr_of_views hx hA

/-- **`mac.equal` gives the crossing** (`Emulated.crossSound`). -/
theorem crossSound : CrossSound := Emulated.crossSound

/-- **Domain `A`'s obligation** (`Emulated.algebraSound`). -/
theorem algebraSound : AlgebraSound := Emulated.algebraSound

end GordieHowe.MLDSA44.Emulated.QROMParams
