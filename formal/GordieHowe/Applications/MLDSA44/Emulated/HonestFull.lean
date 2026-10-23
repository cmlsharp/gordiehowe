-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Emulated.HonestSource
public import GordieHowe.Language.Honest.Exec
public import GordieHowe.Language.Completeness.Execution

@[expose] public section

/-!
# GordieHowe: the honest execution of an emulated ML-DSA program

The execution of the source program of an emulated ML-DSA program (`GordieHowe.RealizedProgram.SourceExecution`): the honest
valuation `honestVal` at the key's statement, the program facts (`MldsaEmulatedHonest`), the source
predicates (`source_holds`) and the MAC's source facts (`srcMac_holds`) at the source environment,
the node-typed source values in their types (`honest_types`) and the execution (`sourceExecution`).
-/

namespace GordieHowe.MLDSA44.Emulated

open GordieHowe.Bits RealizedProgram
open MLDSA44 (HonestInput)
open Native.ROMParams (hVal MldsaHHash MldsaHSample MldsaHConsts MldsaHHonest MldsaHShuffle MldsaHSelHonest MldsaHNativeData MldsaHNodes)


set_option linter.unusedSectionVars false

set_option hygiene false in
local notation "interp" => mldsaInterpOf F0 FH

set_option hygiene false in
local notation "nat" => MldsaEmbed.nat program

set_option hygiene false in
local notation "L" => MldsaEAlgebra.layout program

/-- **The prime subfield of an emulated program's domain `A`**: the naturals lie in the node
`GF(p^1)`. A fact about the field interpretation, instantiated for each Goldilocks extension. -/
class MldsaANodes (F0 : FieldInterp) : Prop where
  /-- The naturals lie in the node `GF(p^1)`. -/
  natCast_mem : ∀ n : ℕ, (n : F0.K) ∈ F0.node "GF(p^1)"

section Prime

variable {F0 FH : FieldInterp} [MldsaANodes F0]

theorem natCast_mem_prime (n : ℕ) : (n : (interp 0).K) ∈ (interp 0).node "GF(p^1)" :=
  MldsaANodes.natCast_mem n

theorem bitA_mem {z : (interp 0).K} (h : z = 0 ∨ z = 1) : z ∈ (interp 0).node "GF(p^1)" := by
  rcases h with rfl | rfl
  · exact_mod_cast natCast_mem_prime (F0 := F0) (FH := FH) 0
  · exact_mod_cast natCast_mem_prime (F0 := F0) (FH := FH) 1

theorem dite_mem_zero {K : Type*} [Field K] {S : AddSubgroup K} {p : Prop} [Decidable p]
    {f : p → K} (h : ¬ p) : (if hp : p then f hp else 0) ∈ S := by
  rw [dif_neg h]
  exact zero_mem _

end Prime

variable {program : RealizedProgram} [MldsaEAlgebra program] {F0 FH : FieldInterp} [AField F0]
  [MldsaANodes F0] [HField FH] [MldsaHHonest nat] [MldsaHSample nat] [MldsaHSelHonest nat]
  [MldsaHConsts nat FH] [Native.ROMParams.MldsaHNativeData FH] [MldsaHNodes FH]
  [hE : MldsaEmulatedHonest program F0 FH]

open MldsaEmulatedHonest

variable (program F0 FH) in
/-- **The honest relation**: the statement is the input's key's (`MldsaEmulatedHonest.stmtOfKey`). -/
def relH : Set (program.Valuation interp × HonestInput) :=
  {p | p.1 = hE.stmtOfKey p.2.y.key}

variable (program F0 FH) in
/-- **The statement of an honest input**: its key's. -/
noncomputable def stmtH (i : HonestInput) : program.Valuation interp := hE.stmtOfKey i.y.key

/-! ## The cells' bases and the node types -/

theorem mem_castElt_of_eq {a b : ℕ} (h : a = b) {S : String} {z : (interp a).K}
    (hz : z ∈ (interp a).node S) : (castElt z : (interp b).K) ∈ (interp b).node S := by
  subst h
  rwa [castElt_self]

/-- **The nodes of an emulated ML-DSA program contain `1`**: `GF(p^1)` of field `0`, `bit` and
`GF(2^16)` (the selection subfield's node, `MldsaHNodes.node_of_sel`) of field `1`. -/
theorem oneNodes : OneNodes interp [(0, "GF(p^1)"), (1, "bit"), (1, "GF(2^16)")] := by
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · simpa using natCast_mem_prime (F0 := F0) (FH := FH) 1
  · exact (MldsaHNodes.bit_iff (FH := FH) 1).2 (Or.inr rfl)
  · exact MldsaHNodes.node_of_sel (FH := FH) 1 (one_mem _)

theorem bitH_of_mem {z : (interp 1).K} (h : z ∈ (interp 1).node "bit") : z = 0 ∨ z = 1 :=
  (MldsaHNodes.bit_iff (FH := FH) z).1 h

section Mem

variable (i : HonestInput)

/-- **Domain `A`'s honest values lie in `F_p`**, at a layout whose values are distinct. -/
theorem aVal_mem {L' : MldsaELayout} (hnd : (aValues L').Nodup) {v : ℕ} (hv : v ∈ aValues L')
    (j : ℕ) : aVal F0 L' i v j ∈ (interp 0).node "GF(p^1)" := by
  have hAC := nativeEC (F0 := F0) i
  have hnat := natCast_mem_prime (F0 := F0) (FH := FH)
  rcases List.mem_append.1 hv with hf | hd
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · by_cases hj : j < 1024
      · rw [aVal_60 _ i hj]; exact bitA_mem (hAC.hBool _ _)
      · unfold aVal; rw [if_neg (by decide), if_neg (by decide)]; exact dite_mem_zero hj
    · by_cases hj : j < 512
      · rw [aVal_61 _ i hj]; exact bitA_mem (hAC.cBool _ _)
      · unfold aVal; rw [if_pos rfl]; exact dite_mem_zero hj
    · by_cases hj : j < 6144
      · rw [aVal_64 _ i hj]; exact bitA_mem (hAC.w1Bool _)
      · unfold aVal; rw [if_neg (by decide), if_pos rfl]; exact dite_mem_zero hj
    · by_cases hj : j < 1024
      · rw [aVal_65 _ i hj]; exact bitA_mem (hAC.npBool _ _)
      · unfold aVal; rw [if_neg (by decide), if_neg (by decide)]; exact dite_mem_zero hj
  · by_cases hj : j < 1024
    · obtain ⟨k, hk⟩ := aVal_digit_natCast (F0 := F0) i hnd hd hj
      rw [hk]
      exact hnat k
    · obtain ⟨h1, h2, -, -⟩ := aVal_digit_ne hnd hd
      unfold aVal
      rw [if_neg h1, if_neg h2]
      exact dite_mem_zero hj

end Mem

/-- **An honest committed coordinate lies in its value's node.** -/
theorem honest_cell_mem (i : HonestInput) (π : (program.layout interp).Pads) {v : ℕ}
    (hv : v < program.values.length) (hc : program.isCellValue (program.value v).domain v = true)
    (hsrc : program.IsSourceValue v)
    (j : ℕ) {S : String} (hS : (program.value v).node.map (·.name) = some S) :
    program.copyVal interp (honestVal program F0 FH i) π v j ∈
      (interp (program.valueField v)).node S := by
  have hcl := List.all_eq_true.1 (cell_classes (program := program)) v (List.mem_range.2 hv)
  simp only [hc, hsrc, decide_true, Bool.not_true, Bool.false_or, Bool.or_eq_true,
    Bool.and_eq_true, beq_iff_eq, hS, Option.some.injEq, List.contains_iff_mem,
    decide_eq_true_eq] at hcl
  have hpriv : v ≠ 569 → program.copyVal interp (honestVal program F0 FH i) π v j =
      honestVal program F0 FH i v j := by
    intro h569
    unfold RealizedProgram.copyVal
    split
    · rename_i u m hk
      exfalso
      have := List.all_eq_true.1 (padCopy_only (program := program)) v (List.mem_range.2 hv)
      simp [hk, h569] at this
    · rfl
  have hH : ∀ {S'}, program.valueField v = 1 → 1 ≤ v → v - 1 ∈ hV →
      hVal nat F0 FH i (v - 1) j ∈ (interp ((nat).valueField (v - 1))).node S' →
      honestVal program F0 FH i v j ∈ (interp (program.valueField v)).node S' := by
    intro S' hf h1 hvV hm
    have hnA : v ∉ aValues L := fun h => by
      have := (a_cells (program := program) v h).2
      omega
    obtain ⟨-, -, hfE, -⟩ := (MldsaEmbed.embedding (program := program)).vals (v - 1) hvV
    have hfE' : program.valueField v = (nat).valueField (v - 1) := by
      rw [← hfE]
      congr 1
      change v = v - 1 + 1
      omega
    unfold honestVal
    rw [if_neg hnA, if_pos ⟨h1, hvV⟩]
    exact mem_castElt_of_eq hfE'.symm hm
  rcases hcl with ((⟨⟨⟨⟨hf, rfl⟩, h1⟩, hvV⟩, hw⟩ | ⟨⟨⟨⟨hf, rfl⟩, h1⟩, hvV⟩, hb⟩) | ⟨⟨hf, rfl⟩, ha⟩)
  · have h569 : v ≠ 569 := by
      rintro rfl
      have := (blind_cells (program := program)).2.2.2.1
      omega
    rw [hpriv h569]
    obtain ⟨-, -, hfE, -⟩ := (MldsaEmbed.embedding (program := program)).vals (v - 1) hvV
    have hf' : (nat).valueField (v - 1) = 1 := by
      rw [← hfE]
      have : v - 1 + 1 = v := by omega
      change program.valueField (v - 1 + 1) = 1
      rw [this]
      exact hf
    exact hH hf h1 hvV (Native.ROMParams.hVal_mem_gf16 i hf' hw j)
  · have h569 : v ≠ 569 := by
      rintro rfl
      have := (blind_cells (program := program)).2.2.2.1
      omega
    rw [hpriv h569]
    obtain ⟨-, -, hfE, -⟩ := (MldsaEmbed.embedding (program := program)).vals (v - 1) hvV
    have hf' : (nat).valueField (v - 1) = 1 := by
      rw [← hfE]
      have : v - 1 + 1 = v := by omega
      change program.valueField (v - 1 + 1) = 1
      rw [this]
      exact hf
    exact hH hf h1 hvV (Native.ROMParams.hVal_mem_bit i hf' hb j)
  · rcases ha with ha | rfl
    · have h569 : v ≠ 569 := by
        rintro rfl
        have := kind_of_privCellB (a_cells (program := program) 569 ha).1
        rw [(blind_cells (program := program)).1] at this
        cases this
      rw [hpriv h569]
      unfold honestVal
      rw [if_pos ha]
      exact mem_castElt_of_eq (a := 0) hf.symm (aVal_mem (FH := FH) i a_nodup ha j)
    · unfold RealizedProgram.copyVal
      rw [(blind_cells (program := program)).1]
      simp only
      revert hf
      generalize program.valueField 569 = f
      intro hf
      subst hf
      unfold FieldInterp.ofBool
      split_ifs
      · exact bitA_mem (Or.inr rfl)
      · exact bitA_mem (Or.inl rfl)

/-- **The node-typed values lie in their types** at the source environment of the honest values
(`RealizedProgram.SourceSatAt.types`). -/
theorem honest_types (i : HonestInput) (x : program.Valuation interp)
    (c : ∀ k, (program.layout interp).Ch k) (π : (program.layout interp).Pads) (v : ℕ)
    (hv : v < program.values.length) (hts : (program.value v).typeSource = .node)
    (hl : ¬ program.IsLate v) (hsrc : program.IsSourceValue v) (j : ℕ)
    (hj : j < (program.value v).size) :
    (interp (program.valueField v)).InType (program.value v).type
      (program.reader (program.srcEnv interp x (honestVal program F0 FH i) c π) v j) := by
  have hcl := List.all_eq_true.1 (typed_classes (program := program)) v (List.mem_range.2 hv)
  simp only [hts, beq_self_eq_true, Bool.not_true, Bool.false_or, hl, decide_false,
    Bool.or_eq_true, Bool.and_eq_true] at hcl
  rcases hcl with ⟨hk, hty⟩ | ⟨⟨hp, hc⟩, hty⟩
  · simp only [beq_iff_eq] at hty
    rw [hty]
    revert hk
    rcases hkv : (program.value v).kind with _ | _ | _ | _ | _ | ⟨w, sel⟩ | _ | _ | _ <;>
      simp only [Bool.false_eq_true, IsEmpty.forall_iff]
    rcases hkw : (program.value w).kind <;> simp only [Bool.false_eq_true, IsEmpty.forall_iff]
    intro _
    rw [RealizedProgram.reader_of_bits_of_priv _ hkv hkw]
    unfold FieldInterp.ofBool
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  · rw [RealizedProgram.reader_srcEnv_of_privCellB x _ c π hp hj]
    have hmem : ∀ S, (program.value v).node.map (·.name) = some S →
        honestVal program F0 FH i v j ∈ (interp (program.valueField v)).node S := fun S hS => by
      have := honest_cell_mem i π hv hc hsrc j hS
      unfold RealizedProgram.copyVal at this
      split at this
      · rename_i u m hk
        have := kind_of_privCellB hp
        rw [hk] at this
        cases this
      · exact this
    revert hty
    cases hty' : (program.value v).type with
    | sub S =>
      intro hty
      exact hmem S (by simpa using hty)
    | bit =>
      intro hty
      simp only [Bool.and_eq_true, beq_iff_eq] at hty
      have := hmem "bit" hty.1
      revert this
      generalize honestVal program F0 FH i v j = z
      revert z
      rw [hty.2]
      intro z hz
      exact bitH_of_mem hz
    | field => intro _; trivial

/-! ## The execution of the source program -/

section Exec

variable (i : HonestInput) {c : ∀ k, (program.layout interp).Ch k} {π : (program.layout interp).Pads}

/-- **The source program holds at the source environment of the honest values**: its predicates
(`source_holds`, none a MAC role predicate) and its node-typed values' types (`honest_types`, no
source value late). -/
theorem source_sat
    (hsl : ∀ v < program.values.length, program.IsLate v → ¬ program.IsSourceValue v)
    (hsrc : ∀ q < program.predicates.length, program.inSource (program.predicate q) = true →
      q ∉ macRolePreds) :
    program.SourceSatAt (program.srcEnv interp (stmtH program F0 FH i) (honestVal program F0 FH i) c π) where
  preds p hp hs := by
    obtain ⟨q, hq, rfl⟩ := exists_index_of_mem hp
    exact source_holds i rfl hq (hsrc q hq hs) hs
  types v hv hs hts j hj :=
    honest_types i _ c π v hv hts (fun hl => hsl v hv hl hs) hs j hj

/-- **The source cross-field `equal`s read bits at the source environment of the honest values**:
the only one is the MAC's (`crossMac`), whose operands read bits (`srcMac_holds`). -/
theorem source_crossBits :
    program.CrossBitsAt interp
      (program.srcEnv interp (stmtH program F0 FH i) (honestVal program F0 FH i) c π) := by
  intro p hp _ dx x' dy y' k real hb
  have hS := srcMac_holds i (c := c) (π := π) rfl
  have he := crossMac (program := program) p hp dx x' dy y' k real hb
  rw [hE.mac.hb, hb] at he
  cases he
  obtain ⟨-, -, hdy, hy, -, hcdy, hcy⟩ := mac_shape (program := program)
  refine ⟨hS.xbits, ?_⟩
  rw [hcdy, hcy, ← hdy, ← hy]
  exact hS.ybits

end Exec

variable (program F0 FH) in
/-- **The execution of an emulated ML-DSA program's source program** (`RealizedProgram.SourceExecution`): at the
key's statement, the honest values `honestVal` read off by `execOf` (a value bound to its digits
as their number), no late value, no completeness event. The source program accepts (`source_sat`,
`source_crossBits`); no `mod_q` has the field form. -/
noncomputable def sourceExecution {Gn : RealizedProgram.Gens} (R : program.CommittedFacts interp Gn)
    (hbc : program.BoundNoCopy)
    (hsl : ∀ v < program.values.length, program.IsLate v → ¬ program.IsSourceValue v)
    (hk : program.KprivTyped)
    (hone : program.BoundOneMem interp)
    (hsrc : ∀ q < program.predicates.length, program.inSource (program.predicate q) = true →
      q ∉ macRolePreds)
    (hff : ∀ p < program.predicates.length, program.isFieldForm p = false)
    (hng : program.NoGammaTables) :
    program.SourceExecution interp (relH program F0 FH) where
  packFree _ _ _ _ _ := RealizedProgram.packFreeAt_of_noGamma hng _
  stmtOf := stmtH program F0 FH
  stmt _ _ h := h
  val i := program.execOf interp (honestVal program F0 FH i)
  late _ _ := 0
  respects _ _ _ _ _ _ _ := rfl
  bad _ _ _ _ := False
  δ _ := 0
  badBound _ _ _ _ _ := by simp [IOP.probUniform]
  checks x i _ := by
    intro m hm
    rw [MldsaEmulatedHonest.checks (program := program)] at hm
    cases hm
  bounded x i h := by
    have h' : x = hE.stmtOfKey i.y.key := h
    rw [h']
    exact bounded i
  accepting x i hx c _ := by
    rw [show x = stmtH program F0 FH i from hx]
    exact sourceAcceptingAtC_of_srcEnv (l := 0) (π := 0) hE.wellFormed hE.registered hE.lawful R hbc hk hone
      (by rw [RealizedProgram.srcEnvL_zero]; exact source_sat i hsl hsrc)
      (by rw [RealizedProgram.srcEnvL_zero]; exact source_crossBits i)
  fieldEqs _ _ _ _ _ := RealizedProgram.fieldEqsAt_of_none hff _

end GordieHowe.MLDSA44.Emulated
