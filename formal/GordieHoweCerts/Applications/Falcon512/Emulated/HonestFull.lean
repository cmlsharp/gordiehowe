-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Completeness.Roles
public import GordieHoweCerts.Applications.Falcon512.Emulated.HonestAlgebra
public import GordieHowe.Language.Honest.Digits

@[expose] public section

/-!
# GordieHowe: the honest execution of an emulated Falcon program

The execution of the source program of an emulated Falcon program
(`GordieHowe.RealizedProgram.SourceExecution`) on the honest inputs of the native programs
(`GordieHowe.Falcon512.Native.HonestIn`): the honest valuation of the source values (`honestVal`:
the hash's inputs `hashVal`, the selection's `selVal`, domain `A`'s `aVal`), the source
predicates, the crossing's operands' bits and the committed cells' nodes at the source environment
(`source_holds`, `cross_bits`, `honest_cell_mem`) and the execution (`sourceExecution`) at the
program's honest roles (`GordieHowe.RealizedProgram.HonestRoles`), from which
`GordieHowe.RealizedProgram.HonestStrategy.ofCompletionReady` builds the honest strategy. Generic in
the program (`FalconEHonestFull`: the crossing's operands, the covering of the source predicates
and the committed cells' classes, decided per program) and the fields.
-/

namespace GordieHowe.Falcon512.Emulated

open GordieHowe.Bits RealizedProgram
open _root_.GordieHowe.Falcon512.Emulated.Params
open Native (HonestIn)

set_option linter.unusedSectionVars false

variable {program : RealizedProgram} [FalconACore program] [FalconEAlg program]
  [FalconEHonest program] {FH FA : FieldInterp} [HField FH] [EField FA] [FalconHBase program]

set_option hygiene false in
local notation "interp" => falconInterpOf FH FA

variable (program FH FA) in
/-- **The honest relation**: the statement is the input's key's (`stmtOf`). -/
def relH : Set (program.Valuation interp × HonestIn) :=
  {p | p.1 = stmtOf p.2.y.pk}

/-! ## The honest valuation -/

variable [FalconHHonest program] [FalconHSelHonest program] [FalconHConsts program FH]
  [FalconSelField program FH FA]

variable (program FH FA) in
/-- **The honest source values** of an honest input (`hashVal`, `selVal`, `aVal`); `0` for every
other value (the realization's values are generated, `RealizedProgram.genCommitted`; a value bound
to its digits reads them, `RealizedProgram.execOf`).

Running time: computing these values takes eleven Keccak-f permutations, one negacyclic product,
and a constant number of digit operations per coefficient. This running time is argued here, not
proved in Lean. -/
-- spec-side
noncomputable def honestVal (i : HonestIn) (v j : ℕ) : (interp (program.valueField v)).K :=
  if IsHashValue v then hashVal i.y v j
  else if v ∈ [588, 590, 591] then selVal program FH FA i.y v j
  else if v ∈ aValues then aVal program FH FA i.y v j
  else 0

/-- **The selection's values are none of the hash's.** -/
theorem sel_not_hash : ∀ v ∈ [588, 590, 591], ¬ IsHashValue v := by
  decide +kernel

/-- **Domain `A`'s values are none of the hash's or the selection's.** -/
theorem aValues_not_hash : ∀ v ∈ aValues, ¬ IsHashValue v ∧ v ∉ [588, 590, 591] := by
  decide +kernel

theorem honestVal_hash (i : HonestIn) : ∀ v, IsHashValue v →
    honestVal program FH FA i v = hashVal i.y v :=
  fun v hv => funext fun j => by unfold honestVal; rw [if_pos hv]

theorem honestVal_sel (i : HonestIn) : ∀ v ∈ [588, 590, 591],
    honestVal program FH FA i v = selVal program FH FA i.y v :=
  fun v hv => funext fun j => by
    unfold honestVal
    rw [if_neg (sel_not_hash v hv), if_pos hv]

theorem honestVal_a (i : HonestIn) : ∀ v ∈ aValues,
    honestVal program FH FA i v = aVal program FH FA i.y v :=
  fun v hv => funext fun j => by
    unfold honestVal
    rw [if_neg (aValues_not_hash v hv).1, if_neg (aValues_not_hash v hv).2, if_pos hv]

/-! ## The program facts -/

/-- **The source predicates outside the hash's**: the selection's four, the magnitudes, the norm,
`c_A`'s type check, the five ranges, the signature equation, `encoding.high2` and `mac.equal`. -/
def aPreds : List ℕ := [270, 271, 272, 273, 275, 276, 277, 284, 286, 287, 288, 289, 290, 297, 298, 299]

variable (program) in
/-- **The program facts of the honest strategy of an emulated Falcon program** (each program
instantiates them by `decide`): the statement bounds (`hhat` and `key.coefficients` below `q`), the
operands of every cross-field `equal` (`x_H = 589`, `y_A = 595`), the covering of the source
predicates (`src_cover`), the statement's one member check and the committed source cells'
classes. The program-wide facts every honest strategy reads are the honest roles
(`RealizedProgram.HonestRoles`). -/
class FalconEHonestFull (PN : outParam (ℕ → List String)) where
  /-- The program's statement bounds: `hhat` and the key's coefficients below `q`. -/
  bounds : program.declaredRanges = [(593, 12289), (594, 12289)]
  /-- Every cross-field `equal` crosses the raw view `589` of domain `H` and `c_A` (`595`) of
  domain `A`. -/
  crossOperands : program.crossOperandsB 0 (.leaf 589) 1 (.leaf 595) = true
  /-- Every source predicate is the hash's or of `aPreds`. -/
  src_cover : ∀ q < program.predicates.length, program.inSource (program.predicate q) = true →
    q < 270 ∨ q ∈ aPreds
  /-- The statement's one member check: the key below `q`. -/
  checks_list : program.statement.checks = [⟨"hhat", 0, 1024, "falcon_key_canonical", [12289]⟩]
  /-- The committed source cells' classes. -/
  cell_classes : (List.range program.values.length).all (fun v =>
    !program.privCellB v || !decide (program.IsSourceValue v) ||
      (program.valueField v == 0 && (program.value v).node.map (·.name) == some "GF(2^16)" &&
        (v == 96 || (wordsOwner? v).isSome || v == 588 || v == 590)) ||
      (program.valueField v == 0 && (program.value v).node.map (·.name) == some "bit" &&
        [45, 46, 47, 591].contains v) ||
      (program.valueField v == 1 && (program.value v).node.map (·.name) == some "GF(p^1)" &&
        aValues.contains v)) = true

open FalconEHonestFull

variable {PN : ℕ → List String} [hfull : FalconEHonestFull program PN]
include hfull

/-! ## The source predicates at the honest values -/

section Holds

variable (i : HonestIn) {x : program.Valuation interp} {c : ∀ k, (program.layout interp).Ch k}
  {π : (program.layout interp).Pads}

/-- **Every source predicate holds** at the source environment of the honest values at the key's
statement: the hash (`shake_holds_honest`), the selection (`select_holds`) and domain `A`'s
predicates and the crossing (`GordieHoweCerts/Applications/Falcon512/Emulated/HonestAlgebra.lean`). -/
theorem source_holds (hx : x = stmtOf i.y.pk) {q : ℕ} (hq : q < program.predicates.length)
    (hs : program.inSource (program.predicate q) = true) :
    program.HoldsAt (program.srcEnv interp x (honestVal program FH FA i) c π)
      (program.predicate q).body := by
  have hh := honestVal_hash (program := program) (FH := FH) (FA := FA) i
  have hsel := honestVal_sel (program := program) (FH := FH) (FA := FA) i
  have ha := honestVal_a (program := program) (FH := FH) (FA := FA) i
  have hk : keyOf x = some i.y.pk := by rw [hx]; exact keyOf_stmtOf _
  rcases FalconEHonestFull.src_cover (program := program) (PN := PN) q hq hs with h270 | hA
  · exact shake_holds_honest i.hL hh h270
  obtain ⟨s1, s2, s3, s4⟩ := select_holds (x := x) (c := c) (π := π) i.hL i.valid hh hsel
  have hr := ranges_honest (x := x) (c := c) (π := π) ha i.valid
  simp only [aPreds, List.mem_cons, List.not_mem_nil, or_false] at hA
  rcases hA with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  · exact s1
  · exact s2
  · exact s3
  · exact s4
  · exact magS1_honest ha
  · exact magS2_honest ha
  · exact normSum_honest ha i.valid
  · exact cABool_honest ha
  · exact hr _ (by simp)
  · exact hr _ (by simp)
  · exact hr _ (by simp)
  · exact hr _ (by simp)
  · exact hr _ (by simp)
  · exact sig_honest ha i.valid hk
  · exact high2_honest ha i.valid
  · exact cross_honest hsel ha

end Holds

/-! ## The crossing's operands -/

section Mac

variable (i : HonestIn) {x : program.Valuation interp} {c : ∀ k, (program.layout interp).Ch k}
  {π : (program.layout interp).Pads}

/-- **The crossing's operands read bits** at the honest values: the raw view `589` in domain `H`
and `c_A` (`595`) in domain `A`. -/
theorem cross_bits :
    (∀ j < program.exprLen (.leaf 589),
      program.evalWith (program.reader (program.srcEnv interp x (honestVal program FH FA i) c π)) 0
        (.leaf 589) j = 0 ∨
      program.evalWith (program.reader (program.srcEnv interp x (honestVal program FH FA i) c π)) 0
        (.leaf 589) j = 1) ∧
    ∀ j < program.exprLen (.leaf 595),
      program.evalWith (program.reader (program.srcEnv interp x (honestVal program FH FA i) c π)) 1
        (.leaf 595) j = 0 ∨
      program.evalWith (program.reader (program.srcEnv interp x (honestVal program FH FA i) c π)) 1
        (.leaf 595) j = 1 := by
  have hsel := honestVal_sel (program := program) (FH := FH) (FA := FA) i
  have ha := honestVal_a (program := program) (FH := FH) (FA := FA) i
  have hsz : program.exprLen (.leaf 589) = 8192 := by
    rw [exprLen_leaf]; exact (FalconACore.raw_facts (program := program)).2.1
  have hszy : program.exprLen (.leaf 595) = 8192 := by
    rw [exprLen_leaf]; exact cA_size (program := program)
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · rw [hsz] at hj
    unfold evalWith
    rw [FalconHBase.domainField0 (program := program)]
    rw [raw_honest hsel hj]
    rcases (show aNat i.y 595 j = 0 ∨ aNat i.y 595 j = 1 by
      have := aNat_595_lt (y := i.y) j; omega) with h0 | h0 <;> rw [h0] <;> simp
  · rw [hszy] at hj
    unfold evalWith
    rw [FalconACore.domainField1 (program := program)]
    exact rd_cA_bool ha hj

end Mac

/-! ## The cells' bases and the node types -/

omit hfull in
theorem mem_castElt_of_eq {a b : ℕ} (h : a = b) {S : String} {z : (interp a).K}
    (hz : z ∈ (interp a).node S) : (castElt z : (interp b).K) ∈ (interp b).node S := by
  subst h
  rwa [castElt_self]

omit hfull in
/-- **The naturals lie in `F_p`** in domain `A`'s field. -/
theorem natCast_mem_prime [Ring.PrimeNode FA] (n : ℕ) :
    (n : (interp 1).K) ∈ (interp 1).node "GF(p^1)" := by
  obtain ⟨S, hS⟩ := Ring.PrimeNode.subfield (FA := FA)
  exact (hS _).2 (natCast_mem S n)

omit hfull in
/-- The packed words lie in `GF(2^16)`. -/
theorem gf16_mem_pack (bits : Fin (2 ^ 4) → Bool) :
    (PackedClaim.pack (HField.packing (FH := FH)) bits : (interp 0).K) ∈
      (interp 0).node "GF(2^16)" :=
  (HField.node16 (FH := FH) _).2 (HField.pack_mem _)

omit hfull in
/-- The selection's labels lie in `GF(2^16)` of the selection's field. -/
theorem gf16_mem_gpow (k : ℕ) :
    ((selF (program := program) (FH := FH) (FA := FA)).g ^ k :
        (interp (SelectShape.field program selShape)).K) ∈
      (interp (SelectShape.field program selShape)).node "GF(2^16)" :=
  (HField.node16 (FH := SelField program FH FA) _).2
    (Subring.pow_mem _ (HField.g_mem (FH := SelField program FH FA)) k)

omit hfull in
theorem bit_mem {z : (interp 0).K} (hz : z = 0 ∨ z = 1) : z ∈ (interp 0).node "bit" :=
  (HField.nodeBit (FH := FH) z).2 hz

omit hfull in
theorem bit_mem_sel {z : (interp (SelectShape.field program selShape)).K} (hz : z = 0 ∨ z = 1) :
    z ∈ (interp (SelectShape.field program selShape)).node "bit" :=
  (HField.nodeBit (FH := SelField program FH FA) z).2 hz

variable [Ring.PrimeNode FA]

/-- **An honest committed source cell lies in its value's node.** -/
theorem honest_cell_mem (i : HonestIn) {v : ℕ} (hv : v < program.values.length)
    (hp : program.privCellB v = true) (hsrc : program.IsSourceValue v)
    (j : ℕ) {S : String} (hS : (program.value v).node.map (·.name) = some S) :
    honestVal program FH FA i v j ∈ (interp (program.valueField v)).node S := by
  have hcl := List.all_eq_true.1 (FalconEHonestFull.cell_classes (program := program)) v
    (List.mem_range.2 hv)
  simp only [hp, hsrc, decide_true, Bool.not_true, Bool.false_or, Bool.or_eq_true,
    Bool.and_eq_true, beq_iff_eq, hS, Option.some.injEq, List.contains_iff_mem] at hcl
  have hsf := selField (program := program)
  rcases hcl with (⟨⟨hf, rfl⟩, hw⟩ | ⟨⟨hf, rfl⟩, hb⟩) | ⟨⟨hf, rfl⟩, ha⟩
  · have hw' : (v = 96 ∨ (wordsOwner? v).isSome) ∨ v = 588 ∨ v = 590 := by tauto
    rcases hw' with hh | hs
    · have hH : IsHashValue v := by unfold IsHashValue; tauto
      rw [honestVal_hash i v hH]
      have h45 : v ≠ 45 ∧ v ≠ 46 ∧ v ≠ 47 := by
        obtain ⟨-, w45, w46, w47, -⟩ := wordsOwner_checks
        refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> rcases hh with h | h <;> simp_all
      unfold hashVal
      rw [if_neg h45.1, if_neg h45.2.1, if_neg h45.2.2]
      split_ifs with h96
      · exact mem_castElt_of_eq (a := 0) hf.symm (by unfold stateWords; exact gf16_mem_pack _)
      · split
        · exact mem_castElt_of_eq (a := 0) hf.symm (by unfold stateWords; exact gf16_mem_pack _)
        · exact zero_mem _
    · rw [honestVal_sel i v (by rcases hs with rfl | rfl <;> simp)]
      unfold selVal
      rcases hs with rfl | rfl
      · rw [if_pos rfl]
        exact mem_castElt_of_eq (a := 0) hf.symm (gf16_mem_pack _)
      · rw [if_neg (by norm_num), if_pos rfl]
        refine mem_castElt_of_eq (a := SelectShape.field program selShape) (hsf.trans hf.symm) ?_
        by_cases hj : j < 717
        · simp only [hj, ↓reduceDIte]
          unfold hRoute SelectFirstCutoff.Model.honestRoute
          exact gf16_mem_gpow _
        · simp only [hj, ↓reduceDIte]
          exact zero_mem _
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · rw [honestVal_hash i 45 (Or.inl rfl)]
      unfold hashVal
      rw [if_pos rfl]
      by_cases hj : j < 320
      · simp only [hj, ↓reduceDIte]
        exact mem_castElt_of_eq (a := 0) hf.symm (bit_mem (hBlock_bool _ _))
      · simp only [hj, ↓reduceDIte]
        exact zero_mem _
    · rw [honestVal_hash i 46 (Or.inr (Or.inl rfl))]
      unfold hashVal
      rw [if_neg (by norm_num), if_pos rfl]
      by_cases hj : j < 768
      · simp only [hj, ↓reduceDIte]
        exact mem_castElt_of_eq (a := 0) hf.symm (bit_mem (hBlock_bool _ _))
      · simp only [hj, ↓reduceDIte]
        exact zero_mem _
    · rw [honestVal_hash i 47 (Or.inr (Or.inr (Or.inl rfl)))]
      unfold hashVal
      rw [if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]
      refine mem_castElt_of_eq (a := 0) hf.symm (bit_mem ?_)
      split_ifs
      · exact Or.inr rfl
      · exact Or.inl rfl
    · rw [honestVal_sel i 591 (by simp)]
      unfold selVal
      rw [if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]
      refine mem_castElt_of_eq (a := SelectShape.field program selShape) (hsf.trans hf.symm) ?_
      by_cases hj : j < 205
      · simp only [hj, ↓reduceDIte]
        refine bit_mem_sel ?_
        unfold hRoute SelectFirstCutoff.Model.honestRoute
        dsimp only
        split_ifs
        · exact Or.inr rfl
        · exact Or.inl rfl
      · simp only [hj, ↓reduceDIte]
        exact zero_mem _
  · rw [honestVal_a i v ha]
    unfold aVal
    exact mem_castElt_of_eq (a := 1) hf.symm (natCast_mem_prime _)

/-- **A key's statement passes the member check** (`falcon_key_canonical`: `key_hat` below `q`). -/
theorem checks_stmtOf (pk : PublicKey) :
    program.StatementOk interp (stmtOf pk : program.Valuation interp) := by
  intro m hm
  rw [FalconEHonestFull.checks_list (program := program), List.mem_singleton] at hm
  subst hm
  have hv : program.memberValue? "hhat" = some 593 := FalconACore.hhatValue
  have hq : (MemberCheck.mk "hhat" 0 1024 "falcon_key_canonical" [12289]).entryBound? =
      some 12289 := by decide
  unfold MemberHolds
  rw [hv, hq]
  intro i hi
  rw [FalconACore.hhatSize] at hi
  rw [stmtOf_hhat pk ⟨i, hi⟩, toNat_castElt FalconACore.hhatField.symm]
  erw [AReading.toNat_natCast (FA := FA) (KeyNTT.keyHat_lt pk ⟨i, hi⟩)]
  exact KeyNTT.keyHat_lt pk ⟨i, hi⟩

omit [Ring.PrimeNode FA] in
/-- **A key's statement lies within the declared bounds**: `hhat` holds the key's transform below
`q`, and `key.coefficients`, computed from it, is below `q` (`falconOps_key_lt`). -/
theorem bounded_stmtOf (pk : PublicKey) :
    program.StmtBounded interp (stmtOf pk : program.Valuation interp) := by
  intro vN hvN j hj
  rw [FalconEHonestFull.bounds (program := program)] at hvN
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hvN
  rcases hvN with rfl | rfl
  · rw [FalconACore.hhatSize] at hj
    refine ⟨_, KeyNTT.keyHat_lt pk ⟨j, hj⟩, ?_⟩
    rw [stmtRead_of_isStmtLeaf _
      (by rw [FalconEAlg.hhatKind (program := program)]; rfl), stmtOf_hhat pk ⟨j, hj⟩]
    exact castElt_natCast FalconACore.hhatField.symm _
  · have hf594 := FalconEAlg.fields (program := program) 594 (by simp)
    refine ⟨keyNat (stmtOf pk : program.Valuation interp) j, keyCoeffs_lt _ j, ?_⟩
    have hlt : keyNat (stmtOf pk : program.Valuation interp) j < pGold :=
      (keyCoeffs_lt _ j).trans (by norm_num [pGold])
    simp only [stmtRead, FalconEAlg.keyKind (program := program), List.map_cons, List.map_nil]
    show (interp _).decode (falconOps "key.coefficients" _ j) = _
    rw [falconOps_key]
    change (interp (program.valueField 594)).decode (keyNat (stmtOf pk : program.Valuation interp) j) = _
    revert hf594
    generalize program.valueField 594 = f
    intro hf594
    subst hf594
    exact decode1 hlt

/-! ## The execution of the source program -/

omit hfull in
/-- **The nodes of an emulated Falcon program contain `1`**: `GF(2^16)` and `bit` of field `0`,
`GF(p^1)` of field `1`. -/
theorem one_mem_node {f : ℕ} {S : String}
    (h : (f = 0 ∧ (S = "GF(2^16)" ∨ S = "bit")) ∨ (f = 1 ∧ S = "GF(p^1)")) :
    (1 : (interp f).K) ∈ (interp f).node S := by
  rcases h with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩
  · exact (HField.node16 (FH := FH) 1).2 (one_mem _)
  · exact bit_mem (Or.inr rfl)
  · simpa using natCast_mem_prime (FH := FH) (FA := FA) 1

omit hfull in
/-- **The nodes of an emulated Falcon program contain `1`** (`one_mem_node`). -/
theorem oneNodes :
    OneNodes interp [(0, "bit"), (0, "GF(2^16)"), (1, "GF(p^1)")] := by
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact one_mem_node (Or.inl ⟨rfl, Or.inr rfl⟩)
  · exact one_mem_node (Or.inl ⟨rfl, Or.inl rfl⟩)
  · exact one_mem_node (Or.inr ⟨rfl, rfl⟩)

section Exec

variable (i : HonestIn) {x : program.Valuation interp} {c : ∀ k, (program.layout interp).Ch k}
  {π : (program.layout interp).Pads} {L : List (ℕ × String)} {S : RealizedProgram.Structure}

/-- **The source program holds at the source environment of the honest values**: its predicates
(`source_holds`) and its node-typed values' types (`RealizedProgram.HonestRoles.sourceSatAt` at the
honest cells' nodes, `honest_cell_mem`). -/
theorem source_sat (hx : x = stmtOf i.y.pk) (hR : program.HonestRoles L S)
    (hbit : (interp).BitNodes program) :
    program.SourceSatAt (program.srcEnv interp x (honestVal program FH FA i) c π) :=
  hR.sourceSatAt hbit (fun _ hv hp hs j _ hS => honest_cell_mem i hv hp hs j hS) fun p hp hs => by
    obtain ⟨q, hq, rfl⟩ := exists_index_of_mem hp
    exact source_holds i hx hq hs

omit [Ring.PrimeNode FA] in
/-- **The source cross-field `equal`s read bits at the source environment of the honest values**:
every one crosses the raw view and `c_A` (`FalconEHonestFull.crossOperands`), which read bits
(`cross_bits`). -/
theorem source_crossBits :
    program.CrossBitsAt interp (program.srcEnv interp x (honestVal program FH FA i) c π) :=
  crossBitsAt_of_operands (FalconEHonestFull.crossOperands (program := program) (PN := PN))
    (cross_bits i (x := x) (c := c) (π := π)).1 (cross_bits i (x := x) (c := c) (π := π)).2

end Exec

variable (program FH FA PN) in
/-- **The execution of an emulated Falcon program's source program**
(`RealizedProgram.SourceExecution`): at the key's statement, the honest values `honestVal` read
off by `execOf` (a value bound to its digits as their number), no late value, no completeness
event. The source program accepts (`source_sat` at the honest roles `hR`, `source_crossBits`); no
`mod_q` has the field form. -/
noncomputable def sourceExecution (hwf : program.WellFormed) (hI : Interp.Registered interp program)
    (hL : Interp.Lawful interp program PN) {Gn : RealizedProgram.Gens}
    (R : program.CommittedFacts interp Gn) (hbc : program.BoundNoCopy)
    {L : List (ℕ × String)} {S : RealizedProgram.Structure} (hR : program.HonestRoles L S)
    (hO : OneNodes interp L) (hbit : (interp).BitNodes program)
    (hff : ∀ p < program.predicates.length, program.isFieldForm p = false) :
    program.SourceExecution interp (relH program FH FA) where
  packFree _ _ _ _ _ := packFreeAt_of_noGamma hR.noGamma _
  stmtOf i := stmtOf i.y.pk
  stmt _ _ h := h
  val i := program.execOf interp (honestVal program FH FA i)
  late _ _ := 0
  respects _ _ _ _ _ _ _ := rfl
  bad _ _ _ _ := False
  δ _ := 0
  badBound _ _ _ _ _ := by simp [IOP.probUniform]
  checks x i h := by
    rw [show x = stmtOf i.y.pk from h]
    exact checks_stmtOf _
  bounded x i h := by
    rw [show x = stmtOf i.y.pk from h]
    exact bounded_stmtOf _
  accepting x i hx c _ :=
    sourceAcceptingAtC_of_srcEnv (l := 0) (π := 0) hwf hI hL R hbc hR.kprivTyped (hR.boundOneMem hO)
      (by rw [srcEnvL_zero]; exact source_sat i hx hR hbit)
      (by rw [srcEnvL_zero]; exact source_crossBits i)
  fieldEqs _ _ _ _ _ := fieldEqsAt_of_none hff _

/-- **The execution of an emulated Falcon program's source program has no completeness error.** -/
theorem sourceExecution_δ (hwf : program.WellFormed) (hI : Interp.Registered interp program)
    (hL : Interp.Lawful interp program PN) {Gn : RealizedProgram.Gens}
    (R : program.CommittedFacts interp Gn) (hbc : program.BoundNoCopy)
    {L : List (ℕ × String)} {S : RealizedProgram.Structure} (hR : program.HonestRoles L S)
    (hO : OneNodes interp L) (hbit : (interp).BitNodes program)
    (hff : ∀ p < program.predicates.length, program.isFieldForm p = false) :
    (sourceExecution program FH FA PN hwf hI hL R hbc hR hO hbit hff).δ = 0 := rfl

end GordieHowe.Falcon512.Emulated
