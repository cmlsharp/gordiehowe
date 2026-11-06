-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Native.ROMParams.Facts
public import GordieHowe.Applications.MLDSA44.Native.SourceValues
public import GordieHowe.Applications.MLDSA44.Native.AlgebraSourceRoles
public import GordieHowe.Applications.MLDSA44.Honest.HashRoleSemantics
public import GordieHowe.Applications.MLDSA44.Honest.SelectionRoleSemantics
public import GordieHowe.Generated.MLDSA44.Native.ROMParams.SourceRoleFacts

public section

/-! Checked role placement and coverage are transported to the unchanged honest witness values.
Only source coordinates required by execution are compared; generated digits remain completion data. -/

open GordieHowe RealizedProgram GordieHowe.Keccak GordieHowe.KeccakTrace
namespace GordieHowe.MLDSA44.Native.ROMParams.SourceRoleSemantics
open _root_.GordieHowe.Generated.MLDSA44.Native.ROMParams.Program (program)
open _root_.GordieHowe.Generated.MLDSA44.Native.ROMParams.SourceRoles (classifier)
variable {F0 FH : FieldInterp} [QField F0] [HField FH]
  [MldsaHConsts program FH] [MldsaHNativeData FH] [MldsaHNodes FH]
  [MldsaNativeHonest program F0 FH]
set_option hygiene false in
local notation "interp" => mldsaInterpOf F0 FH
set_option hygiene false in
local notation "algebraInputs" => ({
  z := fun j => if h : j < 1024 then
    ((MLDSA44.NativeAlgebraCircuit.flat
      (MLDSA44.NativeAlgebraCircuit.Honest.zCentered i.y.z) (fmz j h) : Int) : F0.K) else 0
  hint := fun j => if h : j < 1024 then MLDSA44.NativeAlgebraCircuit.flat (nativeA F0 i).h (fm j h) else 0
  challenge := fun j => if h : j < 512 then
    (nativeA F0 i).cA ⟨j / 2, by change j / 2 < 256; omega⟩ ⟨j % 2, by omega⟩ else 0
  w := fun j => if h : j < 1024 then MLDSA44.NativeAlgebraCircuit.flat (nativeA F0 i).w (fm j h) else 0
  w1 := fun j => if h : j < 6144 then MLDSA44.NativeAlgebraCircuit.outputBits (nativeA F0 i).w1A
    ⟨j / 6, by change j / 6 < 4 * 256; omega⟩ ⟨j % 6, by change j % 6 < 6; omega⟩ else 0
  nonpositive := fun j => if h : j < 1024 then MLDSA44.NativeAlgebraCircuit.flat (nativeA F0 i).np (fm j h) else 0
  offset := fun j => if h : j < 1024 then ((offN i (fm j h) : Nat) : F0.K) else 0
  slack := fun j => if h : j < 1024 then ((slN i (fm j h) : Nat) : F0.K) else 0
} : AlgebraSourceValues F0.K)

set_option hygiene false in
local notation "hashInputs" => (⟨(honestData (K := FH.K) i.y).buf,
  (fun j => ((flagNat i.L j : Nat) : FH.K)),
  packWord (honestData (K := FH.K) i.y).w1,
  packWord (honestData (K := FH.K) i.y).mu,
  (fun p t j => if hp : p < 10 then if ht : t < 24 then
    stateWords HField.packing
      (iterRounds ((honestData (K := FH.K) i.y).states ⟨p, hp⟩) (t + 1)) j
    else 0 else 0)⟩ : HashSourceValues FH.K)

set_option hygiene false in
local notation "selectionInputs" => ({
  selected := jF FH i
  threshold := packWord (FH := FH) (lowF FH i)
  readValue := fun n => if h : n < 39 then ((honestMemW program F0 FH i).read ⟨n, h⟩).value else 0
  readOrigin := fun n => if h : n < 234 then
    ((honestMemW program F0 FH i).read ⟨n / 6, by change n / 6 < 39; omega⟩).origin ⟨n % 6, by omega⟩ else 0
  encoded := fun n => if h : n < 256 then (honestMemW program F0 FH i).cEnc ⟨n, h⟩ else 0
  finalOrigin := fun n => if h : n < 256 then (honestMemW program F0 FH i).finalOrigin ⟨n, h⟩ else 0
  unit := fun n => if h : n < 39 then
    MemoryShuffle.unit (samM program F0 FH).Θ ((honestMemW program F0 FH i).signs ⟨n, h⟩) else 0
  origin := fun n => if h : n < 39 then
    (samM program F0 FH).originOf ((honestMemW program F0 FH i).read ⟨n, h⟩).origin else 0
} : SelectionSourceValues FH.K)

variable (i : MLDSA44.HonestInput)

theorem h_exec {v : Nat} (hp : program.privCellB v = true)
    (hf : program.valueField v = 1) (j : Nat) :
    hVal program F0 FH i v j = program.execOf interp (honestVal program F0 FH i) v j := by
  rw [execOf_of_priv _ (kind_of_privCellB hp), honestVal_of_field i hf]

theorem hash_exec {v : Nat} (hp : program.privCellB v = true)
    (hf : program.valueField v = 1) (hv : IsHashValue v) (j : Nat) :
    hashVal (program := program) (F0 := F0) (FH := FH) i.y v j =
      program.execOf interp (honestVal program F0 FH i) v j := by
  rw [← hVal_hash i v hv]
  exact h_exec i hp hf j

theorem role_words (p : Fin 10) (t : Fin 24)
    (h : classifier.lookup (wordsVal p t) = some (.hashWord, 2 + 24 * (p : Nat) + (t : Nat))) (j : Nat) :
    sourceVal (program := program) algebraInputs hashInputs selectionInputs classifier (wordsVal p t) j =
      program.execOf interp (honestVal program F0 FH i) (wordsVal p t) j := by
  rw [sourceVal_hashWord _ _ _ h, hash_role_words i.y p t h]
  have hc := MldsaHHonest.words_checks (program := program) p t
  apply hash_exec i hc.2.1 hc.2.2.2.1
  exact Or.inr (Or.inr (Or.inr (Or.inr (by rw [(wordsOwner_checks).1 p t]; rfl))))

theorem role_hash_buffer
    (h : classifier.lookup 67 = some (.hashBit, 0)) (j : Nat) :
    sourceVal (program := program) algebraInputs hashInputs selectionInputs classifier 67 j =
      program.execOf interp (honestVal program F0 FH i) 67 j := by
  rw [sourceVal_hashBit _ _ _ h, hash_role_buffer i.y h]
  exact hash_exec i (MldsaHHonest.priv6869 (program := program)).1 (MldsaHHonest.priv6869 (program := program)).2.1 (by decide) j

theorem role_hash_flags
    (h : classifier.lookup 68 = some (.hashBit, 1)) (j : Nat) :
    sourceVal (program := program) algebraInputs hashInputs selectionInputs classifier 68 j =
      program.execOf interp (honestVal program F0 FH i) 68 j := by
  rw [sourceVal_hashBit _ _ _ h, hash_role_flags i.y h]
  exact hash_exec i (MldsaHHonest.priv6869 (program := program)).2.2.1 (MldsaHHonest.priv6869 (program := program)).2.2.2 (by decide) j

theorem role_hash_w1
    (h : classifier.lookup 69 = some (.hashWord, 0)) (j : Nat) :
    sourceVal (program := program) algebraInputs hashInputs selectionInputs classifier 69 j =
      program.execOf interp (honestVal program F0 FH i) 69 j := by
  rw [sourceVal_hashWord _ _ _ h, hash_role_w1 i.y h]
  exact hash_exec i (MldsaHHonest.view71 (program := program)).2.1 (MldsaHHonest.view71 (program := program)).2.2.2.1 (by decide) j

theorem role_hash_mu
    (h : classifier.lookup 119 = some (.hashWord, 1)) (j : Nat) :
    sourceVal (program := program) algebraInputs hashInputs selectionInputs classifier 119 j =
      program.execOf interp (honestVal program F0 FH i) 119 j := by
  rw [sourceVal_hashWord _ _ _ h, hash_role_mu i.y h]
  exact hash_exec i (MldsaHHonest.view121 (program := program)).2.1 (MldsaHHonest.view121 (program := program)).2.2.2.1 (by decide) j

theorem role_selection_selected
    (h : classifier.lookup 556 = some (.selection, 0)) (j : Nat) :
    sourceVal (program := program) algebraInputs hashInputs selectionInputs classifier 556 j =
      program.execOf interp (honestVal program F0 FH i) 556 j := by
  rw [sourceVal_selection _ _ _ h, selection_role_selected i h]
  exact h_exec i (MldsaHSelHonest.sel_cells (program := program)).2.2.2.2.2.2.2.2.2.1 (MldsaHSelHonest.sel_cells (program := program)).2.2.2.2.2.2.2.2.2.2.1 j

theorem role_selection_threshold
    (h : classifier.lookup 557 = some (.selection, 1)) (j : Nat) :
    sourceVal (program := program) algebraInputs hashInputs selectionInputs classifier 557 j =
      program.execOf interp (honestVal program F0 FH i) 557 j := by
  rw [sourceVal_selection _ _ _ h, selection_role_threshold i h]
  exact h_exec i (MldsaHSelHonest.sel_cells (program := program)).2.1 (MldsaHSelHonest.sel_cells (program := program)).2.2.2.1 j

theorem role_selection_read_value
    (h : classifier.lookup 560 = some (.selection, 2)) (j : Nat) :
    sourceVal (program := program) algebraInputs hashInputs selectionInputs classifier 560 j =
      program.execOf interp (honestVal program F0 FH i) 560 j := by
  rw [sourceVal_selection _ _ _ h, selection_role_read_value i h]
  exact h_exec i ((MldsaHSelHonest.mem_cells (program := program)).1 560 (by decide)).1 ((MldsaHSelHonest.mem_cells (program := program)).1 560 (by decide)).2 j

theorem role_selection_read_origin
    (h : classifier.lookup 561 = some (.selection, 3)) (j : Nat) :
    sourceVal (program := program) algebraInputs hashInputs selectionInputs classifier 561 j =
      program.execOf interp (honestVal program F0 FH i) 561 j := by
  rw [sourceVal_selection _ _ _ h, selection_role_read_origin i h]
  exact h_exec i ((MldsaHSelHonest.mem_cells (program := program)).1 561 (by decide)).1 ((MldsaHSelHonest.mem_cells (program := program)).1 561 (by decide)).2 j

theorem role_selection_encoded
    (h : classifier.lookup 562 = some (.selection, 4)) (j : Nat) :
    sourceVal (program := program) algebraInputs hashInputs selectionInputs classifier 562 j =
      program.execOf interp (honestVal program F0 FH i) 562 j := by
  rw [sourceVal_selection _ _ _ h, selection_role_encoded i h]
  exact h_exec i ((MldsaHSelHonest.mem_cells (program := program)).1 562 (by decide)).1 ((MldsaHSelHonest.mem_cells (program := program)).1 562 (by decide)).2 j

theorem role_selection_final_origin
    (h : classifier.lookup 563 = some (.selection, 5)) (j : Nat) :
    sourceVal (program := program) algebraInputs hashInputs selectionInputs classifier 563 j =
      program.execOf interp (honestVal program F0 FH i) 563 j := by
  rw [sourceVal_selection _ _ _ h, selection_role_final_origin i h]
  exact h_exec i ((MldsaHSelHonest.mem_cells (program := program)).1 563 (by decide)).1 ((MldsaHSelHonest.mem_cells (program := program)).1 563 (by decide)).2 j

theorem role_selection_unit
    (h : classifier.lookup 564 = some (.selection, 6)) (j : Nat) :
    sourceVal (program := program) algebraInputs hashInputs selectionInputs classifier 564 j =
      program.execOf interp (honestVal program F0 FH i) 564 j := by
  rw [sourceVal_selection _ _ _ h, selection_role_unit i h]
  exact h_exec i ((MldsaHSelHonest.mem_cells (program := program)).1 564 (by decide)).1 ((MldsaHSelHonest.mem_cells (program := program)).1 564 (by decide)).2 j

theorem role_selection_origin
    (h : classifier.lookup 565 = some (.selection, 7)) (j : Nat) :
    sourceVal (program := program) algebraInputs hashInputs selectionInputs classifier 565 j =
      program.execOf interp (honestVal program F0 FH i) 565 j := by
  rw [sourceVal_selection _ _ _ h, selection_role_origin i h]
  exact h_exec i ((MldsaHSelHonest.mem_cells (program := program)).1 565 (by decide)).1 ((MldsaHSelHonest.mem_cells (program := program)).1 565 (by decide)).2 j

theorem role_a_z
    (h : classifier.lookup 57 = some (.aWitness, 0)) {j : Nat} (hj : j < 1024) :
    sourceVal (program := program) algebraInputs hashInputs selectionInputs classifier 57 j =
      program.execOf interp (honestVal program F0 FH i) 57 j := by
  rw [sourceVal_algebra _ _ _ h]
  exact native_role_z i h hj

theorem role_a_hint
    (h : classifier.lookup 58 = some (.aWitness, 1)) {j : Nat} (hj : j < 1024) :
    sourceVal (program := program) algebraInputs hashInputs selectionInputs classifier 58 j =
      program.execOf interp (honestVal program F0 FH i) 58 j := by
  rw [sourceVal_algebra _ _ _ h]
  exact native_role_hint i h hj

theorem role_a_challenge
    (h : classifier.lookup 59 = some (.aWitness, 2)) {j : Nat} (hj : j < 512) :
    sourceVal (program := program) algebraInputs hashInputs selectionInputs classifier 59 j =
      program.execOf interp (honestVal program F0 FH i) 59 j := by
  rw [sourceVal_algebra _ _ _ h]
  exact native_role_challenge i h hj

theorem role_a_w
    (h : classifier.lookup 60 = some (.aWitness, 3)) {j : Nat} (hj : j < 1024) :
    sourceVal (program := program) algebraInputs hashInputs selectionInputs classifier 60 j =
      program.execOf interp (honestVal program F0 FH i) 60 j := by
  rw [sourceVal_algebra _ _ _ h]
  exact native_role_w i h hj

theorem role_a_w1
    (h : classifier.lookup 62 = some (.aWitness, 4)) {j : Nat} (hj : j < 6144) :
    sourceVal (program := program) algebraInputs hashInputs selectionInputs classifier 62 j =
      program.execOf interp (honestVal program F0 FH i) 62 j := by
  rw [sourceVal_algebra _ _ _ h]
  exact native_role_w1 i h hj

theorem role_a_nonpositive
    (h : classifier.lookup 63 = some (.aWitness, 5)) {j : Nat} (hj : j < 1024) :
    sourceVal (program := program) algebraInputs hashInputs selectionInputs classifier 63 j =
      program.execOf interp (honestVal program F0 FH i) 63 j := by
  rw [sourceVal_algebra _ _ _ h]
  exact native_role_nonpositive i h hj

theorem role_a_offset
    (h : classifier.lookup 64 = some (.aWitness, 6)) {j : Nat} (hj : j < 1024) :
    sourceVal (program := program) algebraInputs hashInputs selectionInputs classifier 64 j =
      program.execOf interp (honestVal program F0 FH i) 64 j := by
  rw [sourceVal_algebra _ _ _ h]
  exact native_role_offset i h hj

theorem role_a_slack
    (h : classifier.lookup 65 = some (.aWitness, 7)) {j : Nat} (hj : j < 1024) :
    sourceVal (program := program) algebraInputs hashInputs selectionInputs classifier 65 j =
      program.execOf interp (honestVal program F0 FH i) 65 j := by
  rw [sourceVal_algebra _ _ _ h]
  exact native_role_slack i h hj

theorem slot_perm (s : Nat) (h : s < 242) : (s - 2) / 24 < 10 := by omega
theorem slot_round (s : Nat) : (s - 2) % 24 < 24 := Nat.mod_lt _ (by decide)

/-- Finite semantic cases of the checked source-role metadata. -/
@[expose] def roleCase (r : SourceRoleEntry) : Prop :=
  r.value = 55 ∨
  r.value = 56 ∨
  r.value = 66 ∨
  (r.value = 57 ∧ r.role = .aWitness ∧ r.slot = 0) ∨
  (r.value = 58 ∧ r.role = .aWitness ∧ r.slot = 1) ∨
  (r.value = 59 ∧ r.role = .aWitness ∧ r.slot = 2) ∨
  (r.value = 60 ∧ r.role = .aWitness ∧ r.slot = 3) ∨
  (r.value = 62 ∧ r.role = .aWitness ∧ r.slot = 4) ∨
  (r.value = 63 ∧ r.role = .aWitness ∧ r.slot = 5) ∨
  (r.value = 64 ∧ r.role = .aWitness ∧ r.slot = 6) ∨
  (r.value = 65 ∧ r.role = .aWitness ∧ r.slot = 7) ∨
  (r.value = 67 ∧ r.role = .hashBit ∧ r.slot = 0) ∨
  (r.value = 68 ∧ r.role = .hashBit ∧ r.slot = 1) ∨
  (r.value = 69 ∧ r.role = .hashWord ∧ r.slot = 0) ∨
  (r.value = 119 ∧ r.role = .hashWord ∧ r.slot = 1) ∨
  (r.value = 556 ∧ r.role = .selection ∧ r.slot = 0) ∨
  (r.value = 557 ∧ r.role = .selection ∧ r.slot = 1) ∨
  (r.value = 560 ∧ r.role = .selection ∧ r.slot = 2) ∨
  (r.value = 561 ∧ r.role = .selection ∧ r.slot = 3) ∨
  (r.value = 562 ∧ r.role = .selection ∧ r.slot = 4) ∨
  (r.value = 563 ∧ r.role = .selection ∧ r.slot = 5) ∨
  (r.value = 564 ∧ r.role = .selection ∧ r.slot = 6) ∨
  (r.value = 565 ∧ r.role = .selection ∧ r.slot = 7) ∨
  (if h : 2 ≤ r.slot ∧ r.slot < 242 then
      r.value = wordsVal ⟨(r.slot - 2) / 24, by omega⟩ ⟨(r.slot - 2) % 24, by omega⟩ ∧
      r.role = .hashWord else False)
instance (r : SourceRoleEntry) : Decidable (roleCase r) := by
  unfold roleCase
  split_ifs
  all_goals
    repeat first | apply instDecidableOr | apply instDecidableAnd

theorem role_cases {r : SourceRoleEntry}
    (hm : r ∈ Generated.MLDSA44.Native.ROMParams.SourceRoles.roles) : roleCase r := by
  have h : Generated.MLDSA44.Native.ROMParams.SourceRoles.roles.all
      (fun r => decide (roleCase r)) = true := by
    rw [Generated.MLDSA44.Native.ROMParams.SourceRoles.roles_eq]
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h r hm)

/-- Every executable source coordinate agrees with the existing honest specification. -/
theorem role_source_coordinates {v j : Nat}
    (hs : program.IsSourceValue v) (hc : program.ExecCoord v j)
    (hpad : ∀ u < program.values.length, program.IsSourceValue u →
      (program.value u).kind.isPadCopy = false) :
    sourceVal (program := program) algebraInputs hashInputs selectionInputs classifier v j =
      program.execOf interp (honestVal program F0 FH i) v j := by
  have hk := hc.source_kind hs hpad
  obtain ⟨r, hr⟩ := Generated.MLDSA44.Native.ROMParams.SourceRoleFacts.rolesOk.exec_covered hc hs hpad
  obtain ⟨hm, hv⟩ := sourceRoleTable_mem hr
  have hl := Generated.MLDSA44.Native.ROMParams.SourceRoleFacts.rolesOk.lookup_of_mem hm
  rw [← Generated.MLDSA44.Native.ROMParams.SourceRoles.classifier_eq] at hl
  subst v
  have hm := role_cases hm
  change r.value = 55 ∨
    r.value = 56 ∨
    r.value = 66 ∨
    (r.value = 57 ∧ r.role = .aWitness ∧ r.slot = 0) ∨
    (r.value = 58 ∧ r.role = .aWitness ∧ r.slot = 1) ∨
    (r.value = 59 ∧ r.role = .aWitness ∧ r.slot = 2) ∨
    (r.value = 60 ∧ r.role = .aWitness ∧ r.slot = 3) ∨
    (r.value = 62 ∧ r.role = .aWitness ∧ r.slot = 4) ∨
    (r.value = 63 ∧ r.role = .aWitness ∧ r.slot = 5) ∨
    (r.value = 64 ∧ r.role = .aWitness ∧ r.slot = 6) ∨
    (r.value = 65 ∧ r.role = .aWitness ∧ r.slot = 7) ∨
    (r.value = 67 ∧ r.role = .hashBit ∧ r.slot = 0) ∨
    (r.value = 68 ∧ r.role = .hashBit ∧ r.slot = 1) ∨
    (r.value = 69 ∧ r.role = .hashWord ∧ r.slot = 0) ∨
    (r.value = 119 ∧ r.role = .hashWord ∧ r.slot = 1) ∨
    (r.value = 556 ∧ r.role = .selection ∧ r.slot = 0) ∨
    (r.value = 557 ∧ r.role = .selection ∧ r.slot = 1) ∨
    (r.value = 560 ∧ r.role = .selection ∧ r.slot = 2) ∨
    (r.value = 561 ∧ r.role = .selection ∧ r.slot = 3) ∨
    (r.value = 562 ∧ r.role = .selection ∧ r.slot = 4) ∨
    (r.value = 563 ∧ r.role = .selection ∧ r.slot = 5) ∨
    (r.value = 564 ∧ r.role = .selection ∧ r.slot = 6) ∨
    (r.value = 565 ∧ r.role = .selection ∧ r.slot = 7) ∨
    (if h : 2 ≤ r.slot ∧ r.slot < 242 then
      r.value = wordsVal ⟨(r.slot - 2) / 24, by omega⟩ ⟨(r.slot - 2) % 24, by omega⟩ ∧
      r.role = .hashWord else False) at hm
  rcases r with ⟨rv, rr, rs, rf, rn⟩
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm
  · change rv = 55 at hm
    subst rv
    rw [(MldsaNativeHonest.kinds5657 (program := program)).1] at hk
    simp only [Kind.isBound, Bool.false_eq_true, reduceCtorEq, or_self] at hk
    exact False.elim hk.2.2
  · change rv = 56 at hm
    subst rv
    rw [(MldsaNativeHonest.kinds5657 (program := program)).2] at hk
    simp only [Kind.isBound, Bool.false_eq_true, reduceCtorEq, or_self] at hk
    exact False.elim hk.2.2
  · change rv = 66 at hm
    subst rv
    rw [MldsaHHonest.kind67 (program := program)] at hk
    simp only [Kind.isBound, Bool.false_eq_true, reduceCtorEq, or_self] at hk
    exact False.elim hk.2.2
  · obtain ⟨hrv, hrr, hrs⟩ := hm
    simp only [] at hrv hrr hrs hl
    subst rv
    rw [hrr, hrs] at hl
    simpa only [] using (role_a_z i hl (by simpa only [valueShape_size Generated.MLDSA44.Native.ROMParams.ShapeFacts.value_z_header.2] using hk.2.1))
  · obtain ⟨hrv, hrr, hrs⟩ := hm
    simp only [] at hrv hrr hrs hl
    subst rv
    rw [hrr, hrs] at hl
    simpa only [] using (role_a_hint i hl (by simpa only [valueShape_size Generated.MLDSA44.Native.ROMParams.ShapeFacts.value_h_header.2] using hk.2.1))
  · obtain ⟨hrv, hrr, hrs⟩ := hm
    simp only [] at hrv hrr hrs hl
    subst rv
    rw [hrr, hrs] at hl
    simpa only [] using (role_a_challenge i hl (by simpa only [valueShape_size Generated.MLDSA44.Native.ROMParams.ShapeFacts.value_challenge_2ec_header.2] using hk.2.1))
  · obtain ⟨hrv, hrr, hrs⟩ := hm
    simp only [] at hrv hrr hrs hl
    subst rv
    rw [hrr, hrs] at hl
    simpa only [] using (role_a_w i hl (by simpa only [valueShape_size Generated.MLDSA44.Native.ROMParams.ShapeFacts.value_signature_2ew_header.2] using hk.2.1))
  · obtain ⟨hrv, hrr, hrs⟩ := hm
    simp only [] at hrv hrr hrs hl
    subst rv
    rw [hrr, hrs] at hl
    simpa only [] using (role_a_w1 i hl (by simpa only [valueShape_size Generated.MLDSA44.Native.ROMParams.ShapeFacts.value_hint_2ew1_header.2] using hk.2.1))
  · obtain ⟨hrv, hrr, hrs⟩ := hm
    simp only [] at hrv hrr hrs hl
    subst rv
    rw [hrr, hrs] at hl
    simpa only [] using (role_a_nonpositive i hl (by simpa only [valueShape_size Generated.MLDSA44.Native.ROMParams.ShapeFacts.value_hint_2enonpositive_header.2] using hk.2.1))
  · obtain ⟨hrv, hrr, hrs⟩ := hm
    simp only [] at hrv hrr hrs hl
    subst rv
    rw [hrr, hrs] at hl
    simpa only [] using (role_a_offset i hl (by simpa only [valueShape_size Generated.MLDSA44.Native.ROMParams.ShapeFacts.value_hint_2eoffset_header.2] using hk.2.1))
  · obtain ⟨hrv, hrr, hrs⟩ := hm
    simp only [] at hrv hrr hrs hl
    subst rv
    rw [hrr, hrs] at hl
    simpa only [] using (role_a_slack i hl (by simpa only [valueShape_size Generated.MLDSA44.Native.ROMParams.ShapeFacts.value_hint_2eslack_header.2] using hk.2.1))
  · obtain ⟨hrv, hrr, hrs⟩ := hm
    simp only [] at hrv hrr hrs hl
    subst rv
    rw [hrr, hrs] at hl
    exact role_hash_buffer i hl j
  · obtain ⟨hrv, hrr, hrs⟩ := hm
    simp only [] at hrv hrr hrs hl
    subst rv
    rw [hrr, hrs] at hl
    exact role_hash_flags i hl j
  · obtain ⟨hrv, hrr, hrs⟩ := hm
    simp only [] at hrv hrr hrs hl
    subst rv
    rw [hrr, hrs] at hl
    exact role_hash_w1 i hl j
  · obtain ⟨hrv, hrr, hrs⟩ := hm
    simp only [] at hrv hrr hrs hl
    subst rv
    rw [hrr, hrs] at hl
    exact role_hash_mu i hl j
  · obtain ⟨hrv, hrr, hrs⟩ := hm
    simp only [] at hrv hrr hrs hl
    subst rv
    rw [hrr, hrs] at hl
    exact role_selection_selected i hl j
  · obtain ⟨hrv, hrr, hrs⟩ := hm
    simp only [] at hrv hrr hrs hl
    subst rv
    rw [hrr, hrs] at hl
    exact role_selection_threshold i hl j
  · obtain ⟨hrv, hrr, hrs⟩ := hm
    simp only [] at hrv hrr hrs hl
    subst rv
    rw [hrr, hrs] at hl
    exact role_selection_read_value i hl j
  · obtain ⟨hrv, hrr, hrs⟩ := hm
    simp only [] at hrv hrr hrs hl
    subst rv
    rw [hrr, hrs] at hl
    exact role_selection_read_origin i hl j
  · obtain ⟨hrv, hrr, hrs⟩ := hm
    simp only [] at hrv hrr hrs hl
    subst rv
    rw [hrr, hrs] at hl
    exact role_selection_encoded i hl j
  · obtain ⟨hrv, hrr, hrs⟩ := hm
    simp only [] at hrv hrr hrs hl
    subst rv
    rw [hrr, hrs] at hl
    exact role_selection_final_origin i hl j
  · obtain ⟨hrv, hrr, hrs⟩ := hm
    simp only [] at hrv hrr hrs hl
    subst rv
    rw [hrr, hrs] at hl
    exact role_selection_unit i hl j
  · obtain ⟨hrv, hrr, hrs⟩ := hm
    simp only [] at hrv hrr hrs hl
    subst rv
    rw [hrr, hrs] at hl
    exact role_selection_origin i hl j
  · split_ifs at hm with hslt
    · obtain ⟨hrv, hrr⟩ := hm
      simp only [] at hrv hrr hl hslt
      have hv' : rv = wordsVal ⟨(rs - 2) / 24, slot_perm rs hslt.2⟩
          ⟨(rs - 2) % 24, slot_round rs⟩ := hrv
      clear hrv
      subst rv
      rw [hrr] at hl
      have he : 2 + 24 * ((rs - 2) / 24) + (rs - 2) % 24 = rs := by omega
      have hl' : classifier.lookup (wordsVal ⟨(rs - 2) / 24, by omega⟩
          ⟨(rs - 2) % 24, by omega⟩) = some (.hashWord,
            2 + 24 * ((rs - 2) / 24) + (rs - 2) % 24) := by
        simpa only [he] using hl
      exact role_words i ⟨(rs - 2) / 24, by omega⟩
        ⟨(rs - 2) % 24, by omega⟩ hl' j



end GordieHowe.MLDSA44.Native.ROMParams.SourceRoleSemantics
