-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Ring.SourceValues
public import GordieHowe.Applications.MLDSA44.Ring.Native.RoleCoverage

public section

/-!
# Witness meanings of a native ML-DSA-44 ring program's source roles

The checked source-role table selects each source coordinate's witness meaning. The lemmas here
identify those meanings with the existing honest values `honestVal`, through the embedding of the
native program for the renamed values and directly for the member's values.
-/

namespace GordieHowe.MLDSA44.Ring.Native

open RealizedProgram GordieHowe.Keccak GordieHowe.KeccakTrace

variable {msgLen : ℕ} {program : RealizedProgram} [MldsaRingEmbed program]
  [MldsaRingRelation program] [MldsaRingStmt program] [TableSelect program]
  [MldsaRingFront program] [MldsaRingHonest program]
  {F0 FH : FieldInterp} [QField F0] [HField FH]
  [Native.MldsaAAlgebra (MldsaRingEmbed.nat program)]
  [hN : Native.MldsaNativeHonest (MldsaRingEmbed.nat program) F0 FH]
  [MldsaHHonest (MldsaRingEmbed.nat program)] [MldsaHShuffle (MldsaRingEmbed.nat program)]
  [MldsaHSelHonest (MldsaRingEmbed.nat program)] [MldsaHConsts (MldsaRingEmbed.nat program) FH]
  [MldsaHNativeData FH]

set_option hygiene false in
local notation "interp" => mldsaInterpOf F0 FH
set_option hygiene false in
local notation "nat" => MldsaRingEmbed.nat program
set_option hygiene false in
local notation "σ" => MldsaRingEmbed.σ program

/-- **A cast of a cast between equal first fields is one cast.** -/
theorem castElt_castElt_left {I : Interp} {a b c : ℕ} (h : a = b) (x : (I a).K) :
    (castElt (castElt x : (I b).K) : (I c).K) = castElt x := by
  subst h
  simp

variable (y : RingIn msgLen)

variable (F0 FH) in
/-- **The selected member's algebra inputs**: its key's coordinates, `μ`'s bits and the index bits.
A native ring has no quotient. -/
@[expose] noncomputable def memberInputs : MemberSourceValues (interp 0).K where
  aHat j := ((keyEntry y.key j : ℕ) : (interp 0).K)
  t1 j := ((keyEntry y.key (4096 + j) : ℕ) : (interp 0).K)
  mu j := ((muBitNat y.mu j : ℕ) : (interp 0).K)
  index j := ((y.w.idx / 2 ^ j % 2 : ℕ) : (interp 0).K)
  quotient _ := 0

variable (F0 FH) in
/-- **The algebra witness**: `z`, the hint's offset and slack as numbers, the rest committed. -/
@[expose] noncomputable def algebraInputs : AlgebraSourceValues (interp 0).K where
  z j := if h : j < 1024 then
    ((MLDSA44.NativeAlgebraCircuit.flat (MLDSA44.NativeAlgebraCircuit.Honest.zCentered y.z)
      (Native.fmz j h) : ℤ) : (interp 0).K) else 0
  hint := aValR y (interp 0).K 58
  challenge := aValR y (interp 0).K 59
  w := aValR y (interp 0).K 60
  w1 := aValR y (interp 0).K 62
  nonpositive := aValR y (interp 0).K 63
  offset j := if h : j < 1024 then ((offN y (Native.fm j h) : ℕ) : (interp 0).K) else 0
  slack j := if h : j < 1024 then ((slN y (Native.fm j h) : ℕ) : (interp 0).K) else 0

variable (F0 FH) in
/-- **The hash witness**: `w1`, `μ` and the rounds' words. The core has no buffer or flags. -/
@[expose] noncomputable def hashInputs : HashSourceValues (interp 1).K where
  buffer _ := 0
  flags _ := 0
  w1 := packWord (FH := FH) (w1BitsR y)
  mu := packWord (FH := FH) (muBitsR y)
  rounds p t j := if hp : p < 10 then if ht : t < 24 then
    stateWords HField.packing (iterRounds ((dataR (K := FH.K) y).states ⟨p, hp⟩) (t + 1)) j
    else 0 else 0

variable (program F0 FH) in
/-- **SampleInBall's witness.** -/
@[expose] noncomputable def selectionInputs : SelectionSourceValues (interp 1).K where
  selected := jFR (K := FH.K) y
  threshold := packWord (FH := FH) (lowFR (K := FH.K) y)
  readValue := memFR nat F0 FH y 560
  readOrigin := memFR nat F0 FH y 561
  encoded := memFR nat F0 FH y 562
  finalOrigin := memFR nat F0 FH y 563
  unit := memFR nat F0 FH y 564
  origin := memFR nat F0 FH y 565

variable (program F0 FH) in
/-- **The source valuation** of a ring input through a captured role classifier. -/
@[expose] noncomputable def roleVal (classifier : SourceRoleClassifier) : program.Valuation interp :=
  Ring.sourceVal (program := program) (memberInputs F0 FH y) (algebraInputs F0 FH y)
    (hashInputs F0 FH y) (selectionInputs program F0 FH y) classifier

/-- A renamed committed value executes as its native honest value. -/
theorem exec_held {u : ℕ} (hu : u ∈ ringV) (hk : ((nat).value u).kind = .priv) (j : ℕ) :
    program.execOf interp (honestVal program F0 FH y) ((σ).val u) j =
      castElt (natVal program F0 FH y u j) := by
  have hc := ((MldsaRingEmbed.embedding (program := program)).vals u hu).2.2.2.2.2.2.1
  rw [hk] at hc
  rw [execOf_of_priv _ (Renaming.kindCorr_priv _ hc), honestVal_held y hu j]

variable {classifier : SourceRoleClassifier}

/-- **A committed algebra slot** reads the honest value of domain `A`. -/
theorem role_a_cell {u slot : ℕ} (hu : u ∈ Native.AValues)
    (hr : classifier.lookup ((σ).val u) = some (.aWitness, slot)) (j : ℕ)
    (hm : (algebraInputs F0 FH y).meaning .aWitness slot j = aValR y (interp 0).K u j) :
    roleVal program F0 FH y classifier ((σ).val u) j =
      program.execOf interp (honestVal program F0 FH y) ((σ).val u) j := by
  obtain ⟨hp, hf⟩ := Native.MldsaNativeHonest.a_cells (program := nat) u hu
  have huV := MldsaRingHonest.aV (program := program) u (List.mem_append_left _ hu)
  rw [exec_held y huV (kind_of_privCellB hp), roleVal, Ring.sourceVal_algebra _ _ _ _ hr,
    AlgebraSourceValues.valuation_of_lookup _ hr, hm, natVal, if_pos hu]
  exact (castElt_castElt_left hf.symm _).symm

include hN in
/-- A value of domain `H`'s core lies outside domain `A`. -/
private theorem not_a_of_field {u : ℕ} (hf : (nat).valueField u = 1) : u ∉ Native.AValues := fun h => by
  have := (Native.MldsaNativeHonest.a_cells (program := nat) (F0 := F0) (FH := FH) u h).2
  omega

/-- **A hash word slot** reads the honest word of domain `H`'s core. -/
theorem role_hash {u slot : ℕ} (hu : u ∈ ringV) (hk : ((nat).value u).kind = .priv)
    (hf : (nat).valueField u = 1) (hh : MLDSA44.IsHashValue u)
    (hr : classifier.lookup ((σ).val u) = some (.hashWord, slot)) (j : ℕ)
    (hm : (castElt ((hashInputs F0 FH y).meaning .hashWord slot j) : (interp ((nat).valueField u)).K) =
      hashValCore (program := nat) (F0 := F0) (FH := FH) y u j) :
    roleVal program F0 FH y classifier ((σ).val u) j =
      program.execOf interp (honestVal program F0 FH y) ((σ).val u) j := by
  rw [exec_held y hu hk, roleVal, Ring.sourceVal_hashWord _ _ _ _ hr,
    HashSourceValues.valuation_of_lookup _ hr, natVal, if_neg (not_a_of_field (F0 := F0) (FH := FH) hf), hValCore,
    if_pos hh, ← hm]
  exact (castElt_castElt_left hf.symm _).symm

/-- **A selection slot** reads the honest cell of SampleInBall. -/
theorem role_selection {u slot : ℕ} (hu : u ∈ ringV) (hk : ((nat).value u).kind = .priv)
    (hf : (nat).valueField u = 1) (hs : slot ≠ 8)
    (hr : classifier.lookup ((σ).val u) = some (.selection, slot)) (j : ℕ)
    (hm : (castElt ((selectionInputs program F0 FH y).meaning .selection slot j) :
        (interp ((nat).valueField u)).K) = hValCore nat F0 FH y u j) :
    roleVal program F0 FH y classifier ((σ).val u) j =
      program.execOf interp (honestVal program F0 FH y) ((σ).val u) j := by
  rw [exec_held y hu hk, roleVal, Ring.sourceVal_selection _ _ _ _ hr hs,
    SelectionSourceValues.valuation_of_lookup _ hr, natVal, if_neg (not_a_of_field (F0 := F0) (FH := FH) hf), ← hm]
  exact (castElt_castElt_left hf.symm _).symm

set_option hygiene false in
local notation "E0" => program.srcEnv interp (fun _ _ => 0) (honestVal program F0 FH y)
  (program.chal0 interp) 0

/-- **A bound slot** executes as its native read in the source environment. -/
theorem exec_bound {u : ℕ} {Ex : Expr} (hu : u ∈ ringV) (hk : ((nat).value u).kind = .bound Ex)
    (hf : (nat).valueField u = 0) (j : ℕ) :
    program.execOf interp (honestVal program F0 FH y) ((σ).val u) j =
      castElt (Native.rdA (pull E0) u j) := by
  obtain ⟨-, -, hfu, -, -, -, hc, -⟩ := (MldsaRingEmbed.embedding (program := program)).vals u hu
  rw [hk] at hc
  have hk' := kindCorr_bound hc
  rw [execOf_bound_eq_reader (honestVal program F0 FH y) E0 rfl hk']
  change _ = castElt ((nat).evalE ((nat).reader (pull E0)) 0 (.leaf u) j)
  rw [evalE_leaf, reader_pull _ hu j, castElt_castElt_left hfu]
  exact (castElt_castElt_of_eq (hfu.trans hf) _).symm

/-! ## The role rows -/

/-- **The word slot of round `t` of permutation `p`.** -/
theorem exists_words_of_wordsB {slot u : ℕ} (h : wordsB slot u = true) :
    ∃ (p : Fin 10) (t : Fin 24), u = wordsVal p t ∧ slot = 2 + 24 * (p : ℕ) + (t : ℕ) := by
  simp only [wordsB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨hl, hh⟩, rfl⟩ := h
  refine ⟨_, _, rfl, ?_⟩
  simp only [Fin.val_ofNat]
  omega

/-- **The member's role of a value**: the selected key's two blocks, `μ` and the index. -/
@[expose] def memberRoleB (a t mu i : ℕ) (r : SourceRoleEntry) : Bool :=
  match r.role with
  | .ringSigma =>
    (r.value == a && r.slot == 0) || (r.value == t && r.slot == 1) || (r.value == mu && r.slot == 2)
  | .selection => r.value == i && r.slot == 8
  | _ => false

/-- **The role of a native value at a renamed value**: an algebra, hash or selection slot. -/
@[expose] def heldRoleB (role : SourceRole) (slot u : ℕ) : Bool :=
  match role with
  | .aWitness =>
    (u == 57 && slot == 0) || (u == 58 && slot == 1) || (u == 59 && slot == 2) ||
    (u == 60 && slot == 3) || (u == 62 && slot == 4) || (u == 63 && slot == 5) ||
    (u == 64 && slot == 6) || (u == 65 && slot == 7)
  | .hashWord => (u == 69 && slot == 0) || (u == 119 && slot == 1) || wordsB slot u
  | .selection =>
    (u == 556 && slot == 0) || (u == 557 && slot == 1) || (u == 560 && slot == 2) ||
    (u == 561 && slot == 3) || (u == 562 && slot == 4) || (u == 563 && slot == 5) ||
    (u == 564 && slot == 6) || (u == 565 && slot == 7)
  | _ => false

/-- **One source-role row's meaning**: a value that is not executed (`skip`), a member's value or a
renamed native value. -/
@[expose] def roleRowB (skip : List ℕ) (a t mu i : ℕ) (val inv : ℕ → ℕ) (r : SourceRoleEntry) : Bool :=
  skip.contains r.value || memberRoleB a t mu i r ||
  (ringVB (inv r.value) && val (inv r.value) == r.value && heldRoleB r.role r.slot (inv r.value))

/-- **A member's slot** reads the honest member value. -/
theorem role_member {classifier : SourceRoleClassifier} {r : SourceRoleEntry}
    (hl : classifier.lookup r.value = some (r.role, r.slot))
    (h : memberRoleB (MldsaRingRelation.aHat program) (MldsaRingRelation.t1 program)
      (MldsaRingFront.muA program) (TableSelect.shape program).idx r = true) (j : ℕ) :
    roleVal program F0 FH y classifier r.value j =
      program.execOf interp (honestVal program F0 FH y) r.value j := by
  have hnd := MldsaRingHonest.member_nodup (program := program)
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  obtain ⟨⟨ha1, ha2, ha3⟩, ⟨ht1, ht2⟩, hm1, -⟩ := hnd
  have hkind : ∀ v ∈ [MldsaRingRelation.aHat program, MldsaRingRelation.t1 program,
      MldsaRingFront.muA program, (TableSelect.shape program).idx],
      (program.value v).kind = .priv := fun v hv =>
    kind_of_privCellB (MldsaRingHonest.memberCells v hv).1
  rcases r with ⟨v, role, slot, field, node⟩
  simp only at hl h ⊢
  cases role <;> simp only [memberRoleB, Bool.false_eq_true, Bool.or_eq_true, Bool.and_eq_true,
    beq_iff_eq] at h
  case ringSigma =>
    rcases h with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩
    · rw [roleVal, Ring.sourceVal_aHat _ _ _ _ hl, execOf_of_priv _ (hkind _ (by simp)), honestVal,
        if_pos rfl]
      rfl
    · rw [roleVal, Ring.sourceVal_t1 _ _ _ _ hl, execOf_of_priv _ (hkind _ (by simp)), honestVal,
        if_neg (Ne.symm ha1), if_pos rfl]
      rfl
    · rw [roleVal, Ring.sourceVal_mu _ _ _ _ hl, execOf_of_priv _ (hkind _ (by simp)), honestVal,
        if_neg (Ne.symm ha2), if_neg (Ne.symm ht1), if_pos rfl]
      rfl
  case selection =>
    obtain ⟨rfl, rfl⟩ := h
    rw [roleVal, Ring.sourceVal_index _ _ _ _ hl, execOf_of_priv _ (hkind _ (by simp)), honestVal,
      if_neg (Ne.symm ha3), if_neg (Ne.symm ht2), if_neg (Ne.symm hm1), if_pos rfl]
    rfl

/-- **A renamed native value's slot** reads the honest value, on the value's coordinates. -/
theorem role_held {classifier : SourceRoleClassifier} {u slot : ℕ} {role : SourceRole}
    (hu : u ∈ ringV) (hl : classifier.lookup ((σ).val u) = some (role, slot))
    (h : heldRoleB role slot u = true) {j : ℕ} (hj : j < (program.value ((σ).val u)).size) :
    roleVal program F0 FH y classifier ((σ).val u) j =
      program.execOf interp (honestVal program F0 FH y) ((σ).val u) j := by
  have hsz := ((MldsaRingEmbed.embedding (program := program)).vals u hu).2.2.2.1
  rw [hsz] at hj
  obtain ⟨-, hoff, hsl⟩ := Native.MldsaNativeHonest.a_kinds (program := nat) (F0 := F0) (FH := FH)
  obtain ⟨f57, f64, f65, -⟩ := Native.MldsaNativeHonest.a_bound (program := nat) (F0 := F0) (FH := FH)
  have hz := (Native.MldsaNativeHonest.a_kinds (program := nat) (F0 := F0) (FH := FH)).1
  have hlen := Native.lensA (program := nat)
  have hr := readsA_pull (program := program) (F0 := F0) (FH := FH) y (fun _ _ => 0)
    (program.chal0 interp) 0
  cases role <;> simp only [heldRoleB, Bool.false_eq_true, Bool.or_eq_true, Bool.and_eq_true,
    beq_iff_eq] at h
  case aWitness =>
    rcases h with ((((((⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) |
      ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩
    · have hm : j < 1024 := hlen.1 ▸ hj
      rw [exec_bound y hu hz f57, roleVal, Ring.sourceVal_algebra _ _ _ _ hl,
        AlgebraSourceValues.valuation_of_lookup _ hl, AlgebraSourceValues.meaning_z,
        rdA_58 hr hm]
      simp only [algebraInputs, dite_eq_left hm]
    · exact role_a_cell y (by decide) hl j rfl
    · exact role_a_cell y (by decide) hl j rfl
    · exact role_a_cell y (by decide) hl j rfl
    · exact role_a_cell y (by decide) hl j rfl
    · exact role_a_cell y (by decide) hl j rfl
    · have hm : j < 1024 := hlen.2.2.2.2.2.2.1 ▸ hj
      rw [exec_bound y hu hoff f64, roleVal, Ring.sourceVal_algebra _ _ _ _ hl,
        AlgebraSourceValues.valuation_of_lookup _ hl, AlgebraSourceValues.meaning_offset,
        rdA_65 hr hm]
      simp only [algebraInputs, dite_eq_left hm]
    · have hm : j < 1024 := hlen.2.2.2.2.2.2.2.1 ▸ hj
      rw [exec_bound y hu hsl f65, roleVal, Ring.sourceVal_algebra _ _ _ _ hl,
        AlgebraSourceValues.valuation_of_lookup _ hl, AlgebraSourceValues.meaning_slack,
        rdA_66 hr hm]
      simp only [algebraInputs, dite_eq_left hm]
  case hashWord =>
    obtain ⟨hw, hn67, hn68, hn69, hn119⟩ := MLDSA44.wordsOwner_checks
    rcases h with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | h
    · have hv := MldsaHHonest.view71 (program := nat)
      refine role_hash y hu (kind_of_privCellB hv.2.1) hv.2.2.2.1 (by unfold MLDSA44.IsHashValue; simp) hl j ?_
      unfold hashValCore
      rw [if_pos rfl]
      rfl
    · have hv := MldsaHHonest.view121 (program := nat)
      refine role_hash y hu (kind_of_privCellB hv.2.1) hv.2.2.2.1 (by unfold MLDSA44.IsHashValue; simp) hl j ?_
      unfold hashValCore
      rw [if_neg (by decide), if_pos rfl]
      rfl
    · obtain ⟨p, t, rfl, rfl⟩ := exists_words_of_wordsB h
      have hc := MldsaHHonest.words_checks (program := nat) p t
      have hne69 : wordsVal p t ≠ 69 := fun he => by
        have := hw p t
        rw [he, hn69] at this
        cases this
      have hne119 : wordsVal p t ≠ 119 := fun he => by
        have := hw p t
        rw [he, hn119] at this
        cases this
      refine role_hash y hu (kind_of_privCellB hc.2.1) hc.2.2.2.1
        (by unfold MLDSA44.IsHashValue; simp [hw p t]) hl j ?_
      unfold hashValCore
      rw [if_neg hne69, if_neg hne119, hw p t, HashSourceValues.meaning_round _ _ _ _ t.isLt]
      simp only [hashInputs, dite_eq_left p.isLt, dite_eq_left t.isLt]
  case selection =>
    obtain ⟨n556, n557, nmem⟩ := MLDSA44.h_classes
    have hsel := MldsaHSelHonest.sel_cells (program := nat)
    have hmem := (MldsaHSelHonest.mem_cells (program := nat)).1
    rcases h with ((((((⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) |
      ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩
    · refine role_selection y hu (kind_of_privCellB hsel.2.2.2.2.2.2.2.2.2.1) hsel.2.2.2.2.2.2.2.2.2.2.1 (by decide) hl j ?_
      unfold hValCore
      rw [if_neg n556, if_pos rfl]
      rfl
    · refine role_selection y hu (kind_of_privCellB hsel.2.1) hsel.2.2.2.1 (by decide) hl j ?_
      unfold hValCore
      rw [if_neg n557, if_neg (by decide), if_pos rfl]
      rfl
    all_goals
      refine role_selection y hu (kind_of_privCellB (hmem _ (by simp)).1) (hmem _ (by simp)).2 (by decide) hl j ?_
      unfold hValCore
      rw [if_neg (nmem _ (by simp)), if_neg (by decide), if_neg (by decide), if_pos (by simp)]
      rfl

/-- **Every executed source coordinate agrees with the honest values**, from the checked role rows
of the program's classifier: `skip` lists the source values that are not executed, and `val`, `inv`
are the renaming and its inverse. -/
theorem role_source_coordinates {rs : List SourceRoleEntry} (hrs : SourceRolesOk program rs)
    {skip : List ℕ} {val inv : ℕ → ℕ}
    (hrows : rs.all (roleRowB skip (MldsaRingRelation.aHat program) (MldsaRingRelation.t1 program)
      (MldsaRingFront.muA program) (TableSelect.shape program).idx val inv) = true)
    (hσ : (σ).val = val)
    (hskip : ∀ v ∈ skip, (program.value v).kind ≠ .priv ∧ (program.value v).kind.isBound = false)
    {v j : ℕ} (hs : program.IsSourceValue v) (hc : program.ExecCoord v j)
    (hpad : ∀ u < program.values.length, program.IsSourceValue u →
      (program.value u).kind.isPadCopy = false) :
    roleVal program F0 FH y (sourceRoleClassifier rs) v j =
      program.execOf interp (honestVal program F0 FH y) v j := by
  obtain ⟨-, hj, hk⟩ := hc.source_kind hs hpad
  obtain ⟨r, hr⟩ := hrs.exec_covered hc hs hpad
  obtain ⟨hm, rfl⟩ := sourceRoleTable_mem hr
  have hl : (sourceRoleClassifier rs).lookup r.value = some (r.role, r.slot) :=
    hrs.lookup_of_mem hm
  have hrow := List.all_eq_true.mp hrows r hm
  simp only [roleRowB, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hrow
  rcases hrow with (hx | hx) | ⟨⟨hu, huv⟩, hh⟩
  · obtain ⟨h1, h2⟩ := hskip _ (List.contains_iff_mem.mp hx)
    rcases hk with hk | hk
    · exact absurd hk h1
    · rw [h2] at hk
      cases hk
  · exact role_member y hl hx j
  · have hval : (σ).val (inv r.value) = r.value := by rw [hσ, huv]
    have hl' := hl
    rw [← hval] at hl' hj ⊢
    exact role_held y (mem_ringV_of_ringVB hu) hl' hh hj

end GordieHowe.MLDSA44.Ring.Native
