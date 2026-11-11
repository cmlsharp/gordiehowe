-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Ring.SourceValues
public import GordieHoweCerts.Applications.MLDSA44.Ring.Native.RoleSemantics
public import GordieHoweCerts.Applications.MLDSA44.Ring.Carrier.HonestFull
public import GordieHoweCerts.Applications.MLDSA44.Ring.Carrier.HonestRelation

public section

/-!
# Source roles of an ML-DSA-44 ring carrier

The classes of the committed source values (`MldsaCarrierExec.cell_classes`) and the witness
meaning of each source role, checked on the finite source-role rows. A row's renamed value is found
by the renamings' inverse tables (`hOf`, `aOf`), read through `MldsaCarrierHonest.hOf_val` and
`MldsaCarrierHonest.aOf_val`.
-/

namespace GordieHowe.MLDSA44.Ring.Carrier

set_option hygiene false in
local notation "σH" => CarrierHEmbed.σ program

set_option hygiene false in
local notation "hV" => CarrierHEmbed.V program

set_option hygiene false in
local notation "σA" => CarrierAEmbed.σ program

set_option hygiene false in
local notation "aV" => CarrierAEmbed.V program

set_option hygiene false in
local notation "predMapA" => CarrierAEmbed.pred program

open RealizedProgram GordieHowe.Keccak GordieHowe.KeccakTrace
open GordieHowe.MLDSA44.Ring.Native (natGF16B wordsB coreHashB_of_wordsB exists_words_of_wordsB
  memberRoleB castElt_castElt_left MldsaRingStmt muBitNat offN slN jFR lowFR memFR hValCore
  hashValCore)
open MLDSA44.Emulated (aValues MldsaEAlgebra MldsaEmulatedHonest)

/-- **The inverse of the renaming of domain `H`** on its held values, from the table (`hOf`); `v`
itself where none is. -/
@[expose] def invHOf (program : RealizedProgram) [CarrierHEmbed program] (v : ℕ) : ℕ :=
  (hOf program v).getD v

/-- **The inverse of the renaming of domain `A`** on its held values, from the table (`aOf`). -/
@[expose] def invAOf (program : RealizedProgram) [CarrierAEmbed program] (v : ℕ) : ℕ :=
  (aOf program v).getD v

/-- **Whether a native value is held**, by the table: the table gives it back at its image. -/
@[expose] def heldHB (program : RealizedProgram) [CarrierHEmbed program] (u : ℕ) : Bool :=
  hOf program ((σH).val u) == some u

/-- **Whether an emulated value is held**, by the table. -/
@[expose] def heldAB (program : RealizedProgram) [CarrierAEmbed program] (u : ℕ) : Bool :=
  aOf program ((σA).val u) == some u

theorem mem_of_heldHB {program : RealizedProgram} [CarrierHEmbed program] {u : ℕ}
    (h : heldHB program u = true) : u ∈ hV :=
  (hOf_spec (beq_iff_eq.mp h)).1

theorem mem_of_heldAB {program : RealizedProgram} [CarrierAEmbed program] {u : ℕ}
    (h : heldAB program u = true) : u ∈ aV :=
  (aOf_spec (beq_iff_eq.mp h)).1

/-- **One source-role row's class** at the renamings `valH`, `valA` with inverses `invH`, `invA` on
the values `heldH`, `heldA` accept: a value in `skip`, a member value or the high halves of field
`0`, or a renamed native or emulated value of the honest values' classes. -/
@[expose] def rowB (valH valA invH invA : ℕ → ℕ) (heldH heldA : ℕ → Bool) (skip : List ℕ)
    (r : SourceRoleEntry) : Bool :=
  skip.contains r.value ||
  ([56, 57, 58, 59, 66].contains r.value && r.field == 0 &&
    r.node.map (·.name) == some "GF(p^1)") ||
  (heldH (invH r.value) && valH (invH r.value) == r.value &&
    (((invH r.value == 69 || invH r.value == 119 || wordsB r.slot (invH r.value) ||
        [557, 560, 562, 563, 564, 565].contains (invH r.value)) && r.field == 1 &&
        r.node.map (·.name) == some "GF(2^16)") ||
      ([556, 561].contains (invH r.value) && r.field == 1 &&
        r.node.map (·.name) == some "bit"))) ||
  (heldA (invA r.value) && valA (invA r.value) == r.value &&
    [59, 60, 63, 64].contains (invA r.value) && r.field == 0 &&
    r.node.map (·.name) == some "GF(p^1)")

/-- **The role of a held value**: an algebra slot of an emulated value, or a hash or selection slot
of a native value. -/
@[expose] def heldHRoleB (role : SourceRole) (slot u : ℕ) : Bool :=
  match role with
  | .hashWord => (u == 69 && slot == 0) || (u == 119 && slot == 1) || wordsB slot u
  | .selection =>
    (u == 556 && slot == 0) || (u == 557 && slot == 1) || (u == 560 && slot == 2) ||
    (u == 561 && slot == 3) || (u == 562 && slot == 4) || (u == 563 && slot == 5) ||
    (u == 564 && slot == 6) || (u == 565 && slot == 7)
  | _ => false

/-- The algebra slots of the emulated values. -/
@[expose] def heldARoleB (role : SourceRole) (slot u : ℕ) : Bool :=
  match role with
  | .aWitness =>
    (u == 58 && slot == 0) || (u == 59 && slot == 1) || (u == 60 && slot == 2) ||
    (u == 61 && slot == 3) || (u == 63 && slot == 4) || (u == 64 && slot == 5) ||
    (u == 65 && slot == 6) || (u == 66 && slot == 7)
  | _ => false

/-- **One source-role row's meaning** at the renamings and inverses of `rowB`: a value that is not
executed (`skip`), a member's value, the quotient, the high halves, or a renamed native or emulated
value. -/
@[expose] def roleRowB (valH valA invH invA : ℕ → ℕ) (heldH heldA : ℕ → Bool) (skip : List ℕ)
    (r : SourceRoleEntry) : Bool :=
  skip.contains r.value || memberRoleB 56 57 58 59 r ||
  (r.value == 65 && (match r.role with | .carry => r.slot == 0 | _ => false)) ||
  (r.value == 66 && (match r.role with | .aWitness => r.slot == 8 | _ => false)) ||
  (heldH (invH r.value) && valH (invH r.value) == r.value &&
    heldHRoleB r.role r.slot (invH r.value)) ||
  (heldA (invA r.value) && valA (invA r.value) == r.value &&
    heldARoleB r.role r.slot (invA r.value))

variable {msgLen : ℕ} {program : RealizedProgram} [CarrierHEmbed program] [CarrierAEmbed program]
  [MldsaEAlgebra (CarrierAEmbed.emu program)] [MldsaCarrierHonest program]
  {F0 FH : FieldInterp} [HField FH]

set_option hygiene false in
local notation "interp" => mldsaInterpOf F0 FH
set_option hygiene false in
local notation "nat" => CarrierHEmbed.nat program
set_option hygiene false in
local notation "emu" => CarrierAEmbed.emu program
set_option hygiene false in
local notation "L" => MldsaEAlgebra.layout (CarrierAEmbed.emu program)

/-- **The committed source values' classes from the checked role rows.** `skip` lists source values
that are not committed; the rows' classes then give `MldsaCarrierExec.cell_classes`. -/
theorem cell_classes_of_rows {rs : List SourceRoleEntry} (hrs : SourceRolesOk program rs)
    {valH valA invH invA : ℕ → ℕ} {heldH heldA : ℕ → Bool} {skip : List ℕ}
    (hrows : rs.all (rowB valH valA invH invA heldH heldA skip) = true)
    (hσH : (σH).val = valH) (hσA : (σA).val = valA) (hheldH : ∀ u, heldH u = true → u ∈ hV)
    (hheldA : ∀ u, heldA u = true → u ∈ aV)
    (hskip : ∀ v ∈ skip, (program.value v).kind ≠ .priv) :
    (List.range program.values.length).all (fun v =>
      !program.privCellB v || !decide (program.IsSourceValue v) ||
        (([56, 57, 58, 59, 66] ++ (MldsaCarrierHonest.qD program).ids).contains v &&
          program.valueField v == 0 && (program.value v).node.map (·.name) == some "GF(p^1)") ||
        (match hOf program v with
          | some u => (natGF16B u && program.valueField v == 1 &&
              (program.value v).node.map (·.name) == some "GF(2^16)") ||
            ([556, 561].contains u && program.valueField v == 1 &&
              (program.value v).node.map (·.name) == some "bit")
          | none => match aOf program v with
            | some u => (aValues (MldsaEAlgebra.layout (CarrierAEmbed.emu program))).contains u &&
              program.valueField v == 0 && (program.value v).node.map (·.name) == some "GF(p^1)"
            | none => false)) = true := by
  apply List.all_eq_true.mpr
  intro v hv
  by_cases hp : program.privCellB v = true
  swap
  · simp only [Bool.eq_false_iff.mpr hp, Bool.not_false, Bool.true_or]
  by_cases hs : program.IsSourceValue v
  swap
  · simp only [hs, decide_false, Bool.not_false, Bool.or_true, Bool.true_or]
  have hk := kind_of_privCellB hp
  have hn : (program.value v).needsSourceRole = true := by
    simp only [Value.needsSourceRole, show (program.value v).role = .source from hs,
      decide_true, hk, Bool.true_and]
  obtain ⟨r, hr⟩ := hrs.covered v (List.mem_range.mp hv) hn
  obtain ⟨hm, rfl⟩ := sourceRoleTable_mem hr
  obtain ⟨-, -, hf, hnode⟩ := hrs.entries r hm
  have hrow := List.all_eq_true.mp hrows r hm
  simp only [rowB, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hrow
  simp only [hp, decide_true, hs, Bool.not_true, Bool.false_or]
  rw [hf, hnode]
  rcases hrow with ((hx | ⟨⟨hx, hf0⟩, hn0⟩) | ⟨⟨hu, huv⟩, hc⟩) | ⟨⟨⟨⟨hu, huv⟩, hc⟩, hf0⟩, hn0⟩
  · exact absurd hk (hskip _ (List.contains_iff_mem.mp hx))
  · simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem]
    exact Or.inl ⟨⟨List.mem_append_left _ (List.contains_iff_mem.mp hx), hf0⟩, hn0⟩
  · have hh : hOf program r.value = some (invH r.value) := by
      have h := MldsaCarrierHonest.hOf_val _ (hheldH _ hu)
      rwa [show (σH).val (invH r.value) = r.value by rw [hσH]; exact huv] at h
    rw [hh]
    simp only [natGF16B, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
    refine Or.inr ?_
    rcases hc with ⟨⟨hg, hf1⟩, hn1⟩ | hb
    · refine Or.inl ⟨⟨?_, hf1⟩, hn1⟩
      rcases hg with ((h | h) | h) | h
      · exact Or.inl (by simp [Native.coreHashB, h])
      · exact Or.inl (by simp [Native.coreHashB, h])
      · exact Or.inl (coreHashB_of_wordsB h)
      · exact Or.inr h
    · exact Or.inr hb
  · have hnH : hOf program r.value = none := by
      have h := MldsaCarrierHonest.hOf_valA _ (hheldA _ hu)
      rwa [show (σA).val (invA r.value) = r.value by rw [hσA]; exact huv] at h
    have hA : aOf program r.value = some (invA r.value) := by
      have h := MldsaCarrierHonest.aOf_val _ (hheldA _ hu)
      rwa [show (σA).val (invA r.value) = r.value by rw [hσA]; exact huv] at h
    rw [hnH, hA]
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem]
    exact Or.inr ⟨⟨MLDSA44.Emulated.fixed_mem_aValues (List.contains_iff_mem.mp hc), hf0⟩, hn0⟩

/-! ## The role rows' witness meanings -/

section Meanings

variable (y : RingIn msgLen)

variable (F0 FH) in
/-- **The selected member's inputs**: the spectra of its key, `μ`'s bits, the index bits, the
signature relation's quotient and the rows' high halves (`qHonC`). -/
@[expose] noncomputable def memberInputs : MemberSourceValues (interp 0).K where
  aHat j := if j < 4096 then specE y (interp 0).K j else 0
  t1 j := if j < 1024 then specE y (interp 0).K (4096 + j) else 0
  mu j := ((muBitNat y.mu j : ℕ) : (interp 0).K)
  index j := ((y.w.idx / 2 ^ j % 2 : ℕ) : (interp 0).K)
  quotient j := ((quotN y j : ℕ) : (interp 0).K)
  high j := if h : j < 1020 then qHonC y (interp 0).K ⟨j / 255, by omega⟩ (j % 255) else 0

variable (program F0 FH) in
/-- **The algebra witness**: `z`, `w′`, the hint's offset and slack as numbers, the rest committed. -/
@[expose] noncomputable def algebraInputs : AlgebraSourceValues (interp 0).K where
  z j := if h : j < 1024 then
    ((MLDSA44.NativeAlgebraCircuit.flat (MLDSA44.NativeAlgebraCircuit.Honest.zCentered y.z)
      (MLDSA44.Emulated.fmz j h) : ℤ) : (interp 0).K) else 0
  hint := aValE y (interp 0).K L 59
  challenge := aValE y (interp 0).K L 60
  w j := if h : j < 1024 then ((wNR y (MLDSA44.Emulated.fm j h) : ℕ) : (interp 0).K) else 0
  w1 := aValE y (interp 0).K L 63
  nonpositive := aValE y (interp 0).K L 64
  offset j := if h : j < 1024 then ((offN y (MLDSA44.Emulated.fm j h) : ℕ) : (interp 0).K) else 0
  slack j := if h : j < 1024 then ((slN y (MLDSA44.Emulated.fm j h) : ℕ) : (interp 0).K) else 0

variable [MldsaHHonest nat] [MldsaHShuffle nat] [MldsaHSelHonest nat] [MldsaHConsts nat FH]

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
  Ring.sourceVal (program := program) (memberInputs F0 FH y) (algebraInputs program F0 FH y)
    (Native.hashInputs F0 FH y) (selectionInputs program F0 FH y) classifier

/-- A renamed native committed value executes as its core honest value. -/
theorem exec_heldH {u : ℕ} (hu : u ∈ hV) (hk : ((nat).value u).kind = .priv) (j : ℕ) :
    program.execOf interp (honestVal program F0 FH y) ((σH).val u) j =
      castElt (hValCore nat F0 FH y u j) := by
  have hc := ((CarrierHEmbed.embedding (program := program)).vals u hu).2.2.2.2.2.2.1
  rw [hk] at hc
  rw [execOf_of_priv _ (Renaming.kindCorr_priv _ hc), honestVal_heldH y hu j]

/-- **A hash word slot** reads the honest word of domain `H`'s core. -/
theorem role_hash {classifier : SourceRoleClassifier} {u slot : ℕ} (hu : u ∈ hV)
    (hk : ((nat).value u).kind = .priv) (hf : (nat).valueField u = 1) (hh : MLDSA44.IsHashValue u)
    (hr : classifier.lookup ((σH).val u) = some (.hashWord, slot)) (j : ℕ)
    (hm : (castElt ((Native.hashInputs F0 FH y).meaning .hashWord slot j) :
        (interp ((nat).valueField u)).K) =
      hashValCore (program := nat) (F0 := F0) (FH := FH) y u j) :
    roleVal program F0 FH y classifier ((σH).val u) j =
      program.execOf interp (honestVal program F0 FH y) ((σH).val u) j := by
  rw [exec_heldH y hu hk, roleVal, Ring.sourceVal_hashWord _ _ _ _ hr,
    HashSourceValues.valuation_of_lookup _ hr, hValCore, if_pos hh, ← hm]
  exact (castElt_castElt_left hf.symm _).symm

/-- **A selection slot** reads the honest cell of SampleInBall. -/
theorem role_selection {classifier : SourceRoleClassifier} {u slot : ℕ} (hu : u ∈ hV)
    (hk : ((nat).value u).kind = .priv) (hf : (nat).valueField u = 1) (hs : slot ≠ 8)
    (hr : classifier.lookup ((σH).val u) = some (.selection, slot)) (j : ℕ)
    (hm : (castElt ((selectionInputs program F0 FH y).meaning .selection slot j) :
        (interp ((nat).valueField u)).K) = hValCore nat F0 FH y u j) :
    roleVal program F0 FH y classifier ((σH).val u) j =
      program.execOf interp (honestVal program F0 FH y) ((σH).val u) j := by
  rw [exec_heldH y hu hk, roleVal, Ring.sourceVal_selection _ _ _ _ hr hs,
    SelectionSourceValues.valuation_of_lookup _ hr, ← hm]
  exact (castElt_castElt_left hf.symm _).symm

/-- **A renamed native value's slot** reads the honest value. -/
theorem role_heldH {classifier : SourceRoleClassifier} {u slot : ℕ} {role : SourceRole}
    (hu : u ∈ hV) (hl : classifier.lookup ((σH).val u) = some (role, slot))
    (h : heldHRoleB role slot u = true) (j : ℕ) :
    roleVal program F0 FH y classifier ((σH).val u) j =
      program.execOf interp (honestVal program F0 FH y) ((σH).val u) j := by
  cases role <;> simp only [heldHRoleB, Bool.false_eq_true, Bool.or_eq_true, Bool.and_eq_true,
    beq_iff_eq] at h
  case hashWord =>
    obtain ⟨hw, -, -, hn69, hn119⟩ := MLDSA44.wordsOwner_checks
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
      simp only [Native.hashInputs, dite_eq_left p.isLt, dite_eq_left t.isLt]
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

variable [MldsaCarrierRelation program] [MldsaRingStmt program] [TableSelect program]
  [MldsaCarrierFront program] [MldsaCarrierSelect program] [MldsaCarrierQuot program]
  [RealizedProgram.PrimeCastField F0 pGold] [MLDSA44.MldsaHNativeData FH]
  [MLDSA44.MldsaHSample (MLDSA44.Emulated.MldsaEmbed.nat emu)]
  [MLDSA44.MldsaHConsts (MLDSA44.Emulated.MldsaEmbed.nat emu) FH]
  [MldsaHHonest (MLDSA44.Emulated.MldsaEmbed.nat emu)]
  [MldsaHSelHonest (MLDSA44.Emulated.MldsaEmbed.nat emu)] [MLDSA44.MldsaHNodes FH]
  [hE : MldsaEmulatedHonest emu F0 FH]

set_option hygiene false in
local notation "E0" => program.srcEnv interp (fun _ _ => 0) (honestVal program F0 FH y)
  (program.chal0 interp) 0

include hE in
/-- **A committed algebra slot** reads the honest value of domain `A`. -/
theorem role_a_cell {classifier : SourceRoleClassifier} {u slot : ℕ} (hu : u ∈ aValues L)
    (hr : classifier.lookup ((σA).val u) = some (.aWitness, slot)) (j : ℕ) (hs : slot ≠ 8)
    (hm : (algebraInputs program F0 FH y).meaning .aWitness slot j = aValE y (interp 0).K L u j) :
    roleVal program F0 FH y classifier ((σA).val u) j =
      program.execOf interp (honestVal program F0 FH y) ((σA).val u) j := by
  obtain ⟨hp, -⟩ := MldsaEmulatedHonest.a_cells (program := emu) (F0 := F0) (FH := FH) u hu
  have huV := MldsaCarrierHonest.aVals (program := program) u (List.mem_append_left _ hu)
  have hc := ((CarrierAEmbed.embedding (program := program)).vals u huV).2.2.2.2.2.2.1
  rw [kind_of_privCellB hp] at hc
  rw [execOf_of_priv _ (Renaming.kindCorr_priv _ hc), honestVal_heldA y hu j, roleVal,
    Ring.sourceVal_algebra _ _ _ _ hr hs, AlgebraSourceValues.valuation_of_lookup _ hr, hm]

/-- **A bound slot** executes as its emulated read in the source environment. -/
theorem exec_boundA {u : ℕ} {Ex : Expr} (hu : u ∈ aV) (hk : ((emu).value u).kind = .bound Ex)
    (hf : (emu).valueField u = 0) (j : ℕ) :
    program.execOf interp (honestVal program F0 FH y) ((σA).val u) j =
      castElt (MLDSA44.Emulated.rdA (pullA E0) u j) := by
  obtain ⟨-, -, hfu, -, -, -, hc, -⟩ := (CarrierAEmbed.embedding (program := program)).vals u hu
  rw [hk] at hc
  have hk' := Native.kindCorr_bound hc
  rw [execOf_bound_eq_reader (honestVal program F0 FH y) E0 rfl hk']
  change _ = castElt ((emu).evalE ((emu).reader (pullA E0)) 0 (.leaf u) j)
  rw [evalE_leaf, readerA_pull _ hu j, castElt_castElt_left hfu]
  exact (castElt_castElt_of_eq (hfu.trans hf) _).symm

/-- **A renamed emulated value's slot** reads the honest value, on the value's coordinates. -/
theorem role_heldA {classifier : SourceRoleClassifier} {u slot : ℕ} {role : SourceRole}
    (hu : u ∈ aV) (hl : classifier.lookup ((σA).val u) = some (role, slot))
    (h : heldARoleB role slot u = true) {j : ℕ} (hj : j < (program.value ((σA).val u)).size) :
    roleVal program F0 FH y classifier ((σA).val u) j =
      program.execOf interp (honestVal program F0 FH y) ((σA).val u) j := by
  have hsz := ((CarrierAEmbed.embedding (program := program)).vals u hu).2.2.2.1
  rw [hsz] at hj
  have hbv := MldsaEmulatedHonest.boundVals (program := emu) (F0 := F0) (FH := FH)
  have hlen := MLDSA44.Emulated.lensA (program := emu)
  have hr := readsAE_pullA (program := program) (F0 := F0) (FH := FH) y (fun _ _ => 0)
    (program.chal0 interp) 0
  have hfix : ∀ v ∈ [59, 60, 63, 64], v ∈ aValues L := fun v hv =>
    MLDSA44.Emulated.fixed_mem_aValues hv
  cases role <;> simp only [heldARoleB, Bool.false_eq_true, Bool.or_eq_true, Bool.and_eq_true,
    beq_iff_eq] at h
  case aWitness =>
    rcases h with ((((((⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) |
      ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩
    · have hm : j < 1024 := hlen.1 ▸ hj
      rw [exec_boundA y hu (MldsaEmulatedHonest.kind59 (program := emu) (F0 := F0) (FH := FH))
          (hbv 58 (by simp)).2, roleVal, Ring.sourceVal_algebra _ _ _ _ hl (by decide),
        AlgebraSourceValues.valuation_of_lookup _ hl, AlgebraSourceValues.meaning_z,
        rdAE_58 hr hm]
      simp only [algebraInputs, dite_eq_left hm]
    · exact role_a_cell y (hfix 59 (by simp)) hl j (by decide) rfl
    · exact role_a_cell y (hfix 60 (by simp)) hl j (by decide) rfl
    · have hm : j < 1024 := hlen.2.2.2.1 ▸ hj
      rw [exec_boundA y hu (MldsaEmulatedHonest.kind62 (program := emu) (F0 := F0) (FH := FH))
          (hbv 61 (by simp)).2, roleVal, Ring.sourceVal_algebra _ _ _ _ hl (by decide),
        AlgebraSourceValues.valuation_of_lookup _ hl, AlgebraSourceValues.meaning_w,
        rdAE_61 hr hm]
      simp only [algebraInputs, dite_eq_left hm]
    · exact role_a_cell y (hfix 63 (by simp)) hl j (by decide) rfl
    · exact role_a_cell y (hfix 64 (by simp)) hl j (by decide) rfl
    · have hm : j < 1024 := hlen.2.2.2.2.2.2.1 ▸ hj
      rw [exec_boundA y hu (MldsaEmulatedHonest.kind66 (program := emu) (F0 := F0) (FH := FH))
          (hbv 65 (by simp)).2, roleVal, Ring.sourceVal_algebra _ _ _ _ hl (by decide),
        AlgebraSourceValues.valuation_of_lookup _ hl, AlgebraSourceValues.meaning_offset,
        rdAE_65 hr hm]
      simp only [algebraInputs, dite_eq_left hm]
    · have hm : j < 1024 := hlen.2.2.2.2.2.2.2.1 ▸ hj
      rw [exec_boundA y hu (MldsaEmulatedHonest.kind67 (program := emu) (F0 := F0) (FH := FH))
          (hbv 66 (by simp)).2, roleVal, Ring.sourceVal_algebra _ _ _ _ hl (by decide),
        AlgebraSourceValues.valuation_of_lookup _ hl, AlgebraSourceValues.meaning_slack,
        rdAE_66 hr hm]
      simp only [algebraInputs, dite_eq_left hm]

/-- **The quotient's slot** reads the honest quotient. -/
theorem role_quot {classifier : SourceRoleClassifier} (hl : classifier.lookup 65 = some (.carry, 0))
    {j : ℕ} (hj : j < (program.value 65).size) :
    roleVal program F0 FH y classifier 65 j =
      program.execOf interp (honestVal program F0 FH y) 65 j := by
  have hf := MldsaCarrierQuot.field65 (program := program)
  have hm : j < 1024 := MldsaCarrierQuot.size65 (program := program) ▸ hj
  have hq := rd_q (program := program) (F0 := F0) (FH := FH) y (fun _ _ => 0)
    (program.chal0 interp) 0 hm
  rw [evalE_leaf] at hq
  rw [execOf_bound_eq_reader (honestVal program F0 FH y) E0 rfl MldsaCarrierHonest.kind65, roleVal,
    Ring.sourceVal_quotient _ _ _ _ hl]
  change castElt (a := 0) ((quotN y j : ℕ) : (interp 0).K) = _
  rw [← hq]
  exact castElt_castElt_of_eq hf _

omit [MldsaCarrierFront program] [MldsaCarrierSelect program] [MldsaCarrierQuot program]
  [RealizedProgram.PrimeCastField F0 pGold] [MLDSA44.MldsaHNativeData FH]
  [MLDSA44.MldsaHSample (MLDSA44.Emulated.MldsaEmbed.nat emu)]
  [MLDSA44.MldsaHConsts (MLDSA44.Emulated.MldsaEmbed.nat emu) FH]
  [MldsaHHonest (MLDSA44.Emulated.MldsaEmbed.nat emu)]
  [MldsaHSelHonest (MLDSA44.Emulated.MldsaEmbed.nat emu)] [MLDSA44.MldsaHNodes FH]
  [MldsaEmulatedHonest emu F0 FH] in
omit [MldsaCarrierRelation program] [MldsaRingStmt program] [TableSelect program] in
/-- **The high halves' slot** (algebra slot `8`) reads the honest high halves. -/
theorem role_high {classifier : SourceRoleClassifier}
    (hl : classifier.lookup 66 = some (.aWitness, 8)) (j : ℕ) :
    roleVal program F0 FH y classifier 66 j =
      program.execOf interp (honestVal program F0 FH y) 66 j := by
  have hc := MldsaCarrierHonest.member_cells (program := program) 66 (by simp)
  have hm := (honestVal_member (program := program) (F0 := F0) (FH := FH) y j).2.2.2.2.1
  rw [execOf_of_priv _ (kind_of_privCellB hc.1), roleVal, Ring.sourceVal_high _ _ _ _ hl]
  change castElt (a := 0) (if h : j < 1020 then qHonC y (interp 0).K ⟨j / 255, by omega⟩ (j % 255)
    else 0) = _
  rw [← hm]
  exact castElt_castElt_of_eq hc.2 _

/-- **A member's slot** reads the honest member value. -/
theorem role_member {classifier : SourceRoleClassifier} {r : SourceRoleEntry}
    (hl : classifier.lookup r.value = some (r.role, r.slot))
    (h : memberRoleB 56 57 58 59 r = true) (j : ℕ) :
    roleVal program F0 FH y classifier r.value j =
      program.execOf interp (honestVal program F0 FH y) r.value j := by
  have hkind : ∀ v ∈ [56, 57, 58, 59], (program.value v).kind = .priv := fun v hv =>
    kind_of_privCellB (MldsaCarrierHonest.member_cells v (List.mem_append_left _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv ⊢; omega))).1
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
        if_neg (by decide), if_pos rfl]
      rfl
    · rw [roleVal, Ring.sourceVal_mu _ _ _ _ hl, execOf_of_priv _ (hkind _ (by simp)), honestVal,
        if_neg (by decide), if_neg (by decide), if_pos rfl]
      rfl
  case selection =>
    obtain ⟨rfl, rfl⟩ := h
    rw [roleVal, Ring.sourceVal_index _ _ _ _ hl, execOf_of_priv _ (hkind _ (by simp)), honestVal,
      if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
    rfl

/-- **Every executed source coordinate agrees with the honest values**, from the checked role rows
of the program's classifier: `skip` lists the source values that are not executed. -/
theorem role_source_coordinates {rs : List SourceRoleEntry} (hrs : SourceRolesOk program rs)
    {valH valA invH invA : ℕ → ℕ} {heldH heldA : ℕ → Bool} {skip : List ℕ}
    (hrows : rs.all (roleRowB valH valA invH invA heldH heldA skip) = true)
    (hσH : (σH).val = valH) (hσA : (σA).val = valA) (hheldH : ∀ u, heldH u = true → u ∈ hV)
    (hheldA : ∀ u, heldA u = true → u ∈ aV)
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
  rcases hrow with ((((hx | hx) | ⟨hx, hq⟩) | ⟨hx, hq⟩) | ⟨⟨hu, huv⟩, hh⟩) | ⟨⟨hu, huv⟩, hh⟩
  · obtain ⟨h1, h2⟩ := hskip _ (List.contains_iff_mem.mp hx)
    rcases hk with hk | hk
    · exact absurd hk h1
    · rw [h2] at hk
      cases hk
  · exact role_member y hl hx j
  · rcases r with ⟨v, role, slot, field, node⟩
    simp only at hx hq hl hj ⊢
    subst hx
    cases role <;> simp only [beq_iff_eq, Bool.false_eq_true] at hq
    case carry =>
      subst hq
      exact role_quot y hl hj
  · rcases r with ⟨v, role, slot, field, node⟩
    simp only at hx hq hl hj ⊢
    subst hx
    cases role <;> simp only [beq_iff_eq, Bool.false_eq_true] at hq
    case aWitness =>
      subst hq
      exact role_high y hl j
  · have hval : (σH).val (invH r.value) = r.value := by rw [hσH]; exact huv
    have hl' := hl
    rw [← hval] at hl' ⊢
    exact role_heldH y (hheldH _ hu) hl' hh j
  · have hval : (σA).val (invA r.value) = r.value := by rw [hσA]; exact huv
    have hl' := hl
    rw [← hval] at hl' hj ⊢
    exact role_heldA y (hheldA _ hu) hl' hh hj

end Meanings

end GordieHowe.MLDSA44.Ring.Carrier
