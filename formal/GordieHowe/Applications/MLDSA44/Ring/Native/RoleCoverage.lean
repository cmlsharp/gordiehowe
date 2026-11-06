-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Ring.Native.HonestFull
public import GordieHowe.Language.Honest.SourceRoles

@[expose] public section

/-!
# The committed source values' classes of a native ML-DSA-44 ring program

`MldsaRingExec.cell_classes` classifies each committed source value through the inverse of the
renaming. The classification here checks the finite source-role rows at a piecewise inverse, whose
evaluation takes constant time per row, and checks once that this inverse undoes the renaming on
`ringV`. The first-match search `ringInv` is then evaluated by a lemma, in no kernel reduction.
-/

namespace GordieHowe.MLDSA44.Ring.Native

open RealizedProgram

/-- **The inverse of `valR` on the renamed held values**, piecewise (`v` itself elsewhere). -/
def invR (v : ℕ) : ℕ :=
  if v < 12 then [0, 4, 2, 1, 2, 3, 0, 5, 6, 9, 40, 9].getD v v
  else if v < 36 then v - 2
  else if v < 44 then [41, 42, 43, 44, 45, 36, 46, 35].getD (v - 36) v
  else if v < 52 then v + 3
  else if v < 60 then v
  else if v < 69 then v - 3
  else if v < 71 then v + 50
  else if v < 73 then v - 2
  else if v < 520 then v + 48
  else if v < 529 then v
  else if v < 538 then v + 46
  else v

/-- **The inverse of `valQ`**: the QROM parameters merge constant `9`, so every identifier from `9`
is `invR` one larger. -/
def invQ (v : ℕ) : ℕ := invR (if 9 ≤ v then v + 1 else v)

/-- `invR` undoes `valR` on `ringV`. -/
theorem invR_valR : ∀ u ∈ ringV, invR (valR u) = u := by decide +kernel

/-- `invQ` undoes `valQ` on `ringV`. -/
theorem invQ_valQ : ∀ u ∈ ringV, invQ (valQ u) = u := by decide +kernel

/-- **Membership in `ringV`** by its intervals. -/
def ringVB (u : ℕ) : Bool :=
  u < 7 || (9 ≤ u && u < 34) || u == 35 || u == 36 || (40 ≤ u && u < 55) || (57 ≤ u && u < 66) ||
    u == 69 || u == 70 || (119 ≤ u && u < 568) || (575 ≤ u && u < 584)

theorem mem_ringV_of_ringVB {u : ℕ} (h : ringVB u = true) : u ∈ ringV := by
  simp only [ringVB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  simp only [ringV, List.mem_append, List.mem_range'_1, List.mem_cons, List.not_mem_nil, or_false]
  omega

/-- Domain `H`'s core hash values are held. -/
theorem coreV_held : (69 ∈ ringV ∧ 119 ∈ ringV) ∧ ∀ p : Fin 10, (p : ℕ) ≠ 0 → ∀ t : Fin 24,
    wordsVal p t ∈ ringV :=
  ⟨⟨mem_ringV_of_ringVB rfl, mem_ringV_of_ringVB rfl⟩, fun p hp t => mem_ringV_of_ringVB
    ((by decide +kernel : ∀ p : Fin 10, (p : ℕ) ≠ 0 → ∀ t : Fin 24, ringVB (wordsVal p t) = true)
      p hp t)⟩

/-- SampleInBall's cells are held. -/
theorem selV_held : ∀ u ∈ [556, 557, 560, 561, 562, 563, 564, 565], u ∈ ringV := fun _ hu =>
  mem_ringV_of_ringVB
    ((by decide : ∀ u ∈ [556, 557, 560, 561, 562, 563, 564, 565], ringVB u = true) _ hu)

/-- Domain `A`'s values are held. -/
theorem aV_held : ∀ u ∈ MLDSA44.Native.AValues ++ [57, 64, 65], u ∈ ringV := fun _ hu =>
  mem_ringV_of_ringVB
    ((by decide : ∀ u ∈ MLDSA44.Native.AValues ++ [57, 64, 65], ringVB u = true) _ hu)

/-- **A left inverse of the renaming evaluates the first-match inverse.** -/
theorem ringInv_eq_of_leftInverse {σ' : Renaming} {g : ℕ → ℕ}
    (hg : ∀ u ∈ ringV, g (σ'.val u) = u) {u : ℕ} (hu : u ∈ ringV) :
    ringInv σ' (σ'.val u) = u := by
  unfold ringInv
  rcases hf : ringV.find? (fun w => σ'.val w == σ'.val u) with _ | w
  · exact absurd (by simp) (List.find?_eq_none.mp hf u hu)
  · have hw := List.find?_some hf
    have hm := List.mem_of_find?_eq_some hf
    have heq : σ'.val w = σ'.val u := by simpa using hw
    simp only [Option.getD_some]
    rw [← hg w hm, heq, hg u hu]

/-- **The hash word at a source-role slot**: slot `2 + 24 p + t` of permutation `p ≠ 0`. -/
def wordsB (slot u : ℕ) : Bool :=
  26 ≤ slot && slot < 242 &&
    wordsVal (Fin.ofNat 10 ((slot - 2) / 24)) (Fin.ofNat 24 ((slot - 2) % 24)) == u

theorem coreHashB_of_wordsB {slot u : ℕ} (h : wordsB slot u = true) : coreHashB u = true := by
  simp only [wordsB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨hl, hh⟩, rfl⟩ := h
  have hp : (Fin.ofNat 10 ((slot - 2) / 24) : ℕ) ≠ 0 := by
    simp only [Fin.val_ofNat]
    omega
  simp only [coreHashB, wordsOwner_checks.1, bne_iff_ne, Bool.or_eq_true]
  exact Or.inr (by simpa using hp)

/-- **One source-role row's class** at a renaming `val` with inverse `inv`: a value in `skip`, a
member value of field `0`, or a renamed value of the honest values' classes. -/
def rowB (skip members : List ℕ) (val inv : ℕ → ℕ) (r : SourceRoleEntry) : Bool :=
  skip.contains r.value ||
  (members.contains r.value && r.field == 0 && r.node.map (·.name) == some "GF(p^1)") ||
  (ringVB (inv r.value) && val (inv r.value) == r.value &&
    ((MLDSA44.Native.AValues.contains (inv r.value) && r.field == 0 &&
        r.node.map (·.name) == some "GF(p^1)") ||
      ((inv r.value == 69 || inv r.value == 119 || wordsB r.slot (inv r.value) ||
          [557, 560, 562, 563, 564, 565].contains (inv r.value)) && r.field == 1 &&
        r.node.map (·.name) == some "GF(2^16)") ||
      ([556, 561].contains (inv r.value) && r.field == 1 &&
        r.node.map (·.name) == some "bit")))

variable {program : RealizedProgram} [MldsaRingEmbed program] [MldsaRingRelation program]
  [MldsaRingStmt program] [TableSelect program] [MldsaRingFront program] [MldsaRingHonest program]

/-- **The committed source values' classes from the checked role rows.** `skip` lists source values
that are not committed; the rows' classes then give `MldsaRingExec.cell_classes`. -/
theorem cell_classes_of_rows {rs : List SourceRoleEntry} (hrs : SourceRolesOk program rs)
    {skip : List ℕ} {val inv : ℕ → ℕ}
    (hrows : rs.all (rowB skip [MldsaRingRelation.aHat program, MldsaRingRelation.t1 program,
      MldsaRingFront.muA program, (TableSelect.shape program).idx] val inv) = true)
    (hσ : (MldsaRingEmbed.σ program).val = val)
    (hskip : ∀ v ∈ skip, (program.value v).kind ≠ .priv) :
    (List.range program.values.length).all (fun v =>
      !program.privCellB v || !decide (program.IsSourceValue v) ||
        ([MldsaRingRelation.aHat program, MldsaRingRelation.t1 program, MldsaRingFront.muA program,
            (TableSelect.shape program).idx].contains v && program.valueField v == 0 &&
          (program.value v).node.map (·.name) == some "GF(p^1)") ||
        (decide (MldsaRingHonest.inv program v ∈ ringV) &&
          (MldsaRingEmbed.σ program).val (MldsaRingHonest.inv program v) == v &&
          ((MLDSA44.Native.AValues.contains (MldsaRingHonest.inv program v) &&
              program.valueField v == 0 &&
              (program.value v).node.map (·.name) == some "GF(p^1)") ||
            (natGF16B (MldsaRingHonest.inv program v) && program.valueField v == 1 &&
              (program.value v).node.map (·.name) == some "GF(2^16)") ||
            ([556, 561].contains (MldsaRingHonest.inv program v) && program.valueField v == 1 &&
              (program.value v).node.map (·.name) == some "bit")))) = true := by
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
  simp only [hp, decide_true, hs, Bool.not_true, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true,
    beq_iff_eq, hf, hnode, decide_eq_true_eq]
  rcases hrow with (hx | hx) | ⟨⟨hu, huv⟩, hc⟩
  · exact absurd hk (hskip _ (List.contains_iff_mem.mp hx))
  · exact Or.inl hx
  have hum := mem_ringV_of_ringVB hu
  have hinv : MldsaRingHonest.inv program r.value = inv r.value := by
    have h := MldsaRingHonest.inv_val (program := program) _ hum
    rwa [hσ, huv] at h
  have hval : (MldsaRingEmbed.σ program).val (inv r.value) = r.value := by rw [hσ, huv]
  rw [hinv]
  refine Or.inr ⟨⟨hum, hval⟩, ?_⟩
  rcases hc with (ha | hg) | hb
  · exact Or.inl (Or.inl ha)
  · refine Or.inl (Or.inr ⟨⟨?_, hg.1.2⟩, hg.2⟩)
    simp only [natGF16B, Bool.or_eq_true]
    rcases hg.1.1 with ((h | h) | h) | h
    · exact Or.inl (by simp [coreHashB, h])
    · exact Or.inl (by simp [coreHashB, h])
    · exact Or.inl (coreHashB_of_wordsB h)
    · exact Or.inr h
  · exact Or.inr hb

end GordieHowe.MLDSA44.Ring.Native
