-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweCerts.Applications.MLDSA44.Ring.Native.HonestFull
public import GordieHowe.Language.Honest.SourceRoles

@[expose] public section

/-!
# The committed source values' classes of a native ML-DSA-44 ring program

`MldsaRingExec.cell_classes` classifies each committed source value through the inverse of the
renaming. The classification here checks the finite source-role rows at the inverse table of the
renaming on the held values (`RealizedProgram.Renaming.invOn`), built once from the embedding
data, whose lookups take logarithmic time per row.
-/

namespace GordieHowe.MLDSA44.Ring.Native

open RealizedProgram

set_option hygiene false in
local notation "ringV" => MldsaRingEmbed.V program

/-- **The inverse of a renaming of values on `V`**, read from its table (`Renaming.invOn`): the
held value renamed to `w`, `w` itself where none is. -/
def heldInv (σ' : Renaming) (V : List ℕ) (w : ℕ) : ℕ := ((σ'.invOn V).get? w).getD w

/-- **Whether a value is held**, by the table: the table gives it back at its image. -/
def heldB (σ' : Renaming) (V : List ℕ) (u : ℕ) : Bool := (σ'.invOn V).get? (σ'.val u) == some u

theorem mem_of_heldB {σ' : Renaming} {V : List ℕ} {u : ℕ} (h : heldB σ' V u = true) : u ∈ V :=
  (Renaming.invOn_spec (beq_iff_eq.mp h)).1

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

/-- **One source-role row's class** at a renaming `val` with inverse `inv` on the values `held`
accepts: a value in `skip`, a member value of field `0`, or a renamed value of the honest values'
classes. -/
def rowB (skip members : List ℕ) (val inv : ℕ → ℕ) (held : ℕ → Bool) (r : SourceRoleEntry) :
    Bool :=
  skip.contains r.value ||
  (members.contains r.value && r.field == 0 && r.node.map (·.name) == some "GF(p^1)") ||
  (held (inv r.value) && val (inv r.value) == r.value &&
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
    {skip : List ℕ} {val inv : ℕ → ℕ} {held : ℕ → Bool}
    (hrows : rs.all (rowB skip [MldsaRandomPoint.aHat program, MldsaRandomPoint.t1 program,
      MldsaRingFront.muA program, (TableSelect.shape program).idx, MldsaRandomPoint.q program]
      val inv held) = true)
    (hσ : (MldsaRingEmbed.σ program).val = val) (hheld : ∀ u, held u = true → u ∈ ringV)
    (hskip : ∀ v ∈ skip, (program.value v).kind ≠ .priv) :
    (List.range program.values.length).all (fun v =>
      !program.privCellB v || !decide (program.IsSourceValue v) ||
        ([MldsaRandomPoint.aHat program, MldsaRandomPoint.t1 program, MldsaRingFront.muA program,
            (TableSelect.shape program).idx, MldsaRandomPoint.q program].contains v && program.valueField v == 0 &&
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
  have hum := hheld _ hu
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
