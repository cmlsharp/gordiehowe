-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.Check
public import GordieHowe.Language.RealizedProgram.StructureCheck
public import GordieHoweNative.Language.RealizedProgram.SourceRoles

public section

namespace GordieHowe.RealizedProgram

/-- **The certified source-role contract**: unique assignments, correct placement, and coverage. -/
structure SourceRolesOk (ir : RealizedProgram) (rs : List SourceRoleEntry) : Prop where
  ordered : rs.Pairwise (fun a b => a.value < b.value)
  entries : ∀ r ∈ rs, r.value < ir.values.length ∧
    (ir.value r.value).role = .source ∧ ir.valueField r.value = r.field ∧
    (ir.value r.value).node = r.node
  covered : ∀ v < ir.values.length, (ir.value v).needsSourceRole = true →
    ∃ r, (sourceRoleTable rs).get? v = some r

/-- **A lookup returns a record at its declared key**, from the checked list. -/
theorem sourceRoleTable_mem {rs : List SourceRoleEntry} {v : Nat} {r : SourceRoleEntry}
    (h : (sourceRoleTable rs).get? v = some r) : r ∈ rs ∧ r.value = v := by
  have hm : (v, r) ∈ rs.map (fun e => (e.value, e)) := by
    have hp : ((rs.map (fun e => (e.value, e))).foldl
        (fun t kv => t.set kv.1 kv.2) (NatTrie.nil : NatTrie SourceRoleEntry)).get? v = some r := by
      simpa only [List.foldl_map, sourceRoleTable] using h
    rcases NatTrie.mem_of_get?_foldl _ .nil hp with hm | hn
    · exact hm
    · simp only [NatTrie.get?_nil, reduceCtorEq] at hn
  obtain ⟨e, he, hpair⟩ := List.mem_map.mp hm
  have hv := congrArg Prod.fst hpair
  have hr := congrArg Prod.snd hpair
  cases hr
  exact ⟨he, hv⟩

private theorem rolesFold_get_of_absent (rs : List SourceRoleEntry) (t : NatTrie SourceRoleEntry)
    {v : Nat} (h : ∀ r ∈ rs, r.value ≠ v) :
    (rs.foldl (fun tab r => tab.set r.value r) t).get? v = t.get? v := by
  induction rs generalizing t with
  | nil => rfl
  | cons a rs ih =>
    rw [List.foldl_cons, ih _ (fun r hr => h r (List.mem_cons_of_mem _ hr))]
    rw [NatTrie.get?_set, ite_eq_right (Ne.symm (h a (List.mem_cons_self ..)))]

private theorem rolesFold_get_of_mem {rs : List SourceRoleEntry} {r : SourceRoleEntry}
    (h : rs.Pairwise (fun a b => a.value ≠ b.value)) (hr : r ∈ rs)
    (t : NatTrie SourceRoleEntry) :
    (rs.foldl (fun tab e => tab.set e.value e) t).get? r.value = some r := by
  induction rs generalizing t with
  | nil => simp at hr
  | cons a rs ih =>
    rw [List.pairwise_cons] at h
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hr with hr | hr
    · subst r
      rw [rolesFold_get_of_absent rs _ (fun b hb => Ne.symm (h.1 b hb)),
        NatTrie.get?_set, ite_eq_left rfl]
    · exact ih h.2 hr _

/-- **Every checked entry is returned at its declared key**, with exactly its tag and slot.
Generated named-role facts use this to connect application names to the shared classifier. -/
theorem SourceRolesOk.lookup_of_mem {ir : RealizedProgram} {rs : List SourceRoleEntry}
    (h : SourceRolesOk ir rs) {r : SourceRoleEntry} (hr : r ∈ rs) :
    (sourceRoleClassifier rs).lookup r.value = some (r.role, r.slot) := by
  have ht : (sourceRoleTable rs).get? r.value = some r :=
    rolesFold_get_of_mem (h.ordered.imp (fun hab => Nat.ne_of_lt hab)) hr .nil
  change ((sourceRoleTable rs).get? r.value).map _ = _
  rw [ht]
  rfl

/-- **The classifier equation for the checked entry at position `k`.** -/
theorem SourceRolesOk.lookup_at {ir : RealizedProgram} {rs : List SourceRoleEntry}
    (h : SourceRolesOk ir rs) {k : Nat} {r : SourceRoleEntry} (hr : rs[k]? = some r) :
    (sourceRoleClassifier rs).lookup r.value = some (r.role, r.slot) :=
  h.lookup_of_mem (List.mem_of_getElem? hr)

/-- **Every returned role has the certified field and packing node.** -/
theorem SourceRolesOk.lookup {ir : RealizedProgram} {rs : List SourceRoleEntry}
    (h : SourceRolesOk ir rs) {v : Nat} {r : SourceRoleEntry}
    (hr : (sourceRoleTable rs).get? v = some r) :
    v < ir.values.length ∧ (ir.value v).role = .source ∧
    ir.valueField v = r.field ∧ (ir.value v).node = r.node := by
  obtain ⟨hm, hv⟩ := sourceRoleTable_mem hr
  simpa only [hv] using h.entries r hm

/-- **The classifier returns exactly the tag and slot of a checked record.**
Application-specific witness equations determine the meaning of those tags and slots. -/
theorem SourceRolesOk.classifier {ir : RealizedProgram} {rs : List SourceRoleEntry}
    (h : SourceRolesOk ir rs) {v : Nat} {role : SourceRole} {slot : Nat}
    (hc : (sourceRoleClassifier rs).lookup v = some (role, slot)) :
    ∃ r ∈ rs, r.value = v ∧ r.role = role ∧ r.slot = slot ∧
      ir.valueField v = r.field ∧ (ir.value v).node = r.node := by
  obtain ⟨r, hr, he⟩ := Option.map_eq_some_iff.mp hc
  obtain ⟨hm, hv⟩ := sourceRoleTable_mem hr
  have hp := h.lookup hr
  have he' : r.role = role ∧ r.slot = slot := Prod.mk.inj he
  exact ⟨r, hm, hv, he'.1, he'.2, hp.2.2.1, hp.2.2.2⟩

/-- **The adjacent-key check establishes strict ordering and therefore uniqueness.** -/
theorem sourceRolesOrdered_sound : ∀ {rs : List SourceRoleEntry},
    sourceRolesOrderedB rs = true → rs.Pairwise (fun a b => a.value < b.value)
  | [], _ => .nil
  | [_], _ => by simp
  | a :: b :: rs, h => by
    rw [sourceRolesOrderedB, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := sourceRolesOrdered_sound h.2
    refine List.pairwise_cons.mpr ⟨?_, ih⟩
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact h.1
    · exact Nat.lt_trans h.1 ((List.pairwise_cons.mp ih).1 c hc)

/-- **A checked record agrees with the source value at its index.** -/
theorem SourceRoleEntry.check_sound {ir : RealizedProgram} {r : SourceRoleEntry}
    (h : r.check ir ir.valT ir.values.length = true) :
    r.value < ir.values.length ∧ (ir.value r.value).role = .source ∧
    ir.valueField r.value = r.field ∧ (ir.value r.value).node = r.node := by
  have hv : ir.valT.getD r.value default = ir.value r.value := valueT_eq ir r.value
  simp only [SourceRoleEntry.check, hv, Bool.and_eq_true,
    decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- **The role check supplies the source-role contract.** -/
theorem sourceRoles_sound {ir : RealizedProgram} {rs : List SourceRoleEntry}
    (h : sourceRolesB ir rs = true) : SourceRolesOk ir rs := by
  simp only [sourceRolesB, Bool.and_eq_true, List.all_eq_true] at h
  refine ⟨sourceRolesOrdered_sound h.1.1, fun r hr => SourceRoleEntry.check_sound (h.1.2 r hr), ?_⟩
  have hc := h.2
  rw [← allIdx_csimp, allIdx_values_iff] at hc
  intro v hv hs
  have hv' := hc v hv
  simp only [hs, Bool.not_true, Bool.false_or] at hv'
  exact Option.isSome_iff_exists.mp hv'

/-- **The optional source-role contract.** A consumer receives coverage only after
showing that its role table is the table present in the checked data. -/
def SourceRolesPartOk (ir : RealizedProgram) (rs : Option (List SourceRoleEntry)) : Prop :=
  ∀ roles, rs = some roles → SourceRolesOk ir roles

/-- **A present checked table supplies its placement and coverage facts.**
Consumers use this eliminator without unfolding the optional contract. -/
theorem SourceRolesPartOk.present {ir : RealizedProgram} {rs : Option (List SourceRoleEntry)}
    (h : SourceRolesPartOk ir rs) {roles : List SourceRoleEntry} (hr : rs = some roles) :
    SourceRolesOk ir roles := h roles hr

/-- **The optional check is sound**, without asserting anything when no table is present. -/
theorem sourceRolesPart_sound {ir : RealizedProgram} {rs : Option (List SourceRoleEntry)}
    (h : sourceRolesPartB ir rs = true) : SourceRolesPartOk ir rs := by
  intro roles hr
  rw [hr] at h
  exact sourceRoles_sound h

end GordieHowe.RealizedProgram
