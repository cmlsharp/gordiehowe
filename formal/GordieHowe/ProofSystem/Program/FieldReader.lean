-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.FieldDomain
public import GordieHowe.ProofSystem.Program.FieldTable
public import GordieHowe.Language.RealizedProgram.Reader
public import GordieHowe.Language.RealizedProgram.Placement
public import GordieHoweNative.ProofSystem.Program.FieldReader

/-!
# GordieHowe: a domain's checks at a packing descriptor

`fieldOkB` (the checks of domain `d`, `FieldDomain.lean`) reads the field's packing facts `Pk`.
`fieldOkBD` (`GordieHoweNative/ProofSystem/Program/FieldReader.lean`) is every check of it but the
Ligero certificate's, at a packing descriptor `D` (`PackingDesc`): naturals and Booleans at the
queries the program makes. Here:

* **the descriptor's lookups are the packing's** (`desc_edgeOk`, `desc_nodeDeg`, `desc_skipOk`):
  `Pk.desc D` reads `Pk` at `D`'s keys, so an answer it gives is `Pk`'s, and it answers `false` (or
  no degree) only where it has no entry;
* **the checks at the packing's facts are `fieldOkB`'s** (`fieldOkB_of_checks`), the realized
  edges the plan's edges with a kit (`realizedEdges_map_plan`) and the quadratic triples' cells
  from the walk (`quadsOk_of_quadsOkW`);
* **a descriptor equal to the packing's gives them** (`fieldChecksB_of_desc`): the checks read the
  descriptor only where it answers, monotonically;
* **`fieldOkB_of_desc`**: `fieldOkBD d P D`, `Pk.desc D = D` (checked once per field) and the
  Ligero certificate's checks give `fieldOkB d P Pk c`;
* **compiled code runs `fieldOkBD` at a context built once** (`fieldOkBD_csimp`).
-/

public section

namespace GordieHowe.RealizedProgram

open Export

/-- **The packing facts of a field's packing.** -/
def PackReads.ofPacking {F : FieldInterp} (Pk : F.Packing) : PackReads :=
  ⟨Pk.n, fun m k mode => (Pk.edge m k mode).isSome, fun s => some (Pk.nodeDeg s),
    fun w k => (Pk.skip w k).isSome, Pk.nodes.isSome⟩

/-! ## The descriptor's lookups -/

section Desc

variable {F : FieldInterp} (Pk : F.Packing) (D : PackingDesc)

theorem desc_edgeOk {m k : ℕ} {mode : PackingMode} (h : (Pk.desc D).edgeOk m k mode = true) :
    (Pk.edge m k mode).isSome = true := by
  unfold PackingDesc.edgeOk at h
  split at h
  · rename_i x hx
    have hm := List.mem_of_find?_eq_some hx
    have hp := List.find?_some hx
    simp only [FieldInterp.Packing.desc, List.mem_map] at hm
    obtain ⟨y, -, rfl⟩ := hm
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨⟨h1, h2⟩, h3⟩ := hp
    rw [← h1, ← h2, ← h3]
    exact h
  · cases h

theorem desc_nodeDeg {s : String} {nd : Option ℕ} (h : (Pk.desc D).nodeDeg? s = some nd) :
    Pk.nodeDeg s = nd := by
  unfold PackingDesc.nodeDeg? at h
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
  have hm := List.mem_of_find?_eq_some hx
  have hp := List.find?_some hx
  simp only [FieldInterp.Packing.desc, List.mem_map] at hm
  obtain ⟨y, -, rfl⟩ := hm
  simp only [beq_iff_eq] at hp
  rw [← hp]

theorem desc_skipOk {w k : ℕ} (h : (Pk.desc D).skipOk w k = true) :
    (Pk.skip w k).isSome = true := by
  unfold PackingDesc.skipOk at h
  split at h
  · rename_i x hx
    have hm := List.mem_of_find?_eq_some hx
    have hp := List.find?_some hx
    simp only [FieldInterp.Packing.desc, List.mem_map] at hm
    obtain ⟨y, -, rfl⟩ := hm
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨h1, h2⟩ := hp
    rw [← h1, ← h2]
    exact h
  · cases h

end Desc

/-! ## The checks at the packing's facts -/

/-- **The realized edges' plan edges** are the plan's edges the field realizes. -/
theorem realizedEdges_map_plan {F : FieldInterp} (Pk : F.Packing) (es : List PackingEdge) :
    (realizedEdges Pk es).map REdge.plan =
      es.filter fun e => (Pk.edge e.childDegree e.degree e.mode).isSome := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    rw [realizedEdges] at ih ⊢
    rw [List.filterMap_cons, List.filter_cons]
    cases h : Pk.edge e.childDegree e.degree e.mode <;> simp [ih]

section

variable {ir : RealizedProgram} {d : ℕ}

/-- **The quadratic triples' cells from the walk of the predicates** (`quadsOkW`). -/
theorem quadsOk_of_quadsOkW (h : @FReader.quadsOkW ir (FReader.ofProgram ir) d = true) :
    ir.QuadsOk d := by
  intro q a b c hq
  obtain ⟨⟨⟨p, hp⟩, hpq⟩, i⟩ := q
  change ir.quadLeaves d p = some (a, b, c) at hq
  have hw := (allIdx_iff _ ir.predicates 0).1 h p hp
  rw [← predicate_eq_getD] at hw
  change (match ir.quadLeaves d p with
    | some (a, b, c) =>
      ir.exprLen (ir.quadLhs p) == 0 ||
        (@FReader.quadCellsAt ir (FReader.ofProgram ir) d (ir.exprLen (ir.quadLhs p)) a &&
          @FReader.quadCellsAt ir (FReader.ofProgram ir) d (ir.exprLen (ir.quadLhs p)) b &&
          @FReader.quadCellsAt ir (FReader.ofProgram ir) d (ir.exprLen (ir.quadLhs p)) c)
    | none => true) = true at hw
  rw [hq] at hw
  have hi : i.1 < ir.exprLen (ir.quadLhs p) := i.2
  have hL : (ir.exprLen (ir.quadLhs p) == 0) = false := by
    simp only [beq_eq_false_iff_ne]
    omega
  simp only [hL, Bool.false_or, Bool.and_eq_true] at hw
  obtain ⟨⟨ha, hb⟩, hc⟩ := hw
  have cell : ∀ u, @FReader.quadCellsAt ir (FReader.ofProgram ir) d (ir.exprLen (ir.quadLhs p)) u
      = true → CellKey.val u i ∈ ir.cellKeys d := fun u hu => by
    change (decide (u < ir.values.length) && ir.isCellValue d u &&
      decide (ir.exprLen (ir.quadLhs p) ≤ (ir.value u).size)) = true at hu
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hu
    exact (mem_cellKeys_val ir).2 ⟨hu.1.1, hu.1.2, Nat.lt_of_lt_of_le hi hu.2⟩
  exact ⟨cell a ha, cell b hb, cell c hc⟩

/-- **`fieldOkB` from the checks at the packing's facts** and the Ligero certificate's. -/
theorem fieldOkB_of_checks {I : Interp} {P : Export.Plan} {Pk : (I (ir.domainField d)).Packing}
    {c : LigeroCert}
    (h : @FReader.fieldChecksB ir (FReader.ofProgram ir) d P (PackReads.ofPacking Pk) = true)
    (hv : c.validB Pk.q = true) (hl : ir.planLigeroB P d c = true) :
    ir.fieldOkB d P Pk c = true := by
  rw [FReader.fieldChecksB] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hlen, ht⟩, hp⟩, hvw⟩, hc⟩, hb⟩, hq⟩ := h
  have hmap := realizedEdges_map_plan Pk (ir.planPacking P d)
  have hlen' : (ir.fieldEdgesOf d P Pk).length = ((ir.planPacking P d).filter fun e =>
      (Pk.edge e.childDegree e.degree e.mode).isSome).length := by
    rw [← hmap, List.length_map]
  rw [fieldOkB]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, hc⟩, hb⟩, decide_eq_true (quadsOk_of_quadsOkW hq)⟩, hv⟩, hl⟩
  · rw [hlen']
    exact hlen
  · rw [hmap]
    exact ht
  · rw [hmap]
    exact hp
  · rw [hmap]
    exact hvw

end

/-! ## The checks at a descriptor equal to the packing's -/

section Mono

variable (ir : RealizedProgram) (d : ℕ)

theorem FReader.nodeDegB_mono {K K' : PackReads} (hn : K.n = K'.n)
    (hd : ∀ s nd, K.nodeDeg s = some nd → K'.nodeDeg s = some nd) {es : List PackingEdge}
    {s : String} (h : FReader.nodeDegB K es s = true) : FReader.nodeDegB K' es s = true := by
  unfold FReader.nodeDegB at h ⊢
  cases hK : K.nodeDeg s with
  | none => rw [hK] at h; cases h
  | some nd =>
    rw [hK] at h
    rw [hd s nd hK, ← hn]
    exact h

theorem FReader.nameOkB_mono {K K' : PackReads} (hn : K.n = K'.n)
    (hd : ∀ s nd, K.nodeDeg s = some nd → K'.nodeDeg s = some nd) {es : List PackingEdge}
    {o : Option String} (h : FReader.nameOkB K es o = true) : FReader.nameOkB K' es o = true := by
  cases o with
  | none => rfl
  | some s => exact FReader.nodeDegB_mono hn hd h

theorem FReader.placeOkB_mono [FReader] {K K' : PackReads} (hn : K.n = K'.n)
    (hd : ∀ s nd, K.nodeDeg s = some nd → K'.nodeDeg s = some nd) {es : List PackingEdge}
    (h : FReader.placeOkB ir d K es = true) : FReader.placeOkB ir d K' es = true := by
  unfold FReader.placeOkB FReader.placeOkE at h ⊢
  rw [Twin.okB_allE_iff] at h ⊢
  intro k hk
  have hk' := h k hk
  rw [Twin.okB_guardE] at hk' ⊢
  unfold FReader.placeValueB at hk' ⊢
  split_ifs at hk' ⊢ with h1 h2
  · simp only [Bool.or_eq_true] at hk' ⊢
    exact hk'.imp id (FReader.nameOkB_mono hn hd)
  · simp only [Bool.or_eq_true] at hk' ⊢
    exact hk'.imp id (FReader.nameOkB_mono hn hd)
  · exact hk'

theorem FReader.batchesOkB_mono {K K' : PackReads} (hh : K.hasNodes = K'.hasNodes)
    (hs : ∀ w k, K.skipOk w k = true → K'.skipOk w k = true)
    (h : FReader.batchesOkB ir d K = true) : FReader.batchesOkB ir d K' = true := by
  unfold FReader.batchesOkB at h ⊢
  rw [List.all_eq_true] at h ⊢
  intro b hb
  have hb' := h b hb
  simp only [Bool.or_eq_true, Bool.and_eq_true] at hb' ⊢
  rw [← hh]
  exact hb'.imp id fun ⟨h1, h2⟩ => ⟨hs _ _ h1, h2⟩

/-- **The checks at a descriptor equal to the packing's give the checks at the packing's
facts**: every answer the descriptor gives is the packing's (`desc_edgeOk`, `desc_nodeDeg`,
`desc_skipOk`), and the checks read its answers monotonically. -/
theorem FReader.fieldChecksB_of_desc [FReader] {F : FieldInterp} {Pk : F.Packing} {D : PackingDesc}
    {P : Export.Plan} (hD : Pk.desc D = D)
    (h : FReader.fieldChecksB ir d P (PackReads.ofDesc D) = true) :
    FReader.fieldChecksB ir d P (PackReads.ofPacking Pk) = true := by
  rw [← hD] at h
  rw [FReader.fieldChecksB] at h ⊢
  simp only [Bool.and_eq_true, beq_iff_eq] at h ⊢
  obtain ⟨⟨⟨⟨⟨⟨hlen, ht⟩, hp⟩, hvw⟩, hc⟩, hb⟩, hq⟩ := h
  have hall := List.length_filter_eq_length_iff.mp hlen
  have hD' : (ir.planPacking P d).filter (fun e => (PackReads.ofDesc (Pk.desc D)).edgeOk
      e.childDegree e.degree e.mode) = ir.planPacking P d := List.filter_eq_self.mpr hall
  have hP : (ir.planPacking P d).filter (fun e => (PackReads.ofPacking Pk).edgeOk
      e.childDegree e.degree e.mode) = ir.planPacking P d :=
    List.filter_eq_self.mpr fun e he => desc_edgeOk Pk D (hall e he)
  rw [hD'] at ht hp hvw
  rw [hP]
  have hdeg : ∀ s nd, (PackReads.ofDesc (Pk.desc D)).nodeDeg s = some nd →
      (PackReads.ofPacking Pk).nodeDeg s = some nd := fun s nd hs => by
    change some (Pk.nodeDeg s) = some nd
    rw [desc_nodeDeg Pk D hs]
  exact ⟨⟨⟨⟨⟨⟨rfl, ht⟩, FReader.placeOkB_mono ir d (K := PackReads.ofDesc (Pk.desc D))
    (K' := PackReads.ofPacking Pk) rfl hdeg hp⟩, hvw⟩, hc⟩,
    FReader.batchesOkB_mono ir d (K := PackReads.ofDesc (Pk.desc D))
      (K' := PackReads.ofPacking Pk) rfl (fun w k hs => desc_skipOk Pk D hs) hb⟩, hq⟩

end Mono

/-- **The checks of domain `d` from the descriptor**: the checks at a descriptor `D` (`fieldOkBD`),
the field's packing at `D`'s queries equal to `D` (`Pk.desc D = D`, checked once per field) and the
Ligero certificate's checks give `fieldOkB`. -/
theorem fieldOkB_of_desc {ir : RealizedProgram} {I : Interp} {d : ℕ} {P : Export.Plan}
    {Pk : (I (ir.domainField d)).Packing} {D : PackingDesc} {c : LigeroCert}
    (hD : Pk.desc D = D) (h : ir.fieldOkBD d P D = true) (hv : c.validB Pk.q = true)
    (hl : ir.planLigeroB P d c = true) : ir.fieldOkB d P Pk c = true :=
  fieldOkB_of_checks (@FReader.fieldChecksB_of_desc ir d (FReader.ofProgram ir) _ Pk D P hD h)
    hv hl

/-! ## The compiled checks -/

/-- **The compiled field checks' reader of the program's context is the kernel's.** -/
theorem FReader.ofCtx_build (ir : RealizedProgram) :
    FReader.ofCtx ir (FCtx.build ir) = FReader.ofProgram ir := by
  rw [FReader.ofCtx, FCtx.build, FReader.ofProgram, PReader.ofCtx_build]
  congr 1
  funext v
  rw [getD_getElem?_toArray]
  exact getD_memoList v

/-- **Compiled code runs the checks at a descriptor at the context built once** (`fieldOkBC`). -/
@[csimp] theorem fieldOkBD_csimp : @fieldOkBD = @fieldOkBC := by
  funext ir d P D
  rw [fieldOkBD, fieldOkBC]
  show _ = @FReader.fieldChecksB ir (FReader.ofCtx ir (FCtx.build ir)) d P (PackReads.ofDesc D)
  rw [FReader.ofCtx_build]

end GordieHowe.RealizedProgram
