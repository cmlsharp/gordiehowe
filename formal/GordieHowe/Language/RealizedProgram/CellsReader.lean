-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.Placement
public import GordieHowe.Language.RealizedProgram.Reader
public import GordieHoweNative.Language.RealizedProgram.CellsReader

/-!
# GordieHowe: the compiled cells checks

Compiled code runs the cells checks (`placementB`, `chalValuesB`) at a context built once
(`placementBC`, `chalValuesBC`, `GordieHoweNative/Language/RealizedProgram/CellsReader.lean`), by their `@[csimp]` theorems here:

* **the product cells by lists** (`Shape.cells_eq_cellsL`): a shape's product cells, the distinct
  sub-multisets of at least two factors of its monomials, are the distinct sorted sublists of at
  least two factors of its monomials' sorted factors;
* **the kernel checkers are their generic forms at the kernel's reader** (`placementB_eq_reader`,
  `chalValuesB_eq_reader`), by definition but for the product cells;
* **the context's reader is the kernel's** (`CellsReader.ofCtx_build`): its program reader's
  (`PReader.ofCtx_build`), and its tables the kernel's, computed once.
-/

public section

namespace GordieHowe.RealizedProgram

/-! ## The product cells by lists -/

theorem mem_subListsN {s : List ℕ} : ∀ {l : List ℕ}, s ∈ subListsN l ↔ s.Sublist l
  | [] => by simp [subListsN]
  | a :: l => by
    rw [subListsN, List.mem_append, List.mem_map, List.sublist_cons_iff, mem_subListsN]
    refine or_congr Iff.rfl ⟨fun ⟨r, hr, he⟩ => ⟨r, he.symm, mem_subListsN.1 hr⟩, ?_⟩
    rintro ⟨r, rfl, hr⟩
    exact ⟨r, mem_subListsN.2 hr, rfl⟩

theorem nodup_insertAll {α : Type} [DecidableEq α] :
    ∀ {acc : List α} (l : List α), acc.Nodup → (insertAll acc l).Nodup
  | _, [], h => h
  | _, _ :: xs, h => nodup_insertAll xs h.insert

/-- **A shape's product cells by lists**: the distinct sorted sublists of at least two factors of
its monomials' sorted factors, as many as the distinct sub-multisets (`Shape.cellSet`). -/
theorem Shape.cells_eq_cellsL : Shape.cells = Shape.cellsL := by
  funext sh
  classical
  set F := sh.monos.flatMap fun c =>
    (subListsN (c.2.mergeSort (· ≤ ·))).filter fun s => decide (2 ≤ s.length) with hF
  have hsorted : ∀ s ∈ F, s.Pairwise (· ≤ ·) := by
    intro s hs
    simp only [hF, List.mem_flatMap, List.mem_filter, mem_subListsN] at hs
    obtain ⟨c, _, hsub, _⟩ := hs
    have := List.pairwise_mergeSort (le := fun a b : ℕ => decide (a ≤ b))
      (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) c.2
    exact (this.sublist hsub).imp fun h => by simpa using h
  have hinj : ∀ s ∈ insertAll [] F, ∀ t ∈ insertAll [] F,
      Multiset.ofList s = Multiset.ofList t → s = t := by
    intro s hs t ht he
    rw [mem_insertAll] at hs ht
    simp only [List.not_mem_nil, false_or] at hs ht
    exact List.Perm.eq_of_pairwise (fun a b _ _ hab hba => Nat.le_antisymm hab hba)
      (hsorted s hs) (hsorted t ht) (Multiset.coe_eq_coe.1 he)
  have hset : sh.cellSet = ((insertAll [] F).map Multiset.ofList).toFinset := by
    ext M
    simp only [Shape.cellSet, Finset.mem_biUnion, List.mem_toFinset, Finset.mem_filter,
      Multiset.mem_toFinset, Multiset.mem_powerset, List.mem_map, mem_insertAll,
      List.not_mem_nil, false_or, hF, List.mem_flatMap, List.mem_filter, mem_subListsN,
      decide_eq_true_eq]
    have hp : ∀ l : List ℕ, Multiset.ofList (l.mergeSort (· ≤ ·)) = Multiset.ofList l :=
      fun l => Multiset.coe_eq_coe.2 (List.mergeSort_perm l _)
    constructor
    · rintro ⟨c, hc, hle, h2⟩
      induction M using Quotient.inductionOn with
      | h m =>
        have hsp : m.Subperm (c.2.mergeSort (· ≤ ·)) := by
          rw [← Multiset.coe_le, hp]
          exact hle
        obtain ⟨s, hsm, hs⟩ := hsp
        refine ⟨s, ⟨c, hc, hs, ?_⟩, Multiset.coe_eq_coe.2 hsm⟩
        rw [hsm.length_eq]
        exact h2
    · rintro ⟨s, ⟨c, hc, hs, h2⟩, rfl⟩
      refine ⟨c, hc, ?_, by simpa using h2⟩
      exact (hp c.2) ▸ Multiset.coe_le.2 hs.subperm
  rw [Shape.cells, Shape.cellsL, hset, List.toFinset_card_of_nodup
    ((nodup_insertAll F List.nodup_nil).map_on hinj), List.length_map]

/-! ## The kernel checkers at the kernel's reader -/

section

variable (ir : RealizedProgram)

theorem atomSum_eq_atomSumN (lf : ℕ → Bool) (nd : ℕ → ℕ) (e : Expr) :
    ir.atomSum lf nd e = ir.atomSumN ir.exprs.length lf nd e := rfl

/-- **`bpolySum` is its form at the expressions' lengths and summaries.** -/
theorem bpolySumW_eq (lf : ℕ → Bool) (nd : ℕ → ℕ) (rs : ℕ → AtomSum) :
    ∀ e : Expr, bpolySumW ir.exprLen (ir.atomSum lf nd) rs e = ir.bpolySum lf nd rs e
  | .add a b => by rw [bpolySumW, bpolySum, bpolySumW_eq lf nd rs a, bpolySumW_eq lf nd rs b]
  | .sub a b => by rw [bpolySumW, bpolySum, bpolySumW_eq lf nd rs a, bpolySumW_eq lf nd rs b]
  | .scale (.const c) a => by rw [bpolySumW, bpolySum, bpolySumW_eq lf nd rs a]
  | .mul a b => by rw [bpolySumW, bpolySum, bpolySumW_eq lf nd rs a, bpolySumW_eq lf nd rs b]
  | .reindex idx a => by rw [bpolySumW, bpolySum, bpolySumW_eq lf nd rs a]
  | .concat a b => by rw [bpolySumW, bpolySum, bpolySumW_eq lf nd rs a, bpolySumW_eq lf nd rs b]
  | .ref k => by rw [bpolySumW, bpolySum]
  | .leaf _ | .scale (.node _ _) _ | .linear _ _ | .prod _ _ | .mux _ _ _ | .apply _ _
  | .logic _ _ _ => rfl

local notation "R" => CellsReader.ofProgram ir

theorem formsOf_eq_reader (d b : ℕ) : ir.formsOf d b = @CellsReader.formsOf ir (R) d b := by
  rw [formsOf, CellsReader.formsOf]
  cases (ir.batch b).operands <;> funext e <;> exact congrArg Prod.snd (bpolySumW_eq ir _ _ _ e).symm

theorem batchOkB_eq_reader (d b : ℕ) :
    ir.batchOkB d b = @CellsReader.batchOkB ir (CellsReader.ofProgram ir) d b := by
  rw [batchOkB, CellsReader.batchOkB, CellsReader.batchOkWith, Shape.cells_eq_cellsL, formsOf_eq_reader]
  rfl

theorem batchesE_eq_reader : ir.batchesE = @CellsReader.batchesE ir (CellsReader.ofProgram ir) := by
  rw [batchesE, CellsReader.batchesE, CellsReader.batchesWith]
  simp only [batchOkB_eq_reader, CellsReader.batchOkB]

theorem typesE_eq_reader : ir.typesE = @CellsReader.typesE ir (R) := rfl
theorem rowValueOk_eq_reader (v : ℕ) : ir.rowValueOk v = @CellsReader.rowValueOk ir (R) v := rfl
theorem rowExprOk_eq_reader (e : Expr) : ir.rowExprOk e = @CellsReader.rowExprOk ir (R) e := rfl
theorem viewExprOk_eq_reader (d : ℕ) (e : Expr) :
    ir.viewExprOk d e = @CellsReader.viewExprOk ir (R) d e := rfl
theorem isQuad_eq_reader (d p : ℕ) : ir.isQuad d p = @CellsReader.isQuad (R) d p := rfl
theorem routeOkE_eq_reader (pid : ℕ) (pr : Predicate) (rt : Route) :
    ir.routeOkE pid pr rt = @CellsReader.routeOkE ir (R) pid pr rt := rfl
theorem routesE_eq_reader (S : Structure) : ir.routesE S = @CellsReader.routesE ir (R) S := rfl

theorem placementB_eq_reader (S : Structure) :
    ir.placementB S = @CellsReader.placementB ir (CellsReader.ofProgram ir) S := by
  rw [placementB, placementE, batchesE_eq_reader, CellsReader.placementB, CellsReader.placementE]
  rfl

theorem chalValuesB_eq_reader (S : Structure) :
    ir.chalValuesB S = @CellsReader.chalValuesB ir (PReader.ofProgram ir) S := rfl

end

/-! ## The context's reader -/

theorem getElem?_map_range_toArray {α : Type} (f : ℕ → α) (n d : ℕ) :
    ((List.range n).toArray.map f)[d]? = if d < n then some (f d) else none := by
  split_ifs with h <;> simp [h]

/-- **The compiled cells checks' reader of the program's context is the kernel's.** -/
theorem CellsReader.ofCtx_build (ir : RealizedProgram) :
    CellsReader.ofCtx ir (CellsCtx.build ir) = CellsReader.ofProgram ir := by
  rw [CellsReader.ofCtx, CellsCtx.build, CellsReader.ofProgram, PReader.ofCtx_build]
  congr 1
  · funext d v
    rw [getElem?_map_range_toArray]
    by_cases h : d < ir.domains.length
    · simp only [h, ↓reduceIte]
      rfl
    · simp only [h, ↓reduceIte]
  · funext d k
    rw [getElem?_map_range_toArray]
    by_cases h : d < ir.domains.length
    · simp only [h, ↓reduceIte]
      rfl
    · simp only [h, ↓reduceIte]
  · funext d e
    rw [getElem?_map_range_toArray]
    by_cases h : d < ir.domains.length
    · simp only [h, ↓reduceIte]
      rfl
    · simp only [h, ↓reduceIte]

/-! ## The compiled checks -/

/-- **Compiled code runs the cells checks at the context built once** (`placementBC`). -/
@[csimp] theorem placementB_csimp : @placementB = @placementBC := by
  funext ir S
  rw [placementB_eq_reader, placementBC]
  show _ = @CellsReader.placementB ir (CellsReader.ofCtx ir (CellsCtx.build ir)) S
  rw [CellsReader.ofCtx_build]

/-- **Compiled code runs the challenge values' check at the program context built once**
(`chalValuesBC`). -/
@[csimp] theorem chalValuesB_csimp : @chalValuesB = @chalValuesBC := by
  funext ir S
  rw [chalValuesB_eq_reader, chalValuesBC]
  show _ = @CellsReader.chalValuesB ir (PReader.ofCtx (PCtx.build ir)) S
  rw [PReader.ofCtx_build]

end GordieHowe.RealizedProgram
