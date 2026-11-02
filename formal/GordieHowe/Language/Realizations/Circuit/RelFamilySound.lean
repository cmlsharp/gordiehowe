-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Circuit.RelSound
public import GordieHowe.Language.Realizations.Circuit.RelEntry
public import GordieHowe.Language.Realizations.RealizeMac

@[expose] public section

/-!
# GordieHowe: what an accepted family record enforces

* **A fraction tree** (`GordieHowe.GKR.Rel.FracTree.root_eq_fold`): where the tree is well formed
  and its inner nodes' cuts hold, the root's numerator and denominator are the left fold of its
  leaves' denominators (`FractionTree.fold`), whatever the tree's shape.
* **A range LogUp** (`GordieHowe.RealizedProgram.logupAt_of_logupB`): an accepted entry gives the
  group's LogUp identity (`LogupHoldsAt`) at the `α` the circuit reads, where the weights' inputs
  are `(α − j)⁻¹`. The identity is deterministic; the chance of a bad `α` is charged by
  `needlesIn_or_logupBad`.
* **A MAC H half** (`GordieHowe.RealizedProgram.macHHolds_of_macHB`): an accepted entry gives the
  H half of the cross-field `equal` (`MacHHolds`) at a reader.
* **An entry's family** (`GordieHowe.RealizedProgram.entryHolds_of_famHead`): an alignment, LogUp
  or MAC H entry whose head and family cuts are accepted holds.
-/

namespace GordieHowe.GKR.Rel

open GordieHowe.RealizedProgram (Trie teW teW_eval Trie.get_ofList)

/-- **The leaves `[lo, hi)`** of a list. -/
def spanSlice {α : Type*} (ds : List α) (lo hi : ℕ) : List α := (ds.drop lo).take (hi - lo)

theorem spanSlice_append {α : Type*} (ds : List α) {lo mid hi : ℕ} (h1 : lo ≤ mid)
    (h2 : mid ≤ hi) : spanSlice ds lo hi = spanSlice ds lo mid ++ spanSlice ds mid hi := by
  unfold spanSlice
  rw [show hi - lo = (mid - lo) + (hi - mid) by omega, List.take_add, List.drop_drop,
    show lo + (mid - lo) = mid by omega]

theorem spanSlice_succ {α : Type*} (ds : List α) {i : ℕ} (h : i < ds.length) :
    spanSlice ds i (i + 1) = [ds[i]] := by
  unfold spanSlice
  rw [show i + 1 - i = 0 + 1 by omega, List.drop_eq_getElem_cons h,
    List.take_succ_cons, List.take_zero]

theorem FracTree.fracs_get_leaf (tr : FracTree) {i : ℕ} (h : i < tr.dens.length) :
    tr.fracs.get i = (none, tr.dens[i]) := by
  rw [FracTree.fracs, Trie.get_ofList _ (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega),
    List.getElem_append_left (by simp; omega)]
  simp

theorem FracTree.fracs_get_inner (tr : FracTree) {i : ℕ} (h : tr.dens.length ≤ i)
    (h' : i < tr.dens.length + tr.inner.length) :
    tr.fracs.get i = (some tr.inner[i - tr.dens.length].num, tr.inner[i - tr.dens.length].den) := by
  rw [FracTree.fracs, Trie.get_ofList _ (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega),
    List.getElem_append_right (by simp; omega)]
  simp

/-- **The numerator of fraction `a`**: one for a leaf. -/
def fracNumV {F : Type*} [CommRing F] (κc V : ℕ → F) (Fr : Trie (Option Wire × Wire)) (a : ℕ) : F :=
  ((Fr.get a).1.map (·.val κc V)).getD 1

theorem fracTerm_eval {F : Type*} [CommRing F] (κc V : ℕ → F) (Fr : Trie (Option Wire × Wire))
    (a b : ℕ) : (fracTerm Fr a b).eval κc V = fracNumV κc V Fr a * (Fr.get b).2.val κc V := by
  unfold fracTerm fracNumV
  cases (Fr.get a).1 <;> simp [TE.eval, teW_eval]

/-- **Every fraction spans a run of leaves** whose fold is its value. -/
theorem FracTree.span_fold {F : Type*} [CommRing F] {κc V : ℕ → F} {tr : FracTree}
    (hall : ∀ k (hk : k < tr.inner.length),
      fracNodeOkB (Trie.ofList tr.inner) tr.dens.length tr.inner[k] k = true)
    (hc : ∀ q ∈ tr.cuts, q.1.val κc V = q.2.eval κc V) :
    ∀ i < tr.dens.length + tr.inner.length, ∃ lo hi, lo < hi ∧ hi ≤ tr.dens.length ∧
      (∀ f, i < f → fracLo (Trie.ofList tr.inner) tr.dens.length f i = lo ∧
        fracHi (Trie.ofList tr.inner) tr.dens.length f i = hi) ∧
      (fracNumV κc V tr.fracs i, (tr.fracs.get i).2.val κc V) =
        FractionTree.fold (spanSlice (tr.dens.map (·.val κc V)) lo hi) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro hi
  by_cases hin : i < tr.dens.length
  · refine ⟨i, i + 1, by omega, by omega, fun f hf => ?_, ?_⟩
    · obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      simp [fracLo, fracHi, hin]
    · rw [spanSlice_succ _ (by simpa using hin)]
      simp [fracNumV, FracTree.fracs_get_leaf tr hin]
  · have hk : i - tr.dens.length < tr.inner.length := by omega
    have hn := hall _ hk
    generalize hfr : tr.inner[i - tr.dens.length] = fr at hn
    simp only [fracNodeOkB, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq,
      show tr.dens.length + (i - tr.dens.length) = i by omega] at hn
    obtain ⟨⟨hl, hr⟩, hmid⟩ := hn
    obtain ⟨lol, hil, h1l, h2l, hfl, hvl⟩ := ih fr.l hl (by omega)
    obtain ⟨lor, hir, h1r, h2r, hfr', hvr⟩ := ih fr.r hr (by omega)
    rw [(hfl i hl).2, (hfr' i hr).1] at hmid
    have hT : (Trie.ofList tr.inner).get (i - tr.dens.length) = fr := by
      rw [Trie.get_ofList _ hk, List.getD_eq_getElem _ _ hk, hfr]
    refine ⟨lol, hir, by omega, h2r, fun f hf => ?_, ?_⟩
    · obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      have hb : Nat.blt i tr.dens.length = false := by
        cases hb' : Nat.blt i tr.dens.length
        · rfl
        · exact absurd (by simpa [Nat.blt_eq] using hb') hin
      simp only [fracLo, fracHi, hb, Bool.cond_false, hT]
      exact ⟨(hfl f (by omega)).1, (hfr' f (by omega)).2⟩
    · have hmem : fr ∈ tr.inner := hfr ▸ List.getElem_mem hk
      have hcn := hc (fr.num, _) (List.mem_flatMap.2 ⟨fr, hmem, List.mem_cons_self⟩)
      have hcd := hc (fr.den, _) (List.mem_flatMap.2 ⟨fr, hmem,
        List.mem_cons_of_mem _ List.mem_cons_self⟩)
      simp only [TE.eval, fracTerm_eval, teW_eval] at hcn hcd
      rw [spanSlice_append _ (le_of_lt h1l) (hmid ▸ le_of_lt h1r), FractionTree.fold_append,
        ← hvl, hmid, ← hvr]
      have hg := FracTree.fracs_get_inner tr (by omega) hi
      rw [hfr] at hg
      simp only [fracNumV, hg, Option.map_some, Option.getD_some, FractionTree.combine]
      rw [hcn, hcd]
      simp only [fracNumV]

/-- **A well-formed fraction tree's root is the left fold of its leaves**: where every inner node's
cuts hold at `V`. -/
theorem FracTree.root_eq_fold {F : Type*} [CommRing F] {κc V : ℕ → F} {tr : FracTree}
    (h1 : κc 1 = 1) (h : tr.okB = true) (hc : ∀ q ∈ tr.cuts, q.1.val κc V = q.2.eval κc V) :
    (tr.rootTE.1.eval κc V, tr.rootTE.2.eval κc V) =
      FractionTree.fold (tr.dens.map (·.val κc V)) := by
  simp only [FracTree.okB, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hn, hall⟩, hlo⟩, hhi⟩ := h
  have hall' : ∀ k (hk : k < tr.inner.length),
      fracNodeOkB (Trie.ofList tr.inner) tr.dens.length tr.inner[k] k = true := fun k hk => by
    have := hall (tr.inner.zipIdx[k]'(by simpa using hk)) (List.getElem_mem _)
    simpa [List.getElem_zipIdx] using this
  obtain ⟨lo, hi, -, -, hf, hv⟩ := FracTree.span_fold hall' hc _ (by omega : tr.dens.length +
    tr.inner.length - 1 < tr.dens.length + tr.inner.length)
  obtain ⟨rfl, rfl⟩ := hf (tr.dens.length + tr.inner.length) (by omega)
  rw [hlo, hhi] at hv
  have hs : spanSlice (tr.dens.map (·.val κc V)) 0 tr.dens.length = tr.dens.map (·.val κc V) := by
    simp [spanSlice]
  rw [hs] at hv
  rw [← hv]
  unfold FracTree.rootTE fracNumV
  cases hx : (tr.fracs.get (tr.dens.length + tr.inner.length - 1)).1 <;>
    simp [hx, TE.eval, teW_eval, h1]

end GordieHowe.GKR.Rel

namespace GordieHowe.RealizedProgram

open GordieHowe.GKR.Certificate GordieHowe.GKR.Fold GordieHowe.Twin GordieHowe.Range
open GordieHowe.GKR.Rel (Wire TE EntryCert Assert Frac FracTree LogupCert MacHCert FamCert relOkE)

/-- **The field of circuit `c` meets its certificate's codes**: the code arithmetic `ar` is the
field's, the field has characteristic `chr > 0`, and every code below `chr` decodes to its cast. -/
structure CircuitFieldOk (ir : RealizedProgram) (I : Interp) (c : ℕ) (ar : CodeArith) (chr : ℕ) :
    Prop where
  /-- The code arithmetic is the field's. -/
  hom : ar.Hom (I (ir.circField c)).decode
  /-- The characteristic. -/
  charP : CharP (I (ir.circField c)).K chr
  /-- The characteristic is positive. -/
  pos : 0 < chr
  /-- A code below the characteristic decodes to its cast. -/
  dec : ∀ k < chr, (I (ir.circField c)).decode k = (k : (I (ir.circField c)).K)

variable {ir : RealizedProgram} {I : Interp} {primeNodes : ℕ → List String} {c : ℕ}
  {ar : CodeArith} {cd : CircuitData}

/-- **The verifier's input at a weights position** is the weight `(α − j)⁻¹`, `α` the run's
challenge of the table. -/
theorem publicInput_weights {x : ir.Valuation I} {r : (ir.layout I).Run}
    (hL : ir.InputLayoutOk c) {b t a n j : ℕ}
    (hb : (ir.circuit c).inputs[b]? = some (InputBlock.realizationPub (.weights t) a n))
    (hj : j < n) :
    ir.publicInput I c x r (a + j) =
      ((castElt (ir.chalRead I r.chal (ir.table t).alpha 0) : (I (ir.circField c)).K) - j)⁻¹ := by
  have hmem := List.mem_of_getElem? hb
  have h1 := InputBlock.layoutEnd_first_le hL.layout _ hmem
  simp only [InputBlock.first] at h1
  have hy := InputBlock.findSome_pubValue? (pv := fun u i =>
      (castElt (ir.reader (ir.layoutEnv I x ⟨0, 0⟩ r) u i) : (I (ir.circField c)).K))
    (rp := ir.realPubValue I c r) (j := a + j) hL.layout _ hmem
    (by simp only [InputBlock.pubValue?, show a ≤ a + j ∧ a + j < a + n by omega,
      Nat.add_sub_cancel_left]; rfl)
  simp only [publicInput, show a + j ≠ 0 by omega, ite_false, hy, Option.getD_some]
  rfl

/-- **A cut node printed as `e` carries `e`'s coordinates** on its wires. -/
theorem wire_val_of_eqB (hM : ir.DerivModel I primeNodes) {env : TEnv} {E : ETable}
    (hE : ir.EmitTableOk env E) {rd : ir.Valuation I} {V : ℕ → (I (ir.circField c)).K}
    (hT : ∀ m < E.size, (E.get m).cut = true → ir.WiresOk c env E rd V m)
    {k : ℕ} {e : Expr} (hk : k < E.size) (hc : (E.get k).cut = true)
    (he : E.eqB env k e = true) {i : ℕ} (hi : i < (E.get k).len) :
    (wireAt E k i).val (I (ir.circField c)).decode V = ir.evalE rd (ir.circField c) e i := by
  rw [wireAt, (hT k hk hc).2 i hi, ← (eqB_sound hM.wf.refsOrdered hE rd _ he).2]
  rfl


/-- **Lists agreeing pairwise map alike**: equal lengths and `f a = g b` along the zip. -/
theorem map_eq_map_of_zip {α β γ : Type*} {f : α → γ} {g : β → γ} :
    ∀ {l₁ : List α} {l₂ : List β}, l₁.length = l₂.length →
      (∀ p ∈ l₁.zip l₂, f p.1 = g p.2) → l₁.map f = l₂.map g
  | [], [], _, _ => rfl
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl
  | a :: l₁, b :: l₂, hl, h => by
    simp only [List.zip_cons_cons, List.mem_cons, forall_eq_or_imp] at h
    simp only [List.map_cons, h.1, map_eq_map_of_zip (by simpa using hl) h.2]

/-- **The sum over a `flatMap`** is the sum of the blocks' sums. -/
theorem sum_map_flatMap {α β M : Type*} [AddCommMonoid M] (f : α → List β) (e : β → M) :
    ∀ l : List α, ((l.flatMap f).map e).sum = (l.map fun x => ((f x).map e).sum).sum
  | [] => by simp
  | x :: l => by simp [List.flatMap_cons, List.sum_append, sum_map_flatMap f e l]

/-- **A histogram's weighted sum over `[0, T)`** is the sum over its value's coordinates, its size
at most `T`. -/
theorem sum_histRead_some {rd : ir.Valuation I} {f T u : ℕ} (hle : (ir.value u).size ≤ T)
    (w : ℕ → (I f).K) :
    ∑ j : Fin T, ir.histRead rd f T (some u) j * w j =
      ((List.range (ir.value u).size).map fun j => castElt (rd u j) * w j).sum := by
  simp only [histRead]
  rw [Fin.sum_univ_eq_sum_range (fun j => (if j < (ir.value u).size then
    (castElt (rd u j) : (I f).K) else 0) * w j) T, ← Nat.add_sub_cancel' hle,
    Finset.sum_range_add]
  simp only [show ∀ x, ¬ ((ir.value u).size + x < (ir.value u).size) from fun x => by omega,
    ite_false, zero_mul, Finset.sum_const_zero, add_zero, ← sum_map_range]
  exact congrArg List.sum (List.map_congr_left fun x hx => by simp [List.mem_range.1 hx])

/-- **The needle wires read the group's needles**: each named node, a cut node printed as its
member's needle expression and long enough, carries the member's coordinates. -/
theorem needleCoords_vals (hM : ir.DerivModel I primeNodes) {env : TEnv} {E : ETable}
    (hE : ir.EmitTableOk env E) {rd : ir.Valuation I} {V : ℕ → (I (ir.circField c)).K}
    (hT : ∀ m < E.size, (E.get m).cut = true → ir.WiresOk c env E rd V m) :
    ∀ {ms : List Member} {ys : List ℕ}, ys.length = ms.length →
      (∀ p ∈ ms.zip ys, p.2 < E.size ∧ (E.get p.2).cut = true ∧
        E.eqB env p.2 (ir.needleExpr (Member.pred p.1) (Member.needle p.1)) = true ∧
        Member.first p.1 + Member.count p.1 ≤ (E.get p.2).len) →
      (needleCoords ms ys).map (fun q => (wireAt E q.1 q.2).val (I (ir.circField c)).decode V) =
        ms.flatMap (ir.memberVals rd (ir.circField c))
  | [], [], _, _ => rfl
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl
  | m :: ms, y :: ys, hl, h => by
    simp only [List.zip_cons_cons, List.mem_cons, forall_eq_or_imp] at h
    obtain ⟨⟨hy, hcut, heq, hlen⟩, h⟩ := h
    have ih := needleCoords_vals hM hE hT (ms := ms) (ys := ys) (by simpa using hl) h
    simp only [needleCoords] at ih ⊢
    simp only [List.zip_cons_cons, List.flatMap_cons, List.map_append, ih, List.map_map,
      memberVals]
    congr 1
    refine List.map_congr_left fun j hj => ?_
    simp only [Function.comp_apply]
    exact wire_val_of_eqB hM hE hT hy hcut heq (by have := List.mem_range.1 hj; omega)

/-- **An accepted range LogUp entry gives the group's LogUp identity** at the reading `rd`: where
the DAG holds at the inputs `val`, the cut nodes carry their meanings at `rd`, every challenge
value of `α`'s challenge reads `α`, and the weights' inputs are `(α − j)⁻¹`. -/
theorem logupAt_of_logupB (hM : ir.DerivModel I primeNodes)
    (hC : ir.CircuitFieldOk I c ar cd.chr) (hE : ir.EmitTableOk (cd.env ar) cd.table)
    (hAr : (cd.env ar).ArithOk (I (ir.circField c)).decode) (hcf : ir.chalFieldsB = true)
    {rd : ir.Valuation I} {val : ℕ → (I (ir.circField c)).K} {α : (I (ir.circField c)).K}
    {k t g : ℕ} {lc : LogupCert} {as : List Assert}
    (hone : cd.dag.val cd.w (cd.consts.decode (I (ir.circField c)).decode) val 0 = 1)
    (hD : cd.dag.Holds cd.w (cd.consts.decode (I (ir.circField c)).decode) val)
    (hT : ∀ m < cd.table.size, (cd.table.get m).cut = true →
      ir.WiresOk c (cd.env ar) cd.table rd
        (cd.dag.val cd.w (cd.consts.decode (I (ir.circField c)).decode) val) m)
    (hα : ∀ u < ir.values.length, (ir.value u).kind = .challenge (ir.alphaOf t) →
      ir.valueField u = ir.circField c → castElt (rd u 0) = α)
    (hw : ∀ b a T' : ℕ,
      (ir.circuit c).inputs[b]? = some (InputBlock.realizationPub (.weights t) a T') →
      1 ≤ a → a + T' ≤ (ir.circuit c).publicInputs → ∀ j < T',
        cd.dag.val cd.w (cd.consts.decode (I (ir.circField c)).decode) val (a + j) =
        (α - j)⁻¹)
    (h : ir.logupB c ar cd k t g lc as = true) :
    ir.LogupHoldsAt rd t g := by
  simp only [logupB, logupE, okB_seqE, okB_mapE, Bool.and_eq_true,
    ← GordieHowe.GKR.Rel.relOk_eq_okB] at h
  obtain ⟨hg, hcuts, hitem⟩ := h
  have hc := (GordieHowe.GKR.Rel.relOk_sound hC.hom hone hD hcuts).1
  have hi := (GordieHowe.GKR.Rel.relOk_sound hC.hom hone hD hitem).2 _ (List.mem_singleton_self _)
  simp only [logupGuardE, okB_seqE, okB_guardE, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq,
    Nat.ble_eq, List.all_eq_true] at hg
  obtain ⟨⟨⟨⟨ht, hgc⟩, hrr⟩, hcf'⟩, hal, ⟨hnl, hnd⟩, ⟨hhl, hhd⟩, hwt, ⟨hdl, htr⟩, has⟩ := hg
  set V := cd.dag.val cd.w (cd.consts.decode (I (ir.circField c)).decode) val with hV
  set κ := (I (ir.circField c)).decode with hκ
  have h0 : κ 0 = 0 := hC.hom.zero
  have hn1 : κ cd.neg1 = -1 := hAr.neg1
  have h1 : κ 1 = 1 := hC.hom.one
  have hαw : (wireAt cd.table lc.alpha 0).val κ V = α := by
    obtain ⟨⟨⟨hak, hacut⟩, halen⟩, hm⟩ := hal
    split at hm
    · rename_i u _ _
      simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hm
      obtain ⟨⟨⟨hu, hf⟩, heq⟩, hk⟩ := hm
      rw [wire_val_of_eqB hM hE hT hak hacut heq halen, evalE_leaf]
      refine hα u hu ?_ hf
      split at hk
      · rename_i j hj
        rw [hj, Nat.eq_of_beq_eq_true hk]
      · cases hk
    · cases hm
  have hN := needleCoords_vals hM hE hT hnl (fun p hp => by
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hnd p hp
    exact ⟨h1, h2, h3, h4⟩)
  have hleaf : lc.tree.dens.map (·.val κ V) =
      (ir.groupNeedles rd (ir.circField c) t g).map (α - ·) := by
    rw [groupNeedles, ← hN, List.map_map]
    refine map_eq_map_of_zip ?_ fun p hp => ?_
    · rw [hdl, ← length_groupNeedles rd (ir.circField c) t g, groupNeedles, ← hN, List.length_map]
    · have := hc _ (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl
        (List.mem_map.2 ⟨p, hp, rfl⟩)))))
      rw [this]
      show TE.eval κ V (teW _) + κ cd.neg1 * TE.eval κ V (teW _) = _
      rw [teW_eval, teW_eval, hαw, hn1, Function.comp_apply]
      ring
  have hroot := GKR.Rel.FracTree.root_eq_fold (κc := κ) (V := V) hC.hom.one htr
    (fun q hq => hc q (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hq)))))
  rw [hleaf, ← FractionTree.balanced_eq_fold] at hroot
  obtain ⟨hwb, hwm⟩ := hwt
  split at hwm
  · rename_i t' a n hblk
    simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at hwm
    obtain ⟨⟨⟨rfl, rfl⟩, ha⟩, hapub⟩ := hwm
    have hbi : (ir.circuit c).inputs[lc.weights]? =
        some (InputBlock.realizationPub (.weights t') a (ir.tableSize t')) := by
      rw [List.getD_eq_getElem _ _ hwb] at hblk
      rw [List.getElem?_eq_getElem hwb, hblk]
    have hwV := hw _ a _ hbi ha hapub
    have hsum : lc.sum.val κ V =
        ∑ j, ir.staticHist rd (ir.circField c) t' g j * logupTcoef (ir.tableSize t') α j +
          ∑ j, ir.lateHist rd (ir.circField c) t' g j * logupTcoef (ir.tableSize t') α j := by
      have := hc _ (List.mem_append.2 (Or.inr (List.mem_singleton_self _)))
      rw [this, sumL_eval h0, sum_map_flatMap]
      have hmap : (ir.histVals t' g).map (fun u => ∑ j : Fin (ir.tableSize t'),
          ir.histRead rd (ir.circField c) (ir.tableSize t') (some u) j *
            logupTcoef (ir.tableSize t') α j) =
          lc.hists.map (fun h => ((List.range (cd.table.get h).len).map fun j =>
            TE.eval κ V (TE.mul (teW (wireAt cd.table h j))
              (.wire 0 1 (((ir.circuit c).inputs.getD lc.weights default).first + j)))).sum) := by
        refine map_eq_map_of_zip hhl.symm fun p hp => ?_
        obtain ⟨⟨⟨⟨⟨hu, hk⟩, hcut⟩, heq⟩, hlen⟩, hle⟩ := hhd p hp
        refine (sum_histRead_some (w := fun j => (α - (j : (I (ir.circField c)).K))⁻¹) hle).trans ?_
        rw [← hlen]
        refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
        have hj := List.mem_range.1 hj
        show _ = (wireAt cd.table p.2 j).val κ V * (κ 0 + κ 1 * V _)
        rw [wire_val_of_eqB hM hE hT hk hcut heq hj, evalE_leaf, h0, h1, zero_add, one_mul,
          hblk, InputBlock.first, hwV j (by omega)]
      simp only [List.map_map, Function.comp_def]
      rw [← hmap]
      unfold histVals staticHist lateHist
      rcases (ir.groupOf t' g).staticMult with _ | u <;>
        rcases (ir.groupOf t' g).lateMult with _ | u' <;> simp [histRead]
    have hcore : rangeArgument le_rfl (ir.groupNeedles rd (ir.circField c) t' g)
        (logupTcoef (ir.tableSize t') α) (ir.staticHist rd (ir.circField c) t' g)
        (ir.lateHist rd (ir.circField c) t' g) α = true := by
      rw [rangeArgument_eq_true_iff, fracTree, ← hroot]
      simp only [show ∀ j : Fin (ir.tableSize t'), Fin.castLE le_rfl j = j from fun _ => rfl]
      rw [← hsum]
      simp only [logupItem, TE.eval, teW_eval, hn1] at hi
      linear_combination hi
    unfold LogupHoldsAt
    rcases hv : ir.chalNode (ir.alphaOf t') with _ | v
    · trivial
    have hp := List.find?_some hv
    have hvl : v < ir.values.length := List.mem_range.1 (List.mem_of_find?_eq_some hv)
    have hk : (ir.value v).kind = .challenge (ir.alphaOf t') := by
      revert hp
      cases (ir.value v).kind <;> simp
    have hvf : ir.valueField v = ir.chalField (ir.alphaOf t') := by
      have h := List.all_eq_true.1 hcf v (List.mem_range.2 hvl)
      simp only [hk] at h
      exact Nat.eq_of_beq_eq_true h
    have hαv := hα v hvl hk (hvf.trans hcf')
    obtain ⟨T', hrows⟩ : ∃ T', (ir.table t').rows = .range T' := by
      unfold rangeRowsB at hrr
      split at hrr
      · exact ⟨_, ‹_›⟩
      · cases hrr
    unfold logupAt
    simp only [hrows]
    generalize ir.chalField (ir.alphaOf t') = f at hcf' ⊢
    subst hcf'
    rw [hαv]
    exact hcore
  · cases hwm

/-- **A list sum over `range n` is a sum over `Fin n`.** -/
theorem sum_range_map_eq_sum_fin {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∀ n, ((List.range n).map f).sum = ∑ i : Fin n, f i
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_range_map_eq_sum_fin f n,
      Fin.sum_univ_castSucc]
    simp

/-- **A list sum over `zipIdx` is a sum over the indices.** -/
theorem sum_map_zipIdx {α M : Type*} [Inhabited α] [AddCommMonoid M] (f : α × ℕ → M) :
    ∀ (l : List α) (n : ℕ), ((l.zipIdx n).map f).sum =
      ((List.range l.length).map fun i => f (l.getD i default, n + i)).sum
  | [], _ => by simp
  | a :: l, n => by
    rw [List.zipIdx_cons, List.map_cons, List.sum_cons, sum_map_zipIdx f l (n + 1),
      List.length_cons, List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
    simp only [List.getD_cons_zero, add_zero, Function.comp_def, List.getD_cons_succ]
    congr 2
    refine List.map_congr_left fun i _ => ?_
    rw [Nat.add_assoc, Nat.add_comm 1 i]

/-- **Element `i` of a list is its pair in `zipIdx`.** -/
theorem getD_mem_zipIdx {α : Type*} [Inhabited α] {l : List α} {i : ℕ} (hi : i < l.length) :
    (l.getD i default, i) ∈ l.zipIdx := by
  rw [List.mem_iff_getElem]
  refine ⟨i, by simpa using hi, ?_⟩
  rw [List.getElem_zipIdx, List.getD_eq_getElem _ _ hi, Nat.zero_add]

/-- **Casting through an equal field identifier** is casting directly. -/
theorem castElt_eq_castElt_of_eq {a b b' : ℕ} (h : b = b') (x : (I a).K) :
    (castElt x : (I b').K) = castElt (castElt x : (I b).K) := by
  subst h
  simp

/-- **The key of a powers value has a value holding it** (`powersB`), of the key's field
(`chalFieldsB`). -/
theorem chalNode_of_powersB (hcf : ir.chalFieldsB = true) {r key nch f : ℕ}
    (h : ir.powersB r key nch f = true) :
    ∃ v, ir.chalNode key = some v ∧ ir.valueField v = ir.chalField key := by
  unfold powersB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨-, h⟩ := h
  split at h
  · rename_i n idx kv one _
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨-, -⟩, hkv⟩, -⟩, -⟩, hk⟩, -⟩ := h
    have hs : (ir.chalNode key).isSome = true := by
      unfold chalNode
      rw [List.find?_isSome]
      refine ⟨kv, List.mem_range.2 hkv, ?_⟩
      split at hk
      · rename_i j hj
        rw [hj]
        exact hk
      · cases hk
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hs
    refine ⟨v, hv, ?_⟩
    have hp := List.find?_some hv
    have hvl : v < ir.values.length := List.mem_range.1 (List.mem_of_find?_eq_some hv)
    have hcfv := List.all_eq_true.1 hcf v (List.mem_range.2 hvl)
    revert hp hcfv
    cases (ir.value v).kind <;> simp
    rintro rfl h
    exact h
  · cases h

/-- **The key of a powers value is of the powers' field** (`powersB`). -/
theorem chalField_of_powersB {r key nch f : ℕ} (h : ir.powersB r key nch f = true) :
    ir.chalField key = f := by
  unfold powersB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.2

/-- **An accepted MAC H entry gives the H half of its cross-field `equal`** at the reader of `e`:
where the DAG holds at the inputs `val` and the cut nodes carry their meanings at the reader. -/
theorem macHHolds_of_macHB (hM : ir.DerivModel I primeNodes)
    (hC : ir.CircuitFieldOk I c ar cd.chr) (hE : ir.EmitTableOk (cd.env ar) cd.table)
    (hAr : (cd.env ar).ArithOk (I (ir.circField c)).decode) (hcf : ir.chalFieldsB = true)
    {e : ir.Env I} {val : ℕ → (I (ir.circField c)).K} {k p : ℕ} {mc : MacHCert} {as : List Assert}
    (hone : cd.dag.val cd.w (cd.consts.decode (I (ir.circField c)).decode) val 0 = 1)
    (hD : cd.dag.Holds cd.w (cd.consts.decode (I (ir.circField c)).decode) val)
    (hT : ∀ m < cd.table.size, (cd.table.get m).cut = true →
      ir.WiresOk c (cd.env ar) cd.table (ir.reader e)
        (cd.dag.val cd.w (cd.consts.decode (I (ir.circField c)).decode) val) m)
    (h : ir.macHB c ar cd k p mc as = true) :
    ir.MacHHolds (ir.reader e) p := by
  simp only [macHB, macHE, okB_seqE, okB_mapE, Bool.and_eq_true] at h
  obtain ⟨hg, hcuts, hitem⟩ := h
  rw [← GKR.Rel.relOk_eq_okB] at hcuts hitem
  have hcs := (GKR.Rel.relOk_sound hC.hom hone hD hcuts).1
  have hz := (GKR.Rel.relOk_sound hC.hom hone hD hitem).2 _ (List.mem_singleton_self _)
  unfold macHGuardE at hg
  unfold macHCuts at hcs
  unfold MacHHolds
  split at hg
  · rename_i dx x _ _ _ real hb
    rw [hb] at hcs
    simp only [hb]
    simp only [okB_seqE, okB_guardE, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, Nat.ble_eq,
      Option.isNone_iff_eq_none] at hg
    obtain ⟨⟨⟨⟨⟨⟨-, hhp⟩, hdx⟩, hmf⟩, hmfl⟩, hch⟩, hpow, htag, hbits, hchn, -⟩ := hg
    obtain ⟨⟨⟨hpw, hpwc⟩, hpwl⟩, hpwn⟩ := hpow
    obtain ⟨⟨⟨⟨htg, htgc⟩, htgl⟩, htge⟩, -⟩ := htag
    obtain ⟨⟨⟨hbt, hbtc⟩, hbtl⟩, hbtz⟩ := hbits
    split at hpwn
    · rename_i r _ _
      simp only [Bool.and_eq_true] at hpwn
      obtain ⟨hpeq, hpB⟩ := hpwn
      obtain ⟨v, hv, hvf⟩ := chalNode_of_powersB hcf hpB
      have hkf : ir.chalField real.key = real.macField := chalField_of_powersB hpB
      rw [hhp, hv]
      simp only
      have ho := hM.wf.refsOrdered
      have hβ : (castElt (ir.reader e v 0) : (I real.macField).K) =
          castElt (e.chal real.key 0) := by
        rw [castElt_eq_castElt_of_eq hkf, ir.reader_chalNode e hv hvf]
      rw [hβ]
      have hdF : ir.domainField dx < ir.fields.length := by
        rw [hdx]
        show ir.circField c < _
        rw [← hmf]
        exact hmfl
      have hc0 : 0 < ir.charOf (ir.domainField dx) := by
        rw [hdx]
        show 0 < ir.charOf (ir.circField c)
        rw [← hmf]
        omega
      have hpx := padsTo_of_zeroPadB ho hM.registered hM.lawful
        (fun _ _ hk i => reader_of_constant e hk i) hdF hc0 hbtz
      rw [← macHHoldsAt_of_padsTo hpx]
      have hrp : ∀ j < real.chunks, (castElt (ir.reader e r j) : (I real.macField).K) =
          (castElt (e.chal real.key 0) : (I real.macField).K) ^ (j + 1) :=
        fun j hj => reader_powers hM.lawful e hmfl (by omega) hpB hj
      unfold MacHHoldsAt macChunkH
      subst hdx
      generalize real.macField = mf at hmf hrp ⊢
      subst hmf
      have hw : ∀ m < cd.table.size, (cd.table.get m).cut = true → ∀ i < (cd.table.get m).len,
          (wireAt cd.table m i).val (I (ir.circField c)).decode
            (cd.dag.val cd.w (cd.consts.decode (I (ir.circField c)).decode) val) =
            ir.nodeSem (cd.env ar) cd.table (ir.reader e) (ir.circuit c).domain m i :=
        fun m hm hc i hi => (hT m hm hc).2 i hi
      have htw : (wireAt cd.table mc.tag 0).val (I (ir.circField c)).decode
          (cd.dag.val cd.w (cd.consts.decode (I (ir.circField c)).decode) val) =
            castElt (ir.reader e real.tag 0) := by
        rw [hw _ htg htgc 0 htgl, ← (eqB_sound ho hE (ir.reader e) _ htge).2]
        rfl
      have hpw' : ∀ j < real.chunks,
          (wireAt cd.table mc.powers j).val (I (ir.circField c)).decode
            (cd.dag.val cd.w (cd.consts.decode (I (ir.circField c)).decode) val) =
              castElt (ir.reader e r j) := by
        intro j hj
        rw [hw _ hpw hpwc j (by omega), ← (eqB_sound ho hE (ir.reader e) _ hpeq).2]
        rfl
      have hbw : ∀ j < real.chunks * real.width, (wireAt cd.table mc.bits j).val
          (I (ir.circField c)).decode
            (cd.dag.val cd.w (cd.consts.decode (I (ir.circField c)).decode) val) =
          castElt (ir.evalPad (ir.reader e) (ir.circuit c).domain
            (cd.table.print (cd.env ar) mc.bits) j) := by
        intro j hj
        rw [hw _ hbt hbtc j (by omega), evalPad,
          ite_eq_left (by rw [(print_spec ho hE (ir.reader e) mc.bits).1]; omega), castElt_self]
        show ir.evalE _ _ (cd.table.treeErase (cd.env ar) mc.bits) j = ir.evalE _ _ _ j
        rw [(print_spec ho hE (ir.reader e) mc.bits).2]
      have hG : ∀ i < real.width,
          (I (ir.circField c)).decode ((Trie.ofList (powList ar 2 real.width 1)).get i) =
            (I (ir.circField c)).decode 2 ^ i := by
        intro i hi
        have hm := map_powList hC.hom 2 real.width 1
        have hl : (powList ar 2 real.width 1).length = real.width := by
          simpa using congrArg List.length hm
        rw [Trie.get_ofList _ (by omega), List.getD_eq_getElem _ _ (by omega)]
        have h1 := congrArg (fun l => l[i]?) hm
        simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some,
          List.getElem?_eq_getElem (by omega : i < (powList ar 2 real.width 1).length),
          Option.some.injEq] at h1
        refine h1.trans ?_
        rw [hC.hom.one, one_mul]
      have hchunk : ∀ j < real.chunks, (mc.chunks.getD j default).val (I (ir.circField c)).decode
            (cd.dag.val cd.w (cd.consts.decode (I (ir.circField c)).decode) val) =
          ∑ i : Fin real.width, (I (ir.circField c)).decode 2 ^ (i : ℕ) *
            castElt (ir.evalPad (ir.reader e) (ir.circuit c).domain
              (cd.table.print (cd.env ar) mc.bits) (j * real.width + i)) := by
        intro j hj
        have h1 := hcs _
          (List.mem_map.2 ⟨_, getD_mem_zipIdx (l := mc.chunks) (i := j) (by omega), rfl⟩)
        rw [h1, sumL_eval hC.hom.zero, List.map_map, sum_range_map_eq_sum_fin]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Function.comp_apply, TE.eval, teW_eval]
        rw [hG i i.2, hbw _ (by have := i.2; nlinarith)]
      have hS : ∑ j : Fin real.chunks,
          (mc.chunks.getD j default).val (I (ir.circField c)).decode
              (cd.dag.val cd.w (cd.consts.decode (I (ir.circField c)).decode) val) *
            (wireAt cd.table mc.powers j).val (I (ir.circField c)).decode
              (cd.dag.val cd.w (cd.consts.decode (I (ir.circField c)).decode) val) =
          ∑ j : Fin real.chunks, castElt (e.chal real.key 0) ^ ((j : ℕ) + 1) *
            ∑ i : Fin real.width, (I (ir.circField c)).decode 2 ^ (i : ℕ) *
              castElt (ir.evalPad (ir.reader e) (ir.circuit c).domain
                (cd.table.print (cd.env ar) mc.bits) (j * real.width + i)) :=
        Finset.sum_congr rfl fun j _ => by rw [hchunk j j.2, hpw' j j.2, hrp j j.2, mul_comm]
      have hn1 : (I (ir.circField c)).decode cd.neg1 = -1 := hAr.neg1
      simp only [macHItem, TE.eval, teW_eval, sumL_eval hC.hom.zero, List.map_map, hn1,
        sum_map_zipIdx, hchn, sum_range_map_eq_sum_fin, Function.comp_apply, zero_add] at hz
      rw [← htw, ← hS]
      linear_combination hz
    · cases hpwn
  · simp [okB] at hg

/-- **A challenge's value lies in the challenge's field**, by the header's sweep (`chalFieldsB`). -/
theorem valueField_of_chalFieldsB (hcf : ir.chalFieldsB = true) {u j : ℕ}
    (hu : u < ir.values.length) (hk : (ir.value u).kind = .challenge j) :
    ir.valueField u = ir.chalField j := by
  have h := List.all_eq_true.1 hcf u (List.mem_range.2 hu)
  rw [hk] at h
  exact Nat.eq_of_beq_eq_true h

/-- **A challenge's value reads the challenge** at a reader, cast into the circuit's field. -/
theorem castElt_reader_challenge (hcf : ir.chalFieldsB = true) (e : ir.Env I) {u j : ℕ}
    (hu : u < ir.values.length) (hk : (ir.value u).kind = .challenge j) :
    (castElt (ir.reader e u 0) : (I (ir.circField c)).K) = castElt (e.chal j 0) := by
  have hf := valueField_of_chalFieldsB hcf hu hk
  have hr : ir.reader e u 0 = castElt (e.chal j 0) := read_of_challenge e hk (by simp [fuel]) 0
  rw [hr, castElt_castElt_eq, ite_eq_left hf.symm]

/-- **An entry with a family record holds** at the reader of `e`, where its head and its family
cuts are accepted: an alignment entry (no meaning), a range LogUp (`logupAt_of_logupB`, `α` the
challenge `e` draws, the weights' inputs `(α − j)⁻¹`), a MAC H half (`macHHolds_of_macHB`). -/
theorem entryHolds_of_famHead (hM : ir.DerivModel I primeNodes)
    (hC : ir.CircuitFieldOk I c ar cd.chr) (hE : ir.EmitTableOk (cd.env ar) cd.table)
    (hAr : (cd.env ar).ArithOk (I (ir.circField c)).decode) (hcf : ir.chalFieldsB = true)
    {e : ir.Env I} {val : ℕ → (I (ir.circField c)).K} {k : ℕ} {f : FamCert}
    (hone : cd.dag.val cd.w (cd.consts.decode (I (ir.circField c)).decode) val 0 = 1)
    (hD : cd.dag.Holds cd.w (cd.consts.decode (I (ir.circField c)).decode) val)
    (hT : ∀ m < cd.table.size, (cd.table.get m).cut = true →
      ir.WiresOk c (cd.env ar) cd.table (ir.reader e)
        (cd.dag.val cd.w (cd.consts.decode (I (ir.circField c)).decode) val) m)
    (hw : ∀ b t a T' : ℕ,
      (ir.circuit c).inputs[b]? = some (InputBlock.realizationPub (.weights t) a T') →
      1 ≤ a → a + T' ≤ (ir.circuit c).publicInputs → ∀ j < T',
        cd.dag.val cd.w (cd.consts.decode (I (ir.circField c)).decode) val (a + j) =
        ((castElt (e.chal (ir.alphaOf t) 0) : (I (ir.circField c)).K) - j)⁻¹)
    (hh : okB (ir.famHeadE c ar cd k f) = true) (hs : okB (ir.famSliceE c ar cd k 0 0) = true)
    (hf : (cd.entries.getD k default).fam = some f) :
    ir.EntryHolds (ir.reader e) ((ir.circuit c).entries.getD k default) := by
  unfold famHeadE at hh
  unfold famSliceE famCuts at hs
  rw [hf] at hs
  simp only [Nat.beq_refl, Bool.cond_true, List.drop_zero, logupCutsT_eq, macHCutsT_eq] at hs
  revert hh hs
  cases (ir.circuit c).entries.getD k default with
  | alignment n => intro _ _; trivial
  | typeCheck p => cases f <;> exact fun hh _ => absurd hh (by simp [okB])
  | pred p => cases f <;> exact fun hh _ => absurd hh (by simp [okB])
  | realization rc =>
    cases rc with
    | logup t g =>
      cases f with
      | logup lc =>
        intro hh hs
        have hB : ir.logupB c ar cd k t g lc (cd.entries.getD k default).asserts = true := by
          simp only [okB_seqE, Bool.and_eq_true] at hh
          simp only [logupB, logupE, okB_seqE, Bool.and_eq_true]
          exact ⟨hh.1, hs, hh.2⟩
        exact logupAt_of_logupB hM hC hE hAr hcf hone hD hT
          (fun u hu hk _ => castElt_reader_challenge hcf e hu hk)
          (fun b a T' hb ha hT' j hj => hw b t a T' hb ha hT' j hj) hB
      | _ => exact fun hh _ => absurd hh (by simp [okB])
    | macH p =>
      cases f with
      | macH mc =>
        intro hh hs
        have hB : ir.macHB c ar cd k p mc (cd.entries.getD k default).asserts = true := by
          simp only [okB_seqE, Bool.and_eq_true] at hh
          simp only [macHB, macHE, okB_seqE, Bool.and_eq_true]
          exact ⟨hh.1, hs, hh.2⟩
        exact macHHolds_of_macHB hM hC hE hAr hcf hone hD hT hB
      | _ => exact fun hh _ => absurd hh (by simp [okB])
    | named _ => cases f <;> exact fun hh _ => absurd hh (by simp [okB])
    | unmodeled _ => cases f <;> exact fun hh _ => absurd hh (by simp [okB])

end GordieHowe.RealizedProgram
