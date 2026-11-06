-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Library.TableSelect
public import GordieHowe.Language.Realizations.Realized
public import GordieHowe.Language.Realizations.RealizeInteger
public import GordieHowe.Language.RealizedProgram.Shapes
public import GordieHowe.Language.Realizations.Derivation.TableKernel
public import GordieHoweNative.Language.Realizations.SelectionCheck

@[expose] public section

/-!
# GordieHowe: the selections' soundness from the program check

The check `selectionsB` (`GordieHoweNative/Language/Realizations/SelectionCheck.lean`) gives:

* **the table selection of every certificate** (`TableSelect.ofCheck`): the gadget's facts
  (`TableShape.selectB`) are the fields of `GordieHowe.RealizedProgram.TableSelect`, so a frontend
  reads its selection from the check;
* **the selections' soundness** (`selSound_of_selectionsB`, `RealizedProgram.SelSound`). Without a
  product form there is no selection event (`selSound_of_noProduct`). Otherwise each selection a
  product form's kernel reads (`kernelSel?`) is a checked gadget (`selLinkB`). Its event
  (`SelEvent`) implies the gadget's (`TableSelect.SelBad`, `selBad_of_selEventAt`): where the
  gadget's two equations hold and `γ` is no root of its fingerprint's polynomial, the record is the
  row map applied to the selected row (`TableSelect.record_eq_of_not_bad`), and the record's cells
  (`leafRun?_sound`) and the row map's leaves at the kernel's blocks (`rowApply_of_leafAt?`) make
  that the selection's exactness (`SelExact`). The gadgets' events have probability at most
  `(W − 1)/|F|` (`TableSelect.selBad_bound`, Schwartz–Zippel), within the exported degrees
  (`selError`), summed over the selections at a challenge (`probUniform_exists_mem_le`).
-/

namespace GordieHowe.RealizedProgram

open Export IOP
open scoped NNReal ENNReal

/-! ## The walkers -/

/-- **A step-`1` run of an index map** reads consecutive entries. -/
theorem IndexMap.stepRun?_spec : ∀ {m : IndexMap} {i len s : ℕ}, IndexMap.stepRun? m i len = some s →
    ∀ k < len, m.entry (i + k) = s + k
  | [], _, _, _, h => by simp [IndexMap.stepRun?] at h
  | (s₀, d, c) :: rest, i, len, s, h => by
    intro k hk
    simp only [IndexMap.stepRun?] at h
    by_cases hi : i < c
    · rw [if_pos hi] at h
      split_ifs at h with hd
      cases h
      obtain ⟨rfl, hle⟩ := hd
      simp only [IndexMap.entry, if_pos (show i + k < c by omega)]
      omega
    · rw [if_neg hi] at h
      have := IndexMap.stepRun?_spec h k hk
      simp only [IndexMap.entry, if_neg (show ¬ i + k < c by omega)]
      rw [show i + k - c = i - c + k by omega, this]

section Walkers

variable {ir : RealizedProgram} {I : Interp}

/-- **The record walker is sound**: cells `[start, start + len)` of the expression are cells
`[i, i + len)` of the value it names. -/
theorem leafRun?_sound (ho : ir.RefsOrdered) (rd : ir.Valuation I) (f : ℕ) :
    ∀ {n : ℕ} {E : Expr} {start len v i : ℕ}, ir.leafRun? n E start len = some (v, i) →
      ∀ k < len, ir.evalE rd f E (start + k) = ir.evalE rd f (.leaf v) (i + k)
  | 0, _, _, _, _, _, h => by simp [leafRun?] at h
  | n + 1, E, start, len, v, i, h => by
    intro k hk
    cases E with
    | leaf u =>
      simp only [leafRun?, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    | ref j =>
      simp only [leafRun?] at h
      split_ifs at h with hj
      rw [evalE_ref ho rd f hj]
      exact leafRun?_sound ho rd f h k hk
    | concat a b =>
      simp only [leafRun?] at h
      rw [evalE_concat]
      split_ifs at h with h1 h2
      · rw [if_pos (by omega)]
        exact leafRun?_sound ho rd f h k hk
      · rw [if_neg (by omega), show start + k - ir.exprLen a = start - ir.exprLen a + k by omega]
        exact leafRun?_sound ho rd f h k hk
    | reindex m a =>
      simp only [leafRun?] at h
      rw [evalE_reindex]
      split at h
      · rename_i s hs
        rw [IndexMap.stepRun?_spec hs k hk]
        exact leafRun?_sound ho rd f h k hk
      · cases h
    | _ => simp [leafRun?] at h

end Walkers

/-- **A row map at a leaf's first cell**: the row map applied to a row reads, at cell `c + k` of a
leaf starting at cell `c` (`leafAt?`), the leaf applied to the row's cells from `c` on. -/
theorem rowApply_of_leafAt? {K : Type*} [Field K] (dec : ℕ → K) :
    ∀ {m : List RowLeaf} {c : ℕ} {l : RowLeaf}, leafAt? m c = some l →
      ∀ (row : ℕ → K) {k : ℕ}, k < l.n →
        rowApply dec m row (c + k) = l.apply dec (fun j => row (c + j)) k
  | [], _, _, h => by simp [leafAt?] at h
  | l' :: ls, c, l, h => by
    intro row k hk
    simp only [leafAt?] at h
    split_ifs at h with h0 h1
    · cases h
      subst h0
      simp only [rowApply, Nat.zero_add, if_pos hk]
    · have ih := rowApply_of_leafAt? dec h (fun i => row (l'.n + i)) hk
      simp only [rowApply, if_neg (show ¬ c + k < l'.n by omega)]
      rw [show c + k - l'.n = c - l'.n + k by omega, ih]
      congr 1
      funext j
      congr 1
      omega

/-- **The transform in its order reads only its first `n` coordinates.** -/
theorem nttOf_congr {K : Type*} [Field K] (natural : Bool) {n : ℕ} (ψ : K) {x y : ℕ → K}
    (h : ∀ t < n, x t = y t) (m : ℕ) : Ops.nttOf natural n ψ x m = Ops.nttOf natural n ψ y m := by
  unfold Ops.nttOf
  split
  · exact NamedOp.nttNatural_congr h m
  · unfold Ops.nttScheme
    split_ifs
    · exact NamedOp.nttNatural_congr h _
    · rfl

/-- **A transform leaf applies its transform in its order.** -/
theorem RowLeaf.apply_of_ntt {K : Type*} [Field K] (dec : ℕ → K) {l : RowLeaf} (h : l.ntt = true)
    (row : ℕ → K) (k : ℕ) : l.apply dec row k = Ops.nttOf l.natural l.n (dec l.psi) row k := by
  unfold RowLeaf.apply Ops.nttOf
  rw [if_pos h]
  split <;> rfl

/-! ## The gadget's facts -/

section Gadget

variable {ir : RealizedProgram} {t : TableShape}

theorem isExprB_spec {k : Kind} (h : k.isExprB = true) : ∃ e, k = .pub (.expr e) := by
  revert h
  rcases k with _ | (_ | _ | e) | _ | _ | _ | _ | _ | _ | _ <;> simp [Kind.isExprB]

theorem isPrivB_spec {k : Kind} (h : k.isPrivB = true) : k = .priv := by
  revert h
  cases k <;> simp [Kind.isPrivB]

theorem isChallengeB_spec {k : Kind} {c : ℕ} (h : k.isChallengeB c = true) : k = .challenge c := by
  revert h
  cases k <;> simp [Kind.isChallengeB]

theorem isEqualB_spec {b : PredBody} {d : ℕ} {lhs rhs : Expr} (h : b.isEqualB d lhs rhs = true) :
    ∃ tg, b = .equal d lhs rhs tg := by
  revert h
  rcases b with ⟨d', l, r, tg⟩ | _ | _ | _ <;> simp only [PredBody.isEqualB,
    Bool.and_eq_true, beq_iff_eq, Bool.false_eq_true, false_implies]
  rintro ⟨⟨rfl, hl⟩, hr⟩
  exact ⟨tg, by rw [Expr.eq_of_beq hl, Expr.eq_of_beq hr]⟩

theorem isFullB_spec {c : Challenge} (h : c.isFullB = true) : c.sampler = .full := by
  revert h
  unfold Challenge.isFullB
  split <;> simp_all

/-- **The gadget's facts a passing certificate states** (`TableShape.selectB`): the fields of
`TableSelect` at the shape `t`, apart from the shared expressions' order. -/
structure TableShape.SelectFacts (ir : RealizedProgram) (t : TableShape) : Prop where
  exprs_pos : 0 < ir.exprs.length
  values_pos : 0 < ir.values.length
  mapWf : mapWfFrom 0 t.map = true
  width : mapWidth t.map = (t.parts.map (·.2)).sum
  powOk : ir.powSym ⟨onePub t.one t.gamma, none⟩ powFuel (t.powExpr ir) = some (powerExps t.map)
  digOk : ir.digestsOk (t.pubCtx ir) t.map t.parts t.rows (2 ^ t.bits) (t.digExpr ir) = true
  bodyOk : t.bodyOk ir (ir.predicate t.pred).body = true
  powKind : (ir.value t.pow).kind = .pub (.expr (t.powExpr ir))
  digKind : (ir.value t.dig).kind = .pub (.expr (t.digExpr ir))
  idxBool : ∃ tg, (ir.predicate t.idxPred).body =
    .equal t.dom (.mul (.leaf t.idx) (.leaf t.idx)) (.leaf t.idx) tg
  inSource : ∀ p ∈ [t.pred, t.idxPred],
    p < ir.predicates.length ∧ ir.inSource (ir.predicate p) = true
  consts : ir.isConstant t.one = true ∧ (ir.constEntries t.one).getD 0 0 = 1 ∧
    ir.isConstant t.zero = true ∧ (ir.constEntries t.zero).getD 0 0 = 0
  gammaKind : (ir.value t.gamma).kind = .challenge t.chal
  chalOk : (ir.challenge t.chal).size = 1 ∧ (ir.challenge t.chal).sampler = .full ∧
    ir.chalField t.chal = ir.domainField t.dom
  fields : ∀ v ∈ [t.one, t.zero, t.gamma, t.pow, t.dig, t.idx] ++ t.parts.map (·.1),
    ir.valueField v = ir.domainField t.dom
  sizes : (ir.value t.one).size = 1 ∧ (ir.value t.gamma).size = 1 ∧
    (ir.value t.idx).size = t.bits ∧ (ir.value t.dig).size = 2 ^ t.bits ∧
    (ir.value t.pow).size = (powerExps t.map).length
  idxPriv : (ir.value t.idx).kind = .priv
  recordReads : ∀ v ∈ ir.exprNodes t.record, ir.nodeReads ir.fuel v = []
  rowReads : ∀ p ∈ t.parts, ir.nodeReads ir.values.length p.1 = []

/-- **`TableShape.selectB` decides the gadget's facts.** -/
theorem TableShape.selectFacts_of_selectB (h : t.selectB ir = true) : t.SelectFacts ir := by
  unfold TableShape.selectB TableShape.okB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.isEmpty_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩, a10⟩, a11⟩, a12⟩, a13⟩, a14⟩, a15⟩, a16⟩, a17⟩, a18⟩, a19⟩, a20⟩, a21⟩, a22⟩, a23⟩, a24⟩, a25⟩, a26⟩, a27⟩, a28⟩ := h
  exact ⟨a6, a7, a1, a2, a3, a4, a5, TableShape.powKind_of_exists (isExprB_spec a8),
    TableShape.digKind_of_exists (isExprB_spec a9), isEqualB_spec a10, a11, ⟨a12, a13, a14, a15⟩,
    isChallengeB_spec a16, ⟨a17, isFullB_spec a18, a19⟩, a20, ⟨a21, a22, a23, a24, a25⟩,
    isPrivB_spec a26, a27, a28⟩

/-- **The table selection a passing certificate states** (`TableShape.selectB`): its gadget's
facts are the fields of `TableSelect`. -/
@[instance_reducible] def TableSelect.ofCheck (hwf : ir.WellFormed) (h : t.selectB ir = true) :
    TableSelect ir :=
  have F := TableShape.selectFacts_of_selectB h
  { shape := t
    refsOrdered := hwf.refsOrdered
    exprs_pos := F.exprs_pos
    values_pos := F.values_pos
    mapWf := F.mapWf
    width := F.width
    powOk := F.powOk
    digOk := F.digOk
    bodyOk := F.bodyOk
    powKind := F.powKind
    digKind := F.digKind
    idxBool := F.idxBool
    inSource := F.inSource
    consts := F.consts
    gammaKind := F.gammaKind
    chalOk := F.chalOk
    fields := F.fields
    sizes := F.sizes
    idxPriv := F.idxPriv
    recordReads := F.recordReads
    rowReads := F.rowReads }

/-- **The certificate's table selection has the certificate's shape.** -/
theorem TableSelect.ofCheck_shape (hwf : ir.WellFormed) (h : t.selectB ir = true) :
    @TableSelect.shape ir (TableSelect.ofCheck hwf h) = t := rfl

end Gadget

/-! ## The field's `−1` -/

/-- **A selection's field facts from the interpretation's lawfulness**: in a field of the program of
characteristic `p ≥ 2`, the constant `p − 1` decodes to `−1`, `0` and `1` to themselves, and `0`
and `1` read back as themselves. -/
theorem SelectField.of_lawful {ir : RealizedProgram} {I : Interp} {primeNodes : ℕ → List String}
    (hR : I.Registered ir) (hL : I.Lawful ir primeNodes) {f mOne : ℕ} (hf : f < ir.fields.length)
    (h2 : 2 ≤ (ir.field f).characteristic) (hm : mOne + 1 = (ir.field f).characteristic) :
    SelectField (I f) mOne := by
  have hc : ((ir.field f).characteristic : (I f).K) = 0 := by
    rw [← hR.characteristic f hf, ← hR.ringChar f hf]
    exact ringChar.Nat.cast_ringChar
  have h0 := hL.decode_natCast f hf 0 (by omega)
  have h1 := hL.decode_natCast f hf 1 (by omega)
  have t0 := hL.toNat_natCast f hf 0 (by omega)
  have t1 := hL.toNat_natCast f hf 1 (by omega)
  rw [Nat.cast_zero] at h0 t0
  rw [Nat.cast_one] at h1 t1
  refine ⟨?_, h0, h1, t0, t1⟩
  rw [hL.decode_natCast f hf mOne (by omega), eq_neg_iff_add_eq_zero, ← hc, ← hm]
  push_cast
  rfl

/-! ## The event -/

section Event

variable {ir : RealizedProgram} {I : Interp}

/-- **The selection event at predicate `q`** (`SelEvent` at one predicate). -/
def SelEventAt (q j : ℕ) (e : ir.Env I) : Prop :=
  ∃ sh, ir.kernelSel? q = some sh ∧ sh.chal = j ∧
    (∀ rd ∈ sh.records.flatMap (ir.nodeReads ir.fuel) ++ ir.nodeReads ir.fuel sh.table,
      ir.ReadFixedAt j rd) ∧
    (∀ p < ir.predicates.length, (ir.predicate p).body.isEqual = true →
      (∀ rd ∈ ir.predReads (ir.predicate p).body, ir.ReadFixedAt j rd) →
      ir.HoldsAt e (ir.predicate p).body) ∧ ¬ ir.SelExact (ir.reader e) sh

theorem selEvent_iff (j : ℕ) (e : ir.Env I) :
    ir.SelEvent j e ↔ ∃ q ∈ List.range ir.predicates.length, ir.SelEventAt q j e := by
  simp only [SelEvent, SelEventAt, List.mem_range]

/-- **A selection's kernel shape tiles the row.** -/
theorem tilesB_of_kernelSel {q : ℕ} {sh : SelShape} (h : ir.kernelSel? q = some sh) :
    ir.tilesB sh = true := by
  unfold kernelSel? at h
  rw [Option.filter_eq_some_iff] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2.1.2

/-- **`predFixedB` decides that a predicate reads only what is fixed when `j` is drawn.** -/
theorem predReads_fixed_of_predFixedB (hwf : ir.WellFormed) {j : ℕ} {b : PredBody}
    (h : ir.predFixedB j b = true) : ∀ rd ∈ ir.predReads b, ir.ReadFixedAt j rd :=
  predReads_fixed_of_readsFixedB hwf h

/-- **The link's parts** (`selLinkB`). -/
theorem selLinkB_spec {q : ℕ} {sh : SelShape} {t : TableShape} (h : ir.selLinkB q sh t = true) :
    t.pred = q ∧ t.dom = sh.domain ∧ t.chal = sh.chal ∧ t.rows = sh.rows ∧
      (∀ p ∈ [t.pred, t.idxPred], p < ir.predicates.length ∧
        (ir.predicate p).body.isEqual = true ∧ ir.predFixedB sh.chal (ir.predicate p).body = true) ∧
      t.parts.head? = some (sh.table, sh.width) ∧
      (∃ name, (ir.value sh.table).kind = .pub (.opaque name [])) ∧
      (∀ i < sh.records.length, ir.recordLinkB sh t i = true) ∧
      mapWidth t.map - 1 ≤ sh.deg ∧ t.dom < ir.domains.length ∧
      2 ≤ (ir.field (ir.domainField t.dom)).characteristic ∧
      t.mOne + 1 = (ir.field (ir.domainField t.dom)).characteristic := by
  unfold selLinkB at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  refine ⟨h1, h2, h3, h4, fun p hp => by simpa [Bool.and_eq_true, and_assoc] using h5 p hp, h6, ?_, h8,
    h9, h10, h11, h12⟩
  revert h7
  rcases (ir.value sh.table).kind with _ | (_ | ⟨name, _ | ⟨a, as⟩⟩ | _) | _ | _ | _ | _ | _ | _ | _ <;>
    simp

/-- **Without the gadget's event, a linked selection is exact** (`SelExact`): where the gadget's
two equations hold (`TableSelect.Preds`) and `γ` is no root of its fingerprint's polynomial
(`TableSelect.SelBad`), the record is the row map applied to the selected row
(`TableSelect.record_eq_of_not_bad`); at the kernel's records its cells are the records' cells
(`leafRun?_sound`), and at their blocks the row map is the kernel's transform of the table's row
(`rowApply_of_leafAt?`). -/
theorem selExact_of_not_selBad {primeNodes : ℕ → List String} (hwf : ir.WellFormed)
    (hR : I.Registered ir) (hL : I.Lawful ir primeNodes) {q : ℕ} {sh : SelShape} {t : TableShape}
    (hk : ir.kernelSel? q = some sh) (hsel : t.selectB ir = true)
    (hlink : ir.selLinkB q sh t = true) {e : ir.Env I} :
    letI := TableSelect.ofCheck hwf hsel
    TableSelect.Preds e → ¬ TableSelect.SelBad (ir.domainField t.dom) t.chal e →
      ir.SelExact (ir.reader e) sh := by
  let _ := TableSelect.ofCheck hwf hsel
  intro hp hno
  obtain ⟨-, hdom, -, hrows, -, hhead, ⟨name, hkind⟩, hrecs, -, hdlt, h2, hm⟩ :=
    selLinkB_spec hlink
  have F := TableShape.selectFacts_of_selectB hsel
  have tiles := tilesB_of_kernelSel hk
  have hf : ir.domainField (TableSelect.shape ir).dom = ir.domainField t.dom := rfl
  have : SelectField (I (ir.domainField t.dom)) (TableSelect.shape ir).mOne :=
    SelectField.of_lawful hR hL (domainField_lt hwf hdlt) h2 hm
  obtain ⟨ps, hps⟩ : ∃ ps, t.parts = (sh.table, sh.width) :: ps := by
    revert hhead
    cases t.parts with
    | nil => simp
    | cons x ps => intro h; simp only [List.head?_cons, Option.some.injEq] at h; exact ⟨ps, by rw [h]⟩
  have hW : sh.width ≤ TableSelect.W ir := by
    show sh.width ≤ mapWidth t.map
    rw [F.width, hps]
    simp
  refine ⟨TableSelect.rowIdx (ir.domainField t.dom) e, ?_, ?_⟩
  · rw [← hrows]
    exact TableSelect.rowIdx_lt hf hp
  intro i hi b hb m hmn
  have hrl := hrecs i hi
  simp only [recordLinkB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hrl
  obtain ⟨hrun, hleaves⟩ := hrl
  obtain ⟨l, hla, hlntt, hln, hlpsi, hlnat⟩ : ∃ l, leafAt? t.map
      ((ir.blockStart sh i + b) * sh.n) = some l ∧ l.ntt = true ∧ l.n = sh.n ∧ l.psi = sh.psi ∧
      l.natural = sh.natural := by
    have := hleaves b hb
    revert this
    cases leafAt? t.map ((ir.blockStart sh i + b) * sh.n) with
    | none => simp
    | some l =>
      simp only [Bool.and_eq_true, beq_iff_eq]
      rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
      exact ⟨l, rfl, h1, h2, h3, h4⟩
  set s := ir.blockStart sh i
  set v := sh.records.getD i 0
  have hbw := blockStart_add_le ir tiles hi
  have hbn : (s + b) * sh.n + sh.n ≤ sh.width := by
    have : s + b + 1 ≤ s + ir.recBlocks sh v := by omega
    calc (s + b) * sh.n + sh.n = (s + b + 1) * sh.n := by ring
      _ ≤ (s + ir.recBlocks sh v) * sh.n := Nat.mul_le_mul_right _ this
      _ ≤ sh.width := hbw
  have hc : (s + b) * sh.n + m < TableSelect.W ir := by omega
  have hvs : b * sh.n + m < (ir.value v).size := by
    have h1 : b + 1 ≤ ir.recBlocks sh v := hb
    have h2 : (b + 1) * sh.n ≤ (ir.value v).size :=
      (Nat.mul_le_mul_right _ h1).trans (Nat.div_mul_le_self _ _)
    calc b * sh.n + m < b * sh.n + sh.n := by omega
      _ = (b + 1) * sh.n := by ring
      _ ≤ _ := h2
  have hrec := TableSelect.record_eq_of_not_bad hf hp hno hc
  have hL' := leafRun?_sound hwf.refsOrdered (ir.reader e) (ir.domainField t.dom) hrun
    (b * sh.n + m) hvs
  have hR' := rowApply_of_leafAt? (I (ir.domainField t.dom)).decode hla
    (TableSelect.rowAt (ir.domainField t.dom) e (TableSelect.rowIdx (ir.domainField t.dom) e))
    (show m < l.n by rw [hln]; exact hmn)
  rw [RowLeaf.apply_of_ntt _ hlntt, hln, hlpsi, hlnat] at hR'
  have hrow : ∀ j < sh.n,
      TableSelect.rowAt (ir.domainField t.dom) e (TableSelect.rowIdx (ir.domainField t.dom) e)
        ((s + b) * sh.n + j) =
      castElt (ir.reader e sh.table
        (TableSelect.rowIdx (ir.domainField t.dom) e * sh.width + (s + b) * sh.n + j)) := by
    intro j hj
    show rowOf (rowRead (ir.read e ir.values.length) (ir.domainField t.dom)) t.parts _ _ = _
    rw [hps]
    simp only [rowOf, if_pos (show (s + b) * sh.n + j < sh.width by omega), rowRead,
      read_of_opaque_nil e F.values_pos hkind, reader_of_opaque_nil e hkind, Nat.add_assoc]
  rw [← hdom]
  calc (castElt (ir.reader e v (b * sh.n + m)) : (I (ir.domainField t.dom)).K)
      = ir.evalE (ir.reader e) (ir.domainField t.dom) t.record (s * sh.n + (b * sh.n + m)) := by
        rw [hL', Nat.zero_add]
        rfl
    _ = TableSelect.recOf (ir.domainField t.dom) e ((s + b) * sh.n + m) := by
        unfold TableSelect.recOf
        congr 1
        ring
    _ = TableSelect.mapOf (ir.domainField t.dom) e ((s + b) * sh.n + m) := hrec
    _ = _ := hR'
    _ = _ := nttOf_congr _ _ hrow m

end Event

/-! ## The bound -/

section Bound

/-- **An impossible event has probability `0`.** -/
theorem probUniform_le_of_forall_not {C : Type} [Fintype C] [Nonempty C] {p : C → Prop}
    (h : ∀ c, ¬ p c) (x : ℝ≥0∞) : Pr[c ← C : p c] ≤ x := by
  have : {c : C | p c} = ∅ := Set.eq_empty_of_forall_notMem h
  simp only [probUniform, this, MeasureTheory.measure_empty]
  exact zero_le

/-- **The union bound over a list**: the probability that some event of the list occurs is at most
the sum of their bounds. -/
theorem probUniform_exists_mem_le {C ι : Type} [Fintype C] [Nonempty C] (E : ι → C → Prop)
    (a : ι → ℝ≥0) : ∀ L : List ι, (∀ i ∈ L, Pr[c ← C : E i c] ≤ a i) →
      Pr[c ← C : ∃ i ∈ L, E i c] ≤ ((L.map a).sum : ℝ≥0∞)
  | [], _ => probUniform_le_of_forall_not (by simp) _
  | x :: L, h => by
    have hL := probUniform_exists_mem_le E a L fun i hi => h i (List.mem_cons_of_mem _ hi)
    have hx := h x List.mem_cons_self
    refine ((PMF.uniformOfFintype C).toOuterMeasure.mono fun c hc => ?_).trans
      ((probUniform_or_le_add hx hL).trans ?_)
    · simp only [Set.mem_setOf_eq, List.mem_cons, exists_eq_or_imp] at hc ⊢
      exact hc
    · simp [List.map_cons, List.sum_cons]

theorem sum_map_filterMap {α β : Type} (F : α → Option β) (g : β → ℝ≥0) :
    ∀ L : List α, ((L.filterMap F).map g).sum =
      (L.map fun x => match F x with | some b => g b | none => 0).sum
  | [] => rfl
  | x :: L => by
    rw [List.filterMap_cons, List.map_cons, List.sum_cons, ← sum_map_filterMap F g L]
    cases F x with
    | none => simp
    | some b => simp

variable {ir : RealizedProgram} {I : Interp}

/-- **The selections' soundness from the program check** (`RealizedProgram.SelSound`): without a
product form there is no selection event (`selSound_of_noProduct`); otherwise every selection a
product form's kernel reads is a checked gadget (`selLinkB`), whose event implies the gadget's
(`selExact_of_not_selBad`), of probability at most `(W − 1)/|F|` (`TableSelect.selBad_bound`),
within the selection's exported degree; the selections at a challenge add up
(`probUniform_exists_mem_le`) to the selection error (`selError`). -/
theorem selSound_of_selectionsB {primeNodes : ℕ → List String} (hwf : ir.WellFormed)
    (hR : I.Registered ir) (hL : I.Lawful ir primeNodes) {cs : List SelCert}
    (h : ir.selectionsB cs = true) : ir.SelSound I := by
  unfold selectionsB at h
  rw [Bool.and_eq_true, Bool.or_eq_true] at h
  obtain ⟨hall, hnp | hsel⟩ := h
  · exact selSound_of_noProduct ir hnp
  rw [List.all_eq_true] at hall hsel
  intro j e
  let a : ℕ → ℝ≥0 := fun q => match ir.kernelSel? q with
    | some sh => if sh.chal = j then
        (sh.deg : ℝ≥0) / (Fintype.card (I (ir.chalField j)).K - ir.tmaxOf j : ℕ) else 0
    | none => 0
  have hsum : ((List.range ir.predicates.length).map a).sum = ir.selError I j := by
    rw [selError, selErrorTerms, sum_map_filterMap]
    congr 1
    refine List.map_congr_left fun q _ => ?_
    simp only [a]
    cases ir.kernelSel? q with
    | none => rfl
    | some sh =>
      by_cases hj : sh.chal = j
      · simp only [Option.bind_some, hj, if_true]
      · simp only [Option.bind_some, hj, if_false]
  have hb : ∀ q ∈ List.range ir.predicates.length,
      Pr[c ← ir.ChalVal I j : ir.SelEventAt q j (e.setChal j c)] ≤ a q := by
    intro q hq
    cases hk : ir.kernelSel? q with
    | none =>
      refine probUniform_le_of_forall_not (fun c ⟨sh, hk', _⟩ => ?_) _
      rw [hk] at hk'
      cases hk'
    | some sh =>
      by_cases hj : sh.chal = j
      swap
      · refine probUniform_le_of_forall_not (fun c ⟨sh', hk', hj', _⟩ => ?_) _
        rw [hk] at hk'
        cases hk'
        exact hj hj'
      have hq' := hsel q hq
      rw [hk] at hq'
      simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hq'
      obtain ⟨c, hc, rfl, hlink⟩ := hq'
      have hselc := hall c hc
      obtain ⟨-, -, h3, -, h5, -, -, -, h9, -, -, -⟩ := selLinkB_spec hlink
      have F := TableShape.selectFacts_of_selectB hselc
      let _ := TableSelect.ofCheck hwf hselc
      have hjt : c.table.chal = j := h3.trans hj
      subst hjt
      have hev : ∀ x, ir.SelEventAt c.q c.table.chal (e.setChal c.table.chal x) →
          TableSelect.SelBad (ir.domainField c.table.dom) c.table.chal
            (e.setChal c.table.chal x) := by
        rintro x ⟨sh', hk', hj', -, heqs, hx⟩
        rw [hk] at hk'
        cases hk'
        by_contra hno
        refine hx (selExact_of_not_selBad hwf hR hL hk hselc hlink ?_ hno)
        intro p hp
        obtain ⟨hlt, hEq, hfix⟩ := h5 p hp
        exact heqs p hlt hEq (h3 ▸ predReads_fixed_of_predFixedB hwf hfix)
      have hbd := TableSelect.selBad_bound (program := ir) (I := I)
        (f := ir.domainField c.table.dom) rfl e
      refine ((PMF.uniformOfFintype _).toOuterMeasure.mono fun x hx => hev x hx).trans
        (hbd.trans ?_)
      have hcf : ir.chalField c.table.chal = ir.domainField c.table.dom := F.chalOk.2.2
      have htmax : ir.tmaxOf c.table.chal = 0 := by
        simp only [tmaxOf, F.chalOk.2.1]
      simp only [a, hk, h3.symm, if_true]
      rw [hcf, htmax, Nat.sub_zero]
      exact ENNReal.coe_le_coe.2 (div_le_div_of_nonneg_right (by exact_mod_cast h9) (by positivity))
  calc Pr[c ← ir.ChalVal I j : ir.SelEvent j (e.setChal j c)]
      ≤ Pr[c ← ir.ChalVal I j : ∃ q ∈ List.range ir.predicates.length,
          ir.SelEventAt q j (e.setChal j c)] :=
        (PMF.uniformOfFintype _).toOuterMeasure.mono fun x hx => (selEvent_iff j _).1 hx
    _ ≤ _ := probUniform_exists_mem_le _ a _ hb
    _ = _ := by rw [hsum]

/-- **Every certificate of a passing check states its gadget's facts** (`TableShape.selectB`). -/
theorem selectB_of_selectionsB {ir : RealizedProgram} {cs : List SelCert}
    (h : ir.selectionsB cs = true) {c : SelCert} (hc : c ∈ cs) : c.table.selectB ir = true := by
  unfold selectionsB at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  exact h.1 c hc

/-- **The table selection of certificate `i` of a passing check** (`TableSelect.ofCheck`): a
frontend's `TableSelect` from the program check, its shape the certificate's. -/
@[instance_reducible] def TableSelect.ofSelections {ir : RealizedProgram} (hwf : ir.WellFormed)
    {cs : List SelCert} (h : ir.selectionsB cs = true) (i : Fin cs.length) : TableSelect ir :=
  TableSelect.ofCheck hwf (selectB_of_selectionsB h (List.get_mem cs i))

end Bound

end GordieHowe.RealizedProgram
