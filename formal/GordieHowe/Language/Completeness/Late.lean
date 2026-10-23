-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Completeness.Env

@[expose] public section

/-!
# GordieHowe: completeness certificates, the late generators' reads

What the late generators of a completeness certificate read, with the generators read off the
certificate (`Gens.at`): a generator reads only its inputs (`genSrcOf_congr_inputs`); the honest late
values respect the exported reads where every generated value reads only its exported reads
(`respectsReads_genLateOf`, checked by `genReadsCoveredCB`); and a late histogram counts its
group's needles at the honest environment, alone (`histogramsCount_lateC`) or beside a static
histogram (`histogramsCount_mixedC`).
-/

namespace GordieHowe.RealizedProgram

open Export ProofSystem.PhaseLayout IOP

section

variable {ir : RealizedProgram} {I : Interp}

variable (ir) in
/-- **The values and challenges the generator of value `v` (`genSrcOf`) reads**: a tag reads its H
operand's values and its key, a grouped `mod_q`'s accumulators and quotient digits read its
powers and its operand's values, an ungrouped digit-form `mod_q`'s accumulator and lower digits
read its left side's values (`genInputs` with the generators read off `G`). -/
def genInputsOf (G : Gens) (v : ℕ) : List ℕ × List ℕ :=
  match G.at v with
  | .tag p =>
    match (ir.predicate p).body with
    | .cross _ x _ _ _ real => (ir.exprNodes x, [real.key])
    | _ => ([], [])
  | .acc p =>
    match (ir.predicate p).body with
    | .mod _ _ L _ real =>
      match real.grouped, macUnits? L with
      | some _, some u => (u.powers :: ir.exprNodes u.operand, [])
      | _, _ => ([], [])
    | _ => ([], [])
  | .quotDigit p =>
    match (ir.predicate p).body with
    | .mod _ _ L _ real =>
      match real.grouped, macUnits? L with
      | some _, some u => (u.powers :: ir.exprNodes u.operand, [])
      | _, _ => ([], [])
    | _ => ([], [])
  | .digitsAcc p =>
    match (ir.predicate p).body with
    | .mod _ _ L _ _ => (ir.exprNodes L, [])
    | _ => ([], [])
  | .lowDigit p _ =>
    match (ir.predicate p).body with
    | .mod _ _ L _ _ => (ir.exprNodes L, [])
    | _ => ([], [])
  | _ => ([], [])

/-- **A generator reads only its inputs** (`genInputsOf`). -/
theorem genSrcOf_congr_inputs {G : Gens} {e e' : ir.Env I} {v : ℕ}
    (hr : ∀ w ∈ (ir.genInputsOf G v).1, ir.reader e w = ir.reader e' w)
    (hc : ∀ j ∈ (ir.genInputsOf G v).2, e.chal j = e'.chal j) :
    ir.genSrcOf G e v = ir.genSrcOf G e' v := by
  have hcons : ∀ (u : MacUnits), (∀ w ∈ u.powers :: ir.exprNodes u.operand,
      ir.reader e w = ir.reader e' w) →
      ir.reader e u.powers = ir.reader e' u.powers ∧
        ∀ w ∈ ir.exprNodes u.operand, ir.reader e w = ir.reader e' w := fun u h =>
    ⟨h _ (List.mem_cons_self ..), fun w hw => h w (List.mem_cons_of_mem _ hw)⟩
  funext i
  unfold genInputsOf at hr hc
  unfold genSrcOf
  cases hg : G.at v <;> simp only [hg] at hr hc ⊢
  case tag p =>
    cases hb : (ir.predicate p).body <;> simp only [hb] at hr hc ⊢
    rename_i x _ _ _ real
    rw [tagGen_congr (rd' := ir.reader e') hr, hc _ (List.mem_singleton_self _)]
  case acc p =>
    cases hb : (ir.predicate p).body <;> simp only [hb] at hr hc ⊢
    rename_i L _ real
    cases hg : real.grouped <;> cases hu : macUnits? L <;> simp only [hg, hu] at hr hc ⊢
    rename_i u
    obtain ⟨h4, h5⟩ := hcons u hr
    rw [accNat_congr h4 h5]
  case quotDigit p =>
    cases hb : (ir.predicate p).body <;> simp only [hb] at hr hc ⊢
    rename_i L _ real
    cases hg : real.grouped <;> cases hu : macUnits? L <;> simp only [hg, hu] at hr hc ⊢
    rename_i u
    obtain ⟨h4, h5⟩ := hcons u hr
    rw [digitNat_congr h4 h5]
  case digitsAcc p =>
    cases hb : (ir.predicate p).body <;> simp only [hb] at hr hc ⊢
    simp only [digitsAccNat, evalIntWith_congr hr]
  case lowDigit p j =>
    cases hb : (ir.predicate p).body <;> simp only [hb] at hr hc ⊢
    simp only [lowDigitNat, digitsAccNat, evalIntWith_congr hr]

variable (ir) in
/-- **What the generator of value `v` reads is listed in `rs`** (`genInputsOf`): its challenges, and
what its values read at the source environment (`SrcCovered`). -/
def GenCoveredC (G : Gens) (rs : List Read) (v : ℕ) : Prop :=
  (∀ j ∈ (ir.genInputsOf G v).2, Read.chal j ∈ rs) ∧
    ∀ w ∈ (ir.genInputsOf G v).1, ir.SrcCovered rs w

variable (ir) in
/-- **What the late histogram `v` reads is listed in `rs`**: what its needles read at the source
environment, and what the generators of the late values they read read. -/
def HistCoveredC (G : Gens) (rs : List Read) (v : ℕ) : Prop :=
  match G.at v with
  | .lateHist t g => ∀ m ∈ ir.members t g, ∀ w ∈ ir.exprNodes (ir.needleExpr m.pred m.needle),
      ir.SrcCovered rs w ∧ ∀ u, Read.late u ∈ ir.nodeReads ir.fuel w → ir.GenCoveredC G rs u
  | _ => True

variable (ir) in
/-- **Every generated late value reads only its exported reads** (`Value.reads`). -/
def GenReadsCoveredC (G : Gens) : Prop :=
  ∀ l : ir.Late, ir.GenCoveredC G (ir.value l.1).reads l.1 ∧
    ir.HistCoveredC G (ir.value l.1).reads l.1

/-- **A generator reads only what `GenCoveredC` lists**, at the source environment with two choices
of the source program's late values agreeing where `rs` lists their challenges. -/
theorem genSrcOf_congr {G : Gens} (hb : ir.BoundNoCopy) (x val : ir.Valuation I) {rs : List Read}
    {c c' : ∀ k, (ir.layout I).Ch k} {π π' : (ir.layout I).Pads}
    (hc : ∀ j, Read.chal j ∈ rs → ir.chalRead I c j = ir.chalRead I c' j)
    (hp : ∀ u : ir.Late, Read.pad u.1 ∈ rs → π u = π' u) {L L' : ir.Valuation I}
    (hL : ir.SrcLateAgree rs L L') {v : ℕ} (hv : ir.GenCoveredC G rs v) :
    ir.genSrcOf G (ir.srcEnvL I x val L c π) v = ir.genSrcOf G (ir.srcEnvL I x val L' c' π') v :=
  genSrcOf_congr_inputs
    (fun w hw => reader_srcLate_covered hb x val hc hp _ _ (hv.2 w hw) fun _ hu =>
      srcLateOf_congr_covered hL (hv.2 w hw) hu)
    fun j hj => hc j (hv.1 j hj)

/-- **The late histograms' environment agrees at a late value** whose source late values agree
and whose generator reads only what `GenCoveredC` lists. -/
theorem histEnvOf_late_congr {G : Gens} (hb : ir.BoundNoCopy) (x val : ir.Valuation I)
    {rs : List Read} {c c' : ∀ k, (ir.layout I).Ch k} {π π' : (ir.layout I).Pads}
    (hc : ∀ j, Read.chal j ∈ rs → ir.chalRead I c j = ir.chalRead I c' j)
    (hp : ∀ u : ir.Late, Read.pad u.1 ∈ rs → π u = π' u) {L L' : ir.Valuation I}
    (hL : ir.SrcLateAgree rs L L') {u : ℕ} (hs : ir.srcLateOf I L u = ir.srcLateOf I L' u)
    (hg : ir.GenCoveredC G rs u) :
    (ir.histEnvOf G (ir.srcEnvL I x val L c π)).late u =
      (ir.histEnvOf G (ir.srcEnvL I x val L' c' π')).late u := by
  funext k
  show (if k < (ir.value u).size then
      (if ir.IsSourceValue u then ir.srcLateOf I L u k
        else ir.genSrcOf G (ir.srcEnvL I x val L c π) u k)
      else 0) =
    (if k < (ir.value u).size then
      (if ir.IsSourceValue u then ir.srcLateOf I L' u k
        else ir.genSrcOf G (ir.srcEnvL I x val L' c' π') u k)
      else 0)
  rw [hs, genSrcOf_congr hb x val hc hp hL hg]

/-- **A generated value reads only what `GenCoveredC` and `HistCoveredC` list.** -/
theorem genValOf_congr {G : Gens} (hb : ir.BoundNoCopy) (x val : ir.Valuation I) {rs : List Read}
    {c c' : ∀ k, (ir.layout I).Ch k} {π π' : (ir.layout I).Pads}
    (hc : ∀ j, Read.chal j ∈ rs → ir.chalRead I c j = ir.chalRead I c' j)
    (hp : ∀ u : ir.Late, Read.pad u.1 ∈ rs → π u = π' u) {L L' : ir.Valuation I}
    (hL : ir.SrcLateAgree rs L L') {v : ℕ} (hv : ir.GenCoveredC G rs v)
    (hh : ir.HistCoveredC G rs v) :
    ir.genValOf G (ir.srcEnvL I x val L c π) v = ir.genValOf G (ir.srcEnvL I x val L' c' π') v := by
  funext i
  unfold genValOf
  split
  · unfold HistCoveredC at hh
    cases ho : G.at v <;> simp only [ho] at hh ⊢
    case lateHist t g =>
      rw [histNat_congr (rd := ir.reader (ir.histEnvOf G (ir.srcEnvL I x val L c π)))
        (rd' := ir.reader (ir.histEnvOf G (ir.srcEnvL I x val L' c' π'))) fun m hm w hw =>
        reader_srcLate_covered hb x val hc hp (ir.histEnvOf G (ir.srcEnvL I x val L c π)).late
          (ir.histEnvOf G (ir.srcEnvL I x val L' c' π')).late (hh m hm w hw).1
          fun u hu => histEnvOf_late_congr hb x val hc hp hL
            (srcLateOf_congr_covered hL (hh m hm w hw).1 hu) ((hh m hm w hw).2 u hu)]
    all_goals rw [genSrcOf_congr hb x val hc hp hL hv]
  · rfl

/-- **The honest late values of a certificate respect the exported reads** (`RespectsReads`), when
every generated value reads only its exported reads (`GenReadsCoveredC`). -/
theorem respectsReads_genLateOf {Inp : Type} {G : Gens} (hG : ir.CGenFacts I G)
    (hb : ir.BoundNoCopy) (hcov : ir.GenReadsCoveredC G) (stmtOf val : Inp → ir.Valuation I)
    (SL : ir.SrcLate I Inp) (y : Inp) :
    ir.RespectsReads (ir.genLateOf I hG stmtOf val SL y) := by
  intro l c c' π π' hc hp
  funext i
  apply Subtype.ext
  by_cases hs : ir.IsSourceValue l.1
  · simp only [genLateOf, dif_pos hs]
    rw [SL.respects y l.1 hs l.2 c c' hc]
  · simp only [genLateOf, dif_neg hs]
    rw [genValOf_congr hb (stmtOf y) (val y) hc hp
      (fun u hsu hlu hu => SL.respects y u hsu hlu c c' fun j hj => hc j (hu j hj))
      (hcov l).1 (hcov l).2]

variable (ir) in
/-- **`GenCoveredC`, through the reads tables.** -/
def genCoveredCB (G : Gens) (rs : List Read) (v : ℕ) : Bool :=
  (ir.genInputsOf G v).2.all (fun j => rs.contains (.chal j)) &&
    (ir.genInputsOf G v).1.all (ir.srcCoveredB rs)

/-- **`GenCoveredC` holds where its check does.** -/
theorem genCoveredC_of_B (hwf : ir.WellFormed) {G : Gens} {rs : List Read} {v : ℕ}
    (h : ir.genCoveredCB G rs v = true) : ir.GenCoveredC G rs v := by
  unfold genCoveredCB at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
  exact ⟨h.1, fun w hw => srcCovered_of_B hwf (h.2 w hw)⟩

variable (ir) in
/-- **`HistCoveredC`, through the reads tables.** -/
def histCoveredCB (G : Gens) (rs : List Read) (v : ℕ) : Bool :=
  match G.at v with
  | .lateHist t g => (ir.members t g).all fun m =>
      (ir.exprNodes (ir.needleExpr m.pred m.needle)).all fun w =>
        ir.srcCoveredB rs w && (ir.readsT.getD w []).all fun r =>
          match r with
          | .late u => ir.genCoveredCB G rs u
          | _ => true
  | _ => true

/-- **`HistCoveredC` holds where its check does.** -/
theorem histCoveredC_of_B (hwf : ir.WellFormed) {G : Gens} {rs : List Read} {v : ℕ}
    (h : ir.histCoveredCB G rs v = true) : ir.HistCoveredC G rs v := by
  unfold histCoveredCB at h
  unfold HistCoveredC
  split
  · rename_i t g htg
    simp only [htg, List.all_eq_true, Bool.and_eq_true] at h
    intro m hm w hw
    obtain ⟨h1, h2⟩ := h m hm w hw
    exact ⟨srcCovered_of_B hwf h1, fun u hu =>
      genCoveredC_of_B hwf (by simpa using h2 _ ((mem_readsT hwf w _).1 hu))⟩
  · trivial

variable (ir) in
/-- **`GenReadsCoveredC`, through the reads tables.** -/
def genReadsCoveredCB (G : Gens) : Bool :=
  (List.range ir.values.length).all fun v =>
    !decide (ir.IsLate v) ||
      (ir.genCoveredCB G (ir.value v).reads v && ir.histCoveredCB G (ir.value v).reads v)

/-- **`GenReadsCoveredC` holds where its check does.** -/
theorem genReadsCoveredC_of_B (hwf : ir.WellFormed) {G : Gens}
    (h : ir.genReadsCoveredCB G = true) : ir.GenReadsCoveredC G := by
  intro l
  have := List.all_eq_true.1 h l.1 (List.mem_range.2 l.1.2)
  have hl : ir.IsLate l.1 := l.2
  simp only [hl, decide_true, Bool.not_true, Bool.false_or, Bool.and_eq_true] at this
  exact ⟨genCoveredC_of_B hwf this.1, histCoveredC_of_B hwf this.2⟩

section HonestEnv

variable {Inp : Type} {G : Gens} (hG : ir.CGenFacts I G) (stmtOf val : Inp → ir.Valuation I)
  (SL : ir.SrcLate I Inp) (y : Inp) (c : ∀ k, (ir.layout I).Ch k) (π : (ir.layout I).Pads)

set_option hygiene false in
/-- The honest environment of the honest inputs `y`. -/
local notation "HE" => ir.honestEnv I (stmtOf y) (val y) (ir.genLateOf I hG stmtOf val SL y) c π

/-- **The honest environment reads like the histograms' environment** at a value whose late reads
are late values of the program that are no late histogram: the source program's late values alike,
the generated ones as `genSrcOf`. -/
theorem reader_honestEnvC_histEnvOf {v : ℕ}
    (hv : ∀ u, Read.late u ∈ ir.nodeReads ir.fuel v →
      (u < ir.values.length ∧ ir.IsLate u) ∧ ∀ t' g', G.at u ≠ .lateHist t' g') :
    ir.reader HE v =
      ir.reader (ir.histEnvOf G (ir.srcEnvL I (stmtOf y) (val y) (SL.late y c) c π)) v := by
  refine reader_eq_of_late (e := HE)
    (e' := ir.histEnvOf G (ir.srcEnvL I (stmtOf y) (val y) (SL.late y c) c π)) rfl rfl rfl
    fun u hu => ?_
  obtain ⟨hl, hh⟩ := hv u hu
  by_cases hs : ir.IsSourceValue u
  · rw [honestEnvC_late_eq_src hG stmtOf val SL y c π _ hl.1 hl.2 hs]
    funext i
    simp only [histEnvOf, hs, ite_true, srcEnvL, srcLateOf, hl.2, true_and]
    split_ifs <;> rfl
  · rw [honestEnvC_late_eq hG stmtOf val SL y c π _ hl.1 hl.2 hs]
    funext i
    simp only [genValOf, histEnvOf, hs, ite_false]

/-- **A late histogram counts its group's needles at the honest values**: for group `g` of table
`t` with a late histogram `v` (its generator `G.at v = .lateHist t g`, `v` no source value) and no
static one, the honest late histogram is the histogram of the needles read at the histograms'
environment (`histNat`), which reads the needles like the honest environment (`hneedle`: their late
reads are late values that are no late histogram). -/
theorem histogramsCount_lateC {t g v : ℕ}
    (hlate : (ir.groupOf t g).lateMult = some v) (hstatic : (ir.groupOf t g).staticMult = none)
    (hown : G.at v = .lateHist t g) (hns : ¬ ir.IsSourceValue v) (hv : v < ir.values.length)
    (hvl : ir.IsLate v) (hk : (ir.value v).kind = .late) (hsize : (ir.value v).size = ir.tableSize t)
    (hf : ir.valueField v = ir.chalField (ir.alphaOf t))
    (hneedle : ∀ m ∈ ir.members t g, ∀ w ∈ ir.exprNodes (ir.needleExpr m.pred m.needle),
      ∀ u, Read.late u ∈ ir.nodeReads ir.fuel w →
        (u < ir.values.length ∧ ir.IsLate u) ∧ ∀ t' g', G.at u ≠ .lateHist t' g') :
    Range.combined (ir.staticHist (ir.reader HE) (ir.chalField (ir.alphaOf t)) t g)
        (ir.lateHist (ir.reader HE) (ir.chalField (ir.alphaOf t)) t g) =
      Range.histogram (ir.groupNeedles (ir.reader HE) (ir.chalField (ir.alphaOf t)) t g) := by
  set E := HE
  have hN : ir.groupNeedles (ir.reader E) (ir.chalField (ir.alphaOf t)) t g =
      ir.groupNeedles
        (ir.reader (ir.histEnvOf G (ir.srcEnvL I (stmtOf y) (val y) (SL.late y c) c π)))
        (ir.chalField (ir.alphaOf t)) t g :=
    groupNeedles_congr fun m hm w hw =>
      reader_honestEnvC_histEnvOf hG stmtOf val SL y c π fun u hu => hneedle m hm w hw u hu
  funext j
  simp only [Range.combined, staticHist, lateHist, histRead, hstatic, hlate, j.2, dite_eq_left,
    zero_add, Range.histogram]
  rw [hsize, if_pos j.2, reader_of_late E hk, honestEnvC_late_eq hG stmtOf val SL y c π _ hv hvl hns]
  simp only [genValOf, hsize, j.2, if_true, hown, histNat, dite_true, histNeedles, hstatic,
    Option.isSome_none, Bool.false_eq_true, if_false]
  rw [castElt_natCast hf, hN]

/-- **A group with a static and a late histogram counts its needles at the honest values**
(`histogramsCount_mixedC`): the static histogram `s` (a committed
value reading no late value) counts the static members' needles at the source environment
(`hcount`), the late one `v` (its generator `G.at v = .lateHist t g`, `v` no source value; `histNat`)
the late members' needles, all below its size (`hbelow`); the needles below the table's size are
distinct in the field (`hinj`). -/
theorem histogramsCount_mixedC {t g v s : ℕ}
    (hlate : (ir.groupOf t g).lateMult = some v) (hstat : (ir.groupOf t g).staticMult = some s)
    (hown : G.at v = .lateHist t g) (hns : ¬ ir.IsSourceValue v) (hv : v < ir.values.length)
    (hvl : ir.IsLate v) (hsize : (ir.value v).size ≤ ir.tableSize t)
    (hf : ir.valueField v = ir.chalField (ir.alphaOf t))
    (hss : (ir.value s).size = ir.tableSize t) (hsl : ir.NoLateRead s)
    (hstaticNo : ∀ m ∈ ir.members t g, ir.memberReadsLate m = false →
      ∀ w ∈ ir.exprNodes (ir.needleExpr m.pred m.needle), ir.NoLateRead w)
    (hneedle : ∀ m ∈ ir.members t g, ∀ w ∈ ir.exprNodes (ir.needleExpr m.pred m.needle),
      ∀ u, Read.late u ∈ ir.nodeReads ir.fuel w →
        (u < ir.values.length ∧ ir.IsLate u) ∧ ∀ t' g', G.at u ≠ .lateHist t' g')
    (hinj : ∀ a b : ℕ, a < ir.tableSize t → b < ir.tableSize t →
      ((a : ℕ) : (I (ir.chalField (ir.alphaOf t))).K) = (b : ℕ) → a = b)
    (hcount : ∀ j : Fin (ir.tableSize t),
      (castElt (ir.reader (ir.srcEnvL I (stmtOf y) (val y) (SL.late y c) c π) s j) :
        (I (ir.chalField (ir.alphaOf t))).K) =
      (((ir.staticNeedles (ir.reader (ir.srcEnvL I (stmtOf y) (val y) (SL.late y c) c π))
        (ir.chalField (ir.alphaOf t)) t g).count (j : (I (ir.chalField (ir.alphaOf t))).K) : ℕ) :
          (I (ir.chalField (ir.alphaOf t))).K))
    (hbelow : ∀ x ∈ ir.histNeedles (ir.reader (ir.histEnvOf G (ir.srcEnvL I (stmtOf y) (val y)
      (SL.late y c) c π))) (ir.chalField (ir.alphaOf t)) t g, ∃ k < (ir.value v).size,
        x = ((k : ℕ) : (I (ir.chalField (ir.alphaOf t))).K)) :
    Range.combined (ir.staticHist (ir.reader HE) (ir.chalField (ir.alphaOf t)) t g)
        (ir.lateHist (ir.reader HE) (ir.chalField (ir.alphaOf t)) t g) =
      Range.histogram (ir.groupNeedles (ir.reader HE) (ir.chalField (ir.alphaOf t)) t g) := by
  set E := HE
  set E1 := ir.srcEnvL I (stmtOf y) (val y) (SL.late y c) c π
  set f := ir.chalField (ir.alphaOf t)
  have hS : ir.staticNeedles (ir.reader E) f t g = ir.staticNeedles (ir.reader E1) f t g := by
    unfold staticNeedles
    refine List.flatMap_congr fun m hm => ?_
    obtain ⟨hm1, hm2⟩ := List.mem_filter.1 hm
    have hnl : ir.memberReadsLate m = false := by simpa using hm2
    unfold memberVals
    rw [evalE_congr (f := f) fun w hw =>
      reader_honestEnvC_srcEnvL_of_noGen hG stmtOf val SL y c π (hstaticNo m hm1 hnl w hw).noGen]
  have hLate : ((ir.members t g).filter ir.memberReadsLate).flatMap (ir.memberVals (ir.reader E) f) =
      ir.histNeedles (ir.reader (ir.histEnvOf G E1)) f t g := by
    unfold histNeedles
    rw [hstat, Option.isSome_some, if_pos rfl]
    refine List.flatMap_congr fun m hm => ?_
    unfold memberVals
    rw [evalE_congr (f := f) fun w hw =>
      reader_honestEnvC_histEnvOf hG stmtOf val SL y c π fun u hu =>
        hneedle m (List.mem_of_mem_filter hm) w hw u hu]
  funext j
  unfold Range.combined staticHist lateHist histRead Range.histogram
  rw [hstat, hlate, dif_pos j.2]
  simp only []
  rw [if_pos (show (j : ℕ) < (ir.value s).size by rw [hss]; exact j.2),
    (List.Perm.count_eq (groupNeedles_perm _ f t g) _).symm, List.count_append, Nat.cast_add,
    reader_honestEnvC_srcEnvL_of_noGen hG stmtOf val SL y c π hsl.noGen, hcount j, hS, add_comm]
  congr 1
  rw [hLate]
  by_cases hj : (j : ℕ) < (ir.value v).size
  · rw [if_pos hj, reader_of_late E (kind_of_isLate hvl),
      honestEnvC_late_eq hG stmtOf val SL y c π _ hv hvl hns]
    simp only [genValOf, if_pos hj, hown, histNat, dif_pos j.2]
    exact castElt_natCast hf _
  · rw [if_neg hj]
    have hc : (ir.histNeedles (ir.reader (ir.histEnvOf G E1)) f t g).count
        (j : (I f).K) = 0 := by
      rw [List.count_eq_zero]
      intro hmem
      obtain ⟨k, hk, hkx⟩ := hbelow _ hmem
      have := hinj k j (by omega) j.2 (by rw [← hkx])
      omega
    rw [hc, Nat.cast_zero]

end HonestEnv

end

end GordieHowe.RealizedProgram
