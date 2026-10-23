-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Completeness.Deriv
public import GordieHowe.Language.Completeness.Late

@[expose] public section

/-!
# GordieHowe: the honest prover from a completeness certificate

The honest prover of a realized program from an execution of its source program and a completeness
certificate (`GordieHowe.RealizedProgram.HonestCore.ofCompletion`, `lem:core-red` (2)): the committed
values are the execution's phase-`0` values with the committed generators' values
(`genCommitted`), the late values the execution's with the late generators' (`genLateOf`), and the
completeness events the execution's. Off the events, at the honest environment, every predicate
holds by its completeness derivation (`holds_of_cderivs`, `cEnvFacts_honestEnvC`), every node-typed
value lies in its type, every group's histograms count its needles (a static histogram as at the
source environment, a late one by `histogramsCount_lateC`, a static and a late one by
`histogramsCount_mixedC`), the digits are below their bases, the MACs' tags are honest
(`MacFormC.ofB_macTag_honest`), and the committed cells lie in their bases.

The certificate's checks (`GordieHowe.RealizedProgram.CompletionFacts`) cover the realizations the
completeness rules cover: the two-sided and digit lookups with their digits generated as theirs
or as the committed digits of a quotient (`digitLookups`), the values bound to their digits
(`CommittedFacts.boundRecs`), the static histograms, the late histograms that are the only
histogram of their group (`lateGroups`) and the groups with both (`mixedGroups`), the quotients of
one-digit `mod_q`s, the committed-digits `mod_q`s, the MACs with a grouped, a one-digit or an
ungrouped digit tail and the MAC checks over the fields of characteristic `2` (`macs`), the Boolean checks of the pad copies, the spectrally realized convolutions with their
transformed values generated as theirs and the predicates realized through them, and the field
equations of the field-form `mod_q`s (from the execution's field equations, `fieldEqs`).
-/

namespace GordieHowe.RealizedProgram

open Export ProofSystem.PhaseLayout IOP Range
open scoped NNReal

section

variable {ir : RealizedProgram} {I : Interp} {primeNodes : ℕ → List String}

variable (ir) in
/-- **The facts of group `g` of table `t` with the late histogram `v`** at the certificate's
generators `G`: no static histogram; `v` generated as the group's late histogram, no source value, a
late value of the program of the table's size in the field of the table's challenge; the table a
range; the needles reading only late values of the program that are no late histogram. -/
structure LateGroupFactsC (G : Gens) (t g v : ℕ) : Prop where
  /-- No static histogram. -/
  static : (ir.groupOf t g).staticMult = none
  /-- Generated as the group's late histogram. -/
  own : G.at v = .lateHist t g
  /-- No source value. -/
  notSource : ¬ ir.IsSourceValue v
  /-- A value of the program. -/
  lt : v < ir.values.length
  /-- A late value. -/
  late : ir.IsLate v
  /-- The table's size. -/
  size : (ir.value v).size = ir.tableSize t
  /-- The field of the table's challenge. -/
  field : ir.valueField v = ir.chalField (ir.alphaOf t)
  /-- The table is a range. -/
  range : ir.IsRange t
  /-- The needles read only late values of the program that are no late histogram. -/
  needles : ∀ m ∈ ir.members t g, ∀ w ∈ ir.exprNodes (ir.needleExpr m.pred m.needle),
    ∀ u, Read.late u ∈ ir.nodeReads ir.fuel w →
      (u < ir.values.length ∧ ir.IsLate u) ∧ ∀ t' g', G.at u ≠ .lateHist t' g'

variable (ir primeNodes) in
/-- **A late member `m` of a mixed group at the late histogram `v` of table `t` reads a digit of the
tail of the MAC of site `st`** (`HonestFacts.mixedLate` at a site, with the generators read off
`G`), as a check: the site's MAC and interval facts check, and the needle is the lower or the top
digit of an ungrouped digit tail (`lateMemberAtB`, the top digit's bound `macTopMax` below the late
histogram's size) or the quotient of a one-digit tail (`lateMemberOneAtB`, its bound `macQuotMax`
below that size). -/
def mixedMemberCB (G : Gens) (t v : ℕ) (st : MacSite) (m : Member) : Bool :=
  ir.macBaseCB primeNodes G st && ir.macIvlB primeNodes st &&
    ((ir.digitsMacCB G st && ir.lateMemberAtB st t v m &&
        decide (ir.macTopMax st < (ir.value v).size)) ||
      (ir.oneDigitMacCB G st && ir.lateMemberOneAtB st t m &&
        decide (ir.macQuotMax st < (ir.value v).size)))

variable (ir primeNodes) in
/-- **The facts of group `g` of table `t` with the late histogram `v` and the static histogram `s`**
at the certificate's generators `G`: `v` generated as
the group's late histogram, no source value, a late value of the program at most the table's size
in the field of the table's challenge; the table a range; `s` with its static histogram's facts,
reading no late value; the static members reading no late value, every needle's late reads late
values that are no late histogram; the table's size at most the characteristic of the challenge's
field, a field of the program; every late member reading a digit of a MAC's tail
(`mixedMemberCB`). -/
structure MixedGroupFactsC (G : Gens) (t g v s : ℕ) : Prop where
  /-- Generated as the group's late histogram. -/
  own : G.at v = .lateHist t g
  /-- No source value. -/
  notSource : ¬ ir.IsSourceValue v
  /-- A value of the program. -/
  lt : v < ir.values.length
  /-- A late value. -/
  late : ir.IsLate v
  /-- At most the table's size. -/
  sizeLe : (ir.value v).size ≤ ir.tableSize t
  /-- The field of the table's challenge. -/
  field : ir.valueField v = ir.chalField (ir.alphaOf t)
  /-- The table is a range. -/
  range : ir.IsRange t
  /-- The static histogram's facts. -/
  static : ir.StaticGroupFactsC G t g s
  /-- The static histogram reads no late value. -/
  staticNoLate : ir.NoLateRead s
  /-- The static members read no late value. -/
  staticNo : ∀ m ∈ ir.members t g, ir.memberReadsLate m = false →
    ∀ w ∈ ir.exprNodes (ir.needleExpr m.pred m.needle), ir.NoLateRead w
  /-- The needles read only late values of the program that are no late histogram. -/
  needles : ∀ m ∈ ir.members t g, ∀ w ∈ ir.exprNodes (ir.needleExpr m.pred m.needle),
    ∀ u, Read.late u ∈ ir.nodeReads ir.fuel w →
      (u < ir.values.length ∧ ir.IsLate u) ∧ ∀ t' g', G.at u ≠ .lateHist t' g'
  /-- The challenge's field is a field of the program. -/
  fieldLt : ir.chalField (ir.alphaOf t) < ir.fields.length
  /-- The table's size is at most its characteristic. -/
  sizeChar : ir.tableSize t ≤ ir.charOf (ir.chalField (ir.alphaOf t))
  /-- Every late member reads a digit of a MAC's tail. -/
  members : ∀ m ∈ ir.members t g, ir.memberReadsLate m = true →
    ∃ st, ir.mixedMemberCB primeNodes G t v st m = true

variable (ir I primeNodes) in
/-- **The facts of a program and its completeness certificate** (generators `G`, derivations `D`)
the honest prover needs: the committed values' facts (`CommittedFacts`), the late generators'
(`CGenFacts`) and their reads (`BoundNoCopy`, `GenReadsCoveredC`); the node-typed values' types; the
groups' reads and late histograms; every cross-field `equal` a MAC with a grouped, a one-digit or an
ungrouped digit tail, or a MAC check over a field of characteristic `2`, at a MAC site; the MACs'
blinds; the two-sided and digit lookups; and every predicate's completeness
derivation checking. -/
structure CompletionFacts (G : Gens) (D : CDerivations) : Prop where
  /-- The honest committed values' facts. -/
  committed : ir.CommittedFacts I G
  /-- The late generators' facts. -/
  gen : ir.CGenFacts I G
  /-- The values bound to their digits read no pad copy. -/
  boundNoCopy : ir.BoundNoCopy
  /-- Every generated late value reads only its exported reads. -/
  covered : ir.GenReadsCoveredC G
  /-- A node-typed generated late value is no tag, and its type contains the naturals. -/
  lateTypes : ∀ l : ir.Late, ¬ ir.IsSourceValue l.1 → (ir.value l.1).typeSource = .node →
    (∀ p, G.at l.1 ≠ .tag p) ∧ ∀ n : ℕ, (I (ir.valueField l.1)).InType (ir.value l.1).type n
  /-- A node-typed value that is not late reads no late value. -/
  typedNoLate : ∀ v < ir.values.length, (ir.value v).typeSource = .node → ¬ ir.IsLate v →
    ir.NoLateRead v
  /-- A group with no late histogram reads no late value, nor do its table's rows. -/
  staticGroups : ∀ t < ir.tables.length, ∀ g < ir.groupCountOf t,
    (ir.groupOf t g).lateMult = none →
      (∀ m ∈ ir.members t g, ∀ w ∈ ir.exprNodes (ir.needleExpr m.pred m.needle), ir.NoLateRead w) ∧
        (∀ v ∈ (ir.groupOf t g).staticMult.toList, ir.NoLateRead v) ∧
        ∀ w ∈ ir.tableRowReads t, ir.NoLateRead w
  /-- A group with a late histogram and no static one has its facts. -/
  lateGroups : ∀ t < ir.tables.length, ∀ g < ir.groupCountOf t, ∀ v,
    (ir.groupOf t g).lateMult = some v → (ir.groupOf t g).staticMult = none →
      ir.LateGroupFactsC G t g v
  /-- A group with a late and a static histogram has its facts. -/
  mixedGroups : ∀ t < ir.tables.length, ∀ g < ir.groupCountOf t, ∀ v s,
    (ir.groupOf t g).lateMult = some v → (ir.groupOf t g).staticMult = some s →
      ir.MixedGroupFactsC primeNodes G t g v s
  /-- Every cross-field `equal` is the predicate of a MAC site whose MAC, tail and interval
  facts check, or whose MAC check over a field of characteristic `2` checks. -/
  macs : ∀ pid < ir.predicates.length, ∀ dx x dy y k real,
    (ir.predicate pid).body = .cross dx x dy y k real → ∃ st : MacSite, st.pid = pid ∧
      ((ir.macBaseCB primeNodes G st = true ∧ ir.macTailCB primeNodes G st = true ∧
        ir.macIvlB primeNodes st = true) ∨ ir.twoMacCB primeNodes G st = true)
  /-- Every MAC's blind is the pad copy `polynomialBits` of its tag's pad. -/
  blinds : ir.BlindsArePadCopies
  /-- Every two-sided and digit lookup has one record and a range. -/
  digitShape : ∀ pid < ir.predicates.length, ∀ r, lookupOf? (ir.predicate pid).body = some r →
    (r.kind = .twoSided ∨ r.kind = .digits) →
      ∃ d rec N, (ir.predicate pid).body = .mem d [rec] (.range N) (.lookup r)
  /-- Every two-sided and digit lookup has its facts, its digits generated as its digits or as
  the committed digits of a quotient. -/
  digitLookups : ∀ pid < ir.predicates.length, ∀ d rec N r,
    (ir.predicate pid).body = .mem d [rec] (.range N) (.lookup r) →
      (r.kind = .twoSided ∨ r.kind = .digits) →
        ir.DigitLookupFactsC G pid d rec N r ∨ ∃ m j, ir.commLookupCB G pid m j = true
  /-- Every predicate's completeness derivation checks. -/
  derivs : ir.cderivsB primeNodes G D = true

/-- **A source value reads no generated late value** (`SourceValid.reads`). -/
theorem noGenRead_of_source (hsv : ir.SourceValid) {w : ℕ} (hw : w < ir.values.length)
    (hs : ir.IsSourceValue w) : ir.NoGenRead w :=
  fun _ hu _ _ => hsv.reads w hw hs _ hu

/-- **A source predicate reads no generated late value**: it reads only source values
(`SourceValid.preds`), which read none (`noGenRead_of_source`); a value past the program reads
nothing. -/
theorem noGenPred_of_inSource (hsv : ir.SourceValid) {p : Predicate} (hp : p ∈ ir.predicates)
    (hs : ir.inSource p = true) : ir.NoGenPred p.body := by
  intro w hw u hu hlt hl
  by_cases hwl : w < ir.values.length
  · exact noGenRead_of_source hsv hwl (hsv.preds p hp hs w hw) u hu hlt hl
  · rw [nodeReads_of_le (Nat.le_of_not_lt hwl)] at hu
    cases hu

variable {Inp : Type} {relH : Set (ir.Valuation I × Inp)}

/-- **The honest committed values of an execution with a certificate.** -/
abbrev SourceExecutionCore.committedC (E : ir.SourceExecutionCore I relH) (G : Gens) :
    Inp → ir.Valuation I :=
  fun y => ir.genCommitted I G (E.stmtOf y) (E.val y)

section Env

variable (hM : ir.DerivModel I primeNodes) (hreal : ir.MacsRealizable primeNodes)
  {G : Gens} {D : CDerivations} (R : ir.CompletionFacts I primeNodes G D)
  (E : ir.SourceExecutionCore I relH) (y : Inp) (c : ∀ k, (ir.layout I).Ch k)
  (π : (ir.layout I).Pads)

set_option hygiene false in
/-- The honest environment of a certificate. -/
local notation "HE" => ir.honestEnv I (E.stmtOf y) (E.committedC G y)
  (ir.genLateOf I R.gen E.stmtOf (E.committedC G) E.srcLate y) c π

set_option hygiene false in
/-- The source environment of the honest committed values. -/
local notation "SE" => ir.srcEnvL I (E.stmtOf y) (ir.genCommitted I G (E.stmtOf y) (E.val y))
  (ir.padSpaceLate I (E.late y c)) c π

/-- **The honest environment reads like the source environment** at a value reading no generated
late value (`reader_honestEnvC_srcEnvL_of_noGen`). -/
theorem reader_honestEnvC_eq_of_noGen {w : ℕ} (hw : ir.NoGenRead w) :
    ir.reader HE w = ir.reader SE w :=
  reader_honestEnvC_srcEnvL_of_noGen R.gen E.stmtOf (E.committedC G) E.srcLate y c π hw

/-- **A predicate reading no generated late value holds at the honest environment** where it holds
at the source environment (`holds_honestC_of_src`). -/
theorem holds_honestEnvC_of_src {b : PredBody} (hb : ir.NoGenPred b)
    (h : ir.HoldsWith (ir.reader SE) b) : ir.HoldsWith (ir.reader HE) b :=
  holds_honestC_of_src R.gen E.stmtOf (E.committedC G) E.srcLate y c π hb h

include hM hreal in
/-- **The completeness rules' facts hold at the honest environment** off the execution's events:
the model facts (`hM`), the constants (`reader_of_constant`), the values bound to their digits
reading their expressions (`boundReads_of_boundRecs`); the
source predicates, the quotients' `in`s, the lookup rows and the pad copies' Boolean checks where
they hold at the source environment (`sourceSatAt_srcEnvC`, `holds_oneDigitQuot_srcEnvC`,
`holds_reconRowC`, `holds_topRowC`, `holds_padCopyBool_srcEnv`, `holds_commInC`,
`holds_commRowC`, `holds_specProductsC_srcEnv`, `holds_specRowC_srcEnv`, and
`holds_fieldRowC_srcEnv` from the execution's field equations), as they read no generated late
value; the MACs' predicates by `MacFormC.role_holds` from their source facts
(`MacBaseC.source_honestC`), and the tails of the MAC checks over the fields of characteristic `2`
by `TwoMacC.tail_honest` (`TwoMacC.source_honestC`). -/
theorem cEnvFacts_honestEnvC {x : ir.Valuation I} (hy : (x, y) ∈ relH) (hc : ∀ k, ¬ E.bad k x y c) :
    ir.CEnvFacts I primeNodes G (ir.reader HE) := by
  have hA := E.accepting x y hy c hc
  have hbd := E.bounded x y hy
  have hFE := E.fieldEqs x y hy c hc
  rw [E.stmt x y hy] at hA hbd hFE
  have hwf := hM.wf
  have hng : ∀ pid < ir.predicates.length, ir.noGenPredB (ir.predicate pid).body = true →
      ir.NoGenPred (ir.predicate pid).body := fun pid hpid h =>
    noGenPred_of_B hwf (hwf.bodyRefsOk (predicate_mem hpid)) h
  refine ⟨hM, fun v es hk i => reader_of_constant _ hk i, fun v hv x hk => ?_,
    fun q hq hs => ?_, fun m rid hrid h hn => ?_, fun p pid hpid h hn => ?_,
    fun st pid hpid h hd hi hr => ?_, fun pid hpid h hn => ?_, fun m j pid hpid h hm hn => ?_,
    fun m lks pid hpid h hn => ?_, fun k cv hk h hn => ?_, fun m pid hpid h hn => ?_,
    fun pid hpid h hn => ?_, fun st h => ?_⟩
  · exact boundReads_of_boundRecs hwf hM.lawful R.committed.boundRecs R.committed.digitLookups
      (e := HE) rfl v hv x hk
  · exact holds_honestEnvC_of_src R E y c π
      (noGenPred_of_inSource R.committed.sourceValid (predicate_mem hq) hs)
      ((sourceSatAt_srcEnvC hwf hM.registered hM.lawful R.committed hA π).preds _
        (predicate_mem hq) hs)
  · exact holds_honestEnvC_of_src R E y c π (hng rid hrid hn)
      (holds_oneDigitQuot_srcEnvC hwf hM.registered hM.lawful R.committed hA π hbd h)
  · refine holds_honestEnvC_of_src R E y c π (hng pid hpid hn) ?_
    unfold digitRowB at h
    split at h
    · rename_i d rec N r hb
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      obtain ⟨hF, hrow⟩ := h
      have hnat := recNat_srcEnvC hwf hM.registered hM.lawful R.committed hA π hb hF
      have hdig := digitsRead_srcEnvC hwf hM.registered hM.lawful R.committed hA π hb hF
      rcases hrow with ⟨hk, hrec | htop⟩ | ⟨-, hrec⟩
      · exact holds_reconRowC hwf hM.registered hM.lawful hF hrec hnat hdig
      · exact holds_topRowC hwf hM.registered hM.lawful hF hk htop hnat hdig
      · exact holds_reconRowC hwf hM.registered hM.lawful hF hrec hnat hdig
    · cases h
  · obtain ⟨hsrc, hw⟩ := MacBaseC.ofB_ivl hwf hreal h hi
    have hS := (MacBaseC.ofB primeNodes hwf hreal st h).source_honestC R.gen E.stmtOf
      (E.committedC G) E.srcLate y c π hwf hM.registered hM.lawful R.committed hA hbd rfl rfl hsrc hw
    exact MacFormC.ofB_role_holds hwf hreal h hd R.gen E.stmtOf (E.committedC G) E.srcLate y c π
      hM.registered hM.lawful hM.mac R.blinds ((macBaseFactsC_of_B h).macPow hM.mac)
      (macBaseFactsC_of_B h).tag1 hS (predicate_mem hpid) (roleC_of_macRoleCB hwf hreal h hd hr)
  · exact holds_honestEnvC_of_src R E y c π (hng pid hpid hn)
      (holds_padCopyBool_srcEnv _ _ _ c π h)
  · exact holds_honestEnvC_of_src R E y c π (hng pid hpid hn)
      (holds_commInC hwf hM.registered hM.lawful R.committed hA π h hm)
  · exact holds_honestEnvC_of_src R E y c π (hng pid hpid hn)
      (holds_commRowC hwf hM.registered hM.lawful R.committed hA π hbd h)
  · exact holds_honestEnvC_of_src R E y c π (hng _ (products_lt_of_specHonestCB hk h) hn)
      (holds_specProductsC_srcEnv hwf hM.registered hM.lawful R.committed hA π hbd hk h)
  · exact holds_honestEnvC_of_src R E y c π (hng pid hpid hn)
      (holds_specRowC_srcEnv hwf hM.registered hM.lawful R.committed hA π hbd h)
  · exact holds_honestEnvC_of_src R E y c π (hng pid hpid hn)
      (holds_fieldRowC_srcEnv hwf hM.registered hM.lawful R.committed hA π hFE h)
  · exact (TwoMacC.ofB primeNodes hwf hreal st h).tail_honest R.gen E.stmtOf (E.committedC G)
      E.srcLate y c π hwf hM.registered hM.lawful hM.mac R.blinds
      ((TwoMacC.ofB primeNodes hwf hreal st h).source_honestC R.gen E.stmtOf (E.committedC G)
        E.srcLate y c π hwf hM.registered hM.lawful R.committed hA rfl rfl
        (twoMacFactsC_of_B h).source)

include hM in
/-- **The node-typed values lie in their types at the honest environment** off the execution's
events: a source late value and a value that is not late as at the
source environment (`srcTypesHold_srcEnvC`), as they read no generated late value; a generated late
value is a natural (`lateTypes`). -/
theorem typesHold_honestEnvC {x : ir.Valuation I} (hy : (x, y) ∈ relH)
    (hc : ∀ k, ¬ E.bad k x y c) : ir.TypesHold HE := by
  have hA := E.accepting x y hy c hc
  rw [E.stmt x y hy] at hA
  have hT := srcTypesHold_srcEnvC hM.wf hM.registered hM.lawful R.committed hA π
  intro v hv hts i hi
  by_cases hl : ir.IsLate v
  · by_cases hs : ir.IsSourceValue v
    · rw [reader_honestEnvC_eq_of_noGen R E y c π
        (noGenRead_of_source R.committed.sourceValid hv hs)]
      exact hT v hv hts (fun _ => hs) i hi
    · obtain ⟨htag, hnat⟩ := R.lateTypes ⟨⟨v, hv⟩, hl⟩ hs hts
      rw [reader_of_late _ (kind_of_isLate hl),
        honestEnvC_late_eq R.gen E.stmtOf (E.committedC G) E.srcLate y c π _ hv hl hs]
      obtain ⟨n, hn⟩ := genValOf_natCast G
        (ir.srcEnvL I (E.stmtOf y) (E.committedC G y) (E.srcLate.late y c) c π) htag i
      rw [hn]
      exact hnat n
  · rw [reader_honestEnvC_eq_of_noGen R E y c π (R.typedNoLate v hv hts hl).noGen]
    exact hT v hv hts (fun h => absurd h hl) i hi

include hM hreal R in
/-- **A mixed group's late members' needles are naturals below its late histogram's size** at the
histograms' environment, off the execution's events: each reads a digit of a
MAC's tail at a site (`MixedGroupFactsC.members`), which the histograms' environment reads as the
honest environment (`reader_honestEnvC_histEnvOf`); the lower digit lies below the radix
(`DigitsMacC.low_honest`), the derived top digit at most `macTopMax` (`DigitsMacC.top_honest`), the
one-digit quotient at most `macQuotMax` (`OneDigitMacC.quot_honest`), the MAC's source facts from
the execution (`MacBaseC.source_honestC`). -/
theorem mixedLate_honestC {x : ir.Valuation I} (hy : (x, y) ∈ relH) (hc : ∀ k, ¬ E.bad k x y c)
    {t g v s : ℕ} (hF : ir.MixedGroupFactsC primeNodes G t g v s)
    (hs : (ir.groupOf t g).staticMult = some s) :
    ∀ z ∈ ir.histNeedles (ir.reader (ir.histEnvOf G (ir.srcEnvL I (E.stmtOf y) (E.committedC G y)
      (E.srcLate.late y c) c π))) (ir.chalField (ir.alphaOf t)) t g,
        ∃ k < (ir.value v).size, z = ((k : ℕ) : (I (ir.chalField (ir.alphaOf t))).K) := by
  have hA := E.accepting x y hy c hc
  have hbd := E.bounded x y hy
  rw [E.stmt x y hy] at hA hbd
  have hwf := hM.wf
  intro z hz
  unfold histNeedles at hz
  rw [hs] at hz
  simp only [Option.isSome_some, ite_true] at hz
  obtain ⟨m, hm, hz⟩ := List.mem_flatMap.1 hz
  obtain ⟨hm, hml⟩ := List.mem_filter.1 hm
  unfold memberVals at hz
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hz
  rw [List.mem_range] at hk
  rw [evalE_congr (f := ir.chalField (ir.alphaOf t)) fun w hw =>
    (reader_honestEnvC_histEnvOf R.gen E.stmtOf (E.committedC G) E.srcLate y c π
      (hF.needles m hm w hw)).symm]
  obtain ⟨st, hst⟩ := hF.members m hm hml
  unfold mixedMemberCB at hst
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hst
  obtain ⟨⟨h, hi⟩, hst⟩ := hst
  obtain ⟨hsrc, hw⟩ := MacBaseC.ofB_ivl hwf hreal h hi
  have hS := (MacBaseC.ofB primeNodes hwf hreal st h).source_honestC R.gen E.stmtOf
    (E.committedC G) E.srcLate y c π hwf hM.registered hM.lawful R.committed hA hbd rfl rfl hsrc hw
  rcases hst with ⟨⟨hd, hb⟩, htop⟩ | ⟨⟨hd, hb⟩, hq⟩
  · unfold lateMemberAtB at hb
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hb
    obtain ⟨⟨hf, hwd⟩, ⟨hlow, hr⟩ | htd⟩ := hb
    · rw [Expr.eq_of_beq hlow, hf, evalE_leaf]
      exact ⟨_, lt_of_lt_of_le (Nat.mod_lt _ (DigitsMacC.ofB primeNodes hwf hreal st h hd).radixPos) hr,
        (DigitsMacC.ofB primeNodes hwf hreal st h hd).low_honest R.gen E.stmtOf (E.committedC G)
          E.srcLate y c π (i := m.first + k)
          (show m.first + k < (ir.macUnitsAt st).width by omega)⟩
    · rw [Expr.eq_of_beq htd, hf]
      have h1 := (DigitsMacC.ofB primeNodes hwf hreal st h hd).top_honest R.gen E.stmtOf
        (E.committedC G) E.srcLate y c π hwf hM.registered hM.lawful hM.mac R.blinds hS
        (i := m.first + k) (show m.first + k < (ir.macUnitsAt st).width by omega)
      have hle := (DigitsMacC.ofB primeNodes hwf hreal st h hd).lhsNat_le R.gen E.stmtOf
        (E.committedC G) E.srcLate y c π hwf hM.registered hM.lawful R.blinds hS
        (i := m.first + k) (show m.first + k < (ir.macUnitsAt st).width by omega)
      unfold evalWith at h1
      refine ⟨_, lt_of_le_of_lt ?_ htop, h1⟩
      unfold macTopMax
      rw [← convMax_eq_macConvMaxAt (digitsMacFactsC_of_B hd).conv]
      exact Nat.div_le_div_right (Nat.div_le_div_right hle)
  · unfold lateMemberOneAtB at hb
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    obtain ⟨⟨hf, hwd⟩, hqe⟩ := hb
    rw [Expr.eq_of_beq hqe, hf]
    have h1 := (OneDigitMacC.ofB primeNodes hwf hreal st h hd).quot_honest R.gen E.stmtOf
      (E.committedC G) E.srcLate y c π hwf hM.registered hM.lawful hM.mac R.blinds hS
      (i := m.first + k) (show m.first + k < (ir.macUnitsAt st).width by omega)
    have hle := (OneDigitMacC.ofB primeNodes hwf hreal st h hd).lhsNat_le R.gen E.stmtOf
      (E.committedC G) E.srcLate y c π hwf hM.registered hM.lawful R.blinds hS
      (i := m.first + k) (show m.first + k < (ir.macUnitsAt st).width by omega)
    unfold evalWith at h1
    refine ⟨_, lt_of_le_of_lt ?_ hq, h1⟩
    unfold macQuotMax
    rw [← convMax_eq_macConvMaxAt (oneDigitMacFactsC_of_B hd).conv]
    exact Nat.div_le_div_right hle

include hM hreal in
/-- **Every group's histograms count its needles at the honest environment** off the execution's
events: a group without a late histogram as at the source
environment (`staticHistsCount_srcEnvC`), as its needles, its static histogram and its table's rows
read no late value; a group with one by `histogramsCount_lateC`, or beside a static one by
`histogramsCount_mixedC` (`mixedStatic_srcEnvC`, `mixedLate_honestC`), its table a range. -/
theorem histogramsCount_honestEnvC {x : ir.Valuation I} (hy : (x, y) ∈ relH)
    (hc : ∀ k, ¬ E.bad k x y c) : HistogramsCount HE := by
  have hA := E.accepting x y hy c hc
  have hP := E.packFree x y hy c hc
  rw [E.stmt x y hy] at hA hP
  intro t ht g hg
  rcases hlm : (ir.groupOf t g).lateMult with _ | v
  · obtain ⟨hn, hs, hrw⟩ := R.staticGroups t ht g hg hlm
    have hr : ∀ w, ir.NoLateRead w → ir.reader HE w = ir.reader SE w :=
      fun w hw => reader_honestEnvC_eq_of_noGen R E y c π hw.noGen
    have h := staticHistsCount_srcEnvC hM.wf hM.registered hM.lawful R.committed hA π hP t ht g hg
      hlm
    rw [honestCounts_congr (fun m hm w hw => hr w (hn m hm w hw)) fun w hw => hr w (hrw w hw)]
    unfold staticHist lateHist at h ⊢
    rw [histRead_congr fun v hv => hr v (hs v hv), histRead_congr (o := (ir.groupOf t g).lateMult)
      (rd' := ir.reader SE) fun v hv => by
        rw [hlm] at hv
        cases hv]
    exact h
  · rcases hsm : (ir.groupOf t g).staticMult with _ | s
    · have hF := R.lateGroups t ht g hg v hlm hsm
      rw [honestCounts_of_isRange hF.range]
      exact histogramsCount_lateC R.gen E.stmtOf (E.committedC G) E.srcLate y c π hlm hF.static
        hF.own hF.notSource hF.lt hF.late (kind_of_isLate hF.late) hF.size hF.field hF.needles
    · have hF := R.mixedGroups t ht g hg v s hlm hsm
      rw [honestCounts_of_isRange hF.range]
      exact histogramsCount_mixedC R.gen E.stmtOf (E.committedC G) E.srcLate y c π hlm hsm hF.own
        hF.notSource hF.lt hF.late hF.sizeLe hF.field hF.static.size hF.staticNoLate hF.staticNo
        hF.needles (fun a b ha hb hab => natCast_inj_of_le_char hM.registered hF.fieldLt
          hF.sizeChar ha hb hab)
        (fun j => mixedStatic_srcEnvC (x := E.stmtOf y) (s := E.val y) (l := E.late y c) hM.wf
          hM.registered hM.lawful R.committed hA π hF.static hF.range (by rw [hlm]; rfl) j)
        (mixedLate_honestC hM hreal R E y c π hy hc hF hsm)

include hM in
/-- **The digits of the two-sided and digit lookups are below their bases at the honest
environment** off the execution's events: they are committed cells, read alike at the honest and
the source environments (`reader_of_priv`), where they are below their bases
(`digitsBelow_srcEnvCC`). -/
theorem digitsBelow_honestEnvC {x : ir.Valuation I} (hy : (x, y) ∈ relH)
    (hc : ∀ k, ¬ E.bad k x y c) : DigitsBelow (ir.reader HE) := by
  have hA := E.accepting x y hy c hc
  rw [E.stmt x y hy] at hA
  intro pid hpid r hr hk u hu i hi
  obtain ⟨d, rec, N, hb⟩ := R.digitShape pid hpid r hr hk
  have hcell := privCellB_of_lookupFactsC hb (R.digitLookups pid hpid d rec N r hb hk) hu
  have h := digitsBelow_srcEnvCC hM.wf hM.registered hM.lawful R.committed hA π R.digitLookups R.digitShape pid hpid r hr
    hk u hu i hi
  rw [reader_of_priv _ (kind_of_privCellB hcell)] at h ⊢
  exact h

include hM hreal in
/-- **Every MAC's tag is honest at the honest environment**: every cross-field `equal` is the
predicate of a MAC site with a grouped, a one-digit or an ungrouped digit tail, or with a MAC check
over a field of characteristic `2` (`macs`), whose tag is honest (`MacFormC.macTag_honest`,
`TwoMacC.macTag_honest`). -/
theorem macTagsHonest_honestEnvC : ir.MacTagsHonest I HE := by
  intro p hp dx x dy y' k real hb _
  obtain ⟨pid, hpid, rfl⟩ := exists_index_of_mem hp
  obtain ⟨st, rfl, ⟨h, hd, -⟩ | h2⟩ := R.macs pid hpid dx x dy y' k real hb
  · have hT := MacFormC.ofB_macTag_honest hM.wf hreal h hd R.gen E.stmtOf (E.committedC G)
      E.srcLate y c π
    have e : PredBody.cross dx x dy y' k real =
        .cross (ir.macCross st.pid).dx (ir.macCross st.pid).x (ir.macCross st.pid).dy
          (ir.macCross st.pid).y (ir.macCross st.pid).k (ir.macCross st.pid).real :=
      hb.symm.trans (macBaseFactsC_of_B h).hb
    simp only [PredBody.cross.injEq] at e
    obtain ⟨rfl, rfl, -, -, -, rfl⟩ := e
    exact hT
  · have hT := (TwoMacC.ofB primeNodes hM.wf hreal st h2).macTag_honest R.gen E.stmtOf
      (E.committedC G) E.srcLate y c π
    have e : PredBody.cross dx x dy y' k real =
        .cross (ir.macCross st.pid).dx (ir.macCross st.pid).x (ir.macCross st.pid).dy
          (ir.macCross st.pid).y (ir.macCross st.pid).k (ir.macCross st.pid).real :=
      hb.symm.trans (twoMacFactsC_of_B h2).hb
    simp only [PredBody.cross.injEq] at e
    obtain ⟨rfl, rfl, -, -, -, rfl⟩ := e
    exact hT

end Env

/-- **The honest prover of a program from an execution of its source program and a completeness
certificate** (paper, `lem:core-red` (2)), for a program whose cross-field `equal`s have covered MAC
realizations (`hreal`): the committed values are the execution's phase-`0` values with the
committed generators' values (`genCommitted`), the late values the execution's with the late
generators' (`genLateOf`), which respect the exported reads (`respectsReads_genLateOf`), and the
completeness events the execution's. Off the events, at the honest environment, every predicate
holds by its completeness derivation (`holds_of_cderivs`, `cEnvFacts_honestEnvC`), the node-typed
values lie in their types (`typesHold_honestEnvC`), every group's histograms count its needles
(`histogramsCount_honestEnvC`), the digits are below their bases (`digitsBelow_honestEnvC`), the
MACs' tags are honest (`macTagsHonest_honestEnvC`), and the committed cells lie in their bases
(`honestCellsC_base`). -/
def HonestCore.ofCompletion (hM : ir.DerivModel I primeNodes) (hreal : ir.MacsRealizable primeNodes)
    {G : Gens} {D : CDerivations} (R : ir.CompletionFacts I primeNodes G D)
    (E : ir.SourceExecutionCore I relH) : ir.HonestCore I relH where
  val := E.committedC G
  late := ir.genLateOf I R.gen E.stmtOf (E.committedC G) E.srcLate
  respects y := respectsReads_genLateOf R.gen R.boundNoCopy R.covered E.stmtOf (E.committedC G)
    E.srcLate y
  bad := E.bad
  checks := E.checks
  bounded := E.bounded
  base x y hy c hc π d v i h := by
    have hA := E.accepting x y hy c hc
    rw [E.stmt x y hy] at hA
    exact honestCellsC_base hM.wf hM.lawful R.committed hA π h
  sat x y hy c π hc := by
    have hE := cEnvFacts_honestEnvC hM hreal R E y c π hy hc
    have hT := typesHold_honestEnvC hM R E y c π hy hc
    rw [E.stmt x y hy]
    refine ⟨fun p hp => ?_, hT⟩
    obtain ⟨q, hq, rfl⟩ := exists_index_of_mem hp
    exact holds_of_cderivs hE R.derivs q hq
  histograms x y hy c π hc := by
    have h := histogramsCount_honestEnvC hM hreal R E y c π hy hc
    rw [E.stmt x y hy]
    exact h
  digits x y hy c π hc := by
    have h := digitsBelow_honestEnvC hM R E y c π hy hc
    rw [E.stmt x y hy]
    exact h
  blinds := R.blinds
  tags x y hy c π _ := by
    rw [E.stmt x y hy]
    exact macTagsHonest_honestEnvC hM hreal R E y c π

/-- **The completeness error of the honest prover from a certificate over the prover's coins** is
the execution's (`HonestCore.ofCompletion_coinComplete`): the events are the execution's. -/
theorem HonestCore.ofCompletion_coinComplete (hM : ir.DerivModel I primeNodes)
    (hreal : ir.MacsRealizable primeNodes) {G : Gens} {D : CDerivations}
    (R : ir.CompletionFacts I primeNodes G D) (E : ir.SourceExecutionCore I relH) {J Ω : Type}
    [Fintype Ω] [Nonempty Ω] {relJ : Set (ir.Valuation I × J)} {inp : J → Ω → Inp}
    {errc : ir.Valuation I → ℝ≥0} (h : E.CoinComplete relJ inp errc) :
    (HonestCore.ofCompletion hM hreal R E).CoinComplete relJ inp errc := h


/-- **The honest strategy of a program from an execution of its source program and a completeness
certificate**: the honest prover from the certificate (`HonestCore.ofCompletion`) with the
execution's per-phase errors (`ofCompletion_δ`). -/
def HonestStrategy.ofCompletion (hM : ir.DerivModel I primeNodes)
    (hreal : ir.MacsRealizable primeNodes) {G : Gens} {D : CDerivations}
    (R : ir.CompletionFacts I primeNodes G D) (E : ir.SourceExecution I relH) :
    ir.HonestStrategy I relH where
  toHonestCore := HonestCore.ofCompletion hM hreal R E.toSourceExecutionCore
  δ := E.δ
  badBound := E.badBound

/-- **The completeness errors of the honest strategy from a certificate are the execution's.** -/
theorem HonestStrategy.ofCompletion_δ (hM : ir.DerivModel I primeNodes)
    (hreal : ir.MacsRealizable primeNodes) {G : Gens} {D : CDerivations}
    (R : ir.CompletionFacts I primeNodes G D) (E : ir.SourceExecution I relH) :
    (HonestStrategy.ofCompletion hM hreal R E).δ = E.δ := rfl

end

end GordieHowe.RealizedProgram
