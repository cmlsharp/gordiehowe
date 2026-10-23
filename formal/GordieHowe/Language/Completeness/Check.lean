-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Completeness.Honest
public import GordieHowe.Language.Honest.Check
public import GordieHowe.Language.Honest.CheckP

@[expose] public section

/-!
# GordieHowe: the checker of a completeness certificate

`GordieHowe.RealizedProgram.completionB` decides `CompletionFacts` (`completionFacts_of_B`, given
the program and its source part well formed, which the soundness proof checks once) for a program,
its certificate (generators `G`, derivations `D`) and nodes `L` known to contain `1`, in three
zipped passes: over the values (`valueCB`: the source part's facts, the values bound to their
digits, the generators' facts, the committed cells, the node-typed realization values and
generated late values), over the predicates
(`predCB`: the lookups, the MACs) and over the tables' groups (`groupCB`: the static, the late and
the mixed histograms), plus the program-wide checks of the soundness side (`boundNoCopyB`,
`genReadsCoveredCB`, `typedNoLateB`, `blindsB`, `staticGroupNoLateB`) and the derivations
(`cderivsB`). Each value's, predicate's and group's check reads the generator or the MAC site its
entry names (`Gens.at`); nothing is searched. The value passes visit the values and the generators
together (`allIdx2`: `valueCV`, `coveredCV`, and `boundNoCopyV`, `typedNoLateV` of
`GordieHowe/Language/Honest/CheckValues.lean`), reading each value and its generator from the lists
rather than by a lookup per value.
-/

namespace GordieHowe.RealizedProgram

open Export ProofSystem.PhaseLayout IOP Range

/-- **Whether a generator is a static histogram's**, decidably. -/
instance (x : Gen) : Decidable (∀ t g, x ≠ .staticHist t g) := by
  cases x
  case staticHist t g => exact isFalse fun h => h t g rfl
  all_goals exact isTrue fun _ _ h => Gen.noConfusion h

/-- **Whether a generator is a late histogram's**, decidably. -/
instance (x : Gen) : Decidable (∀ t g, x ≠ .lateHist t g) := by
  cases x
  case lateHist t g => exact isFalse fun h => h t g rfl
  all_goals exact isTrue fun _ _ h => Gen.noConfusion h

section

variable (ir : RealizedProgram) {I : Interp}

instance (G : Gens) (t g h : ℕ) : Decidable (ir.StaticGroupFactsC G t g h) :=
  decidable_of_iff (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
    ⟨fun ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ => ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩,
     fun h => ⟨h.cell, h.size, h.field, h.notSource, h.own, h.needles, h.rows, h.packed⟩⟩

/-- **A tag's pad space is the whole field**, as a check at value `v`. -/
def tagFullCB (G : Gens) (v : ℕ) : Bool :=
  match G.at v with
  | .tag _ =>
    match (ir.value v).padSpace with
    | .full => true
    | _ => false
  | _ => true

/-- **A late value's pad space contains the naturals by a node of `L`, its domain is a domain of the
program and it has pad cells there**, as a check at value `v`. -/
def lateGenCB (L : List (ℕ × String)) (v : ℕ) : Bool :=
  !decide (ir.IsLate v) ||
    (ir.padNatB L v && decide ((ir.value v).domain < ir.domains.length) &&
      !ir.isCellValue (ir.value v).domain v && ir.isLateOf (ir.value v).domain v)

/-- **Value `v` is generated as no MAC tag**, as a check. -/
def _root_.GordieHowe.RealizedProgram.Gens.notTagAt (G : Gens) (v : ℕ) : Bool :=
  match G.at v with
  | .tag _ => false
  | _ => true

/-- **A node-typed generated late value is generated as no MAC tag and its type contains the
naturals by a node of `L`** (`CompletionFacts.lateTypes`), as a check at value `v`. -/
def genLateTypeCB (L : List (ℕ × String)) (G : Gens) (v : ℕ) : Bool :=
  !decide (ir.IsLate v) || decide (ir.IsSourceValue v) || !((ir.value v).typeSource == .node) ||
    (G.notTagAt v && ir.natTypedInB L v)

/-- **The completeness checks at value `v`**: the source part's facts (no pad copy, no message, the
late values' pad spaces), a value bound to its digits a source value and the record of a two-sided
or digit lookup (`boundRecsB`), the generators' facts, the committed cells' nodes, the node-typed
realization values and generated late values. -/
def valueCB (L : List (ℕ × String)) (G : Gens) (v : ℕ) : Bool :=
  ir.srcNoPadCopyB v && ir.srcNoMessageB v && ir.srcLatePadB v && ir.boundRecsB v &&
    ir.tagFullCB G v && ir.lateGenCB L v && ir.cellB L v && ir.realTypeB L v &&
    ir.genLateTypeCB L G v

/-- **A two-sided or digit lookup `q` has one record, a range and its facts at the generators `G`**,
its digits generated as its digits (`DigitLookupFactsC`) or, when its record is a quotient digit
(`commRecOf?`), as the committed digits of the quotient digit its first digit's generator names
(`commLookupCB`), as a check. -/
def digitLookupCB (G : Gens) (q : ℕ) : Bool :=
  match lookupOf? (ir.predicateT q).body with
  | some r =>
    !(r.kind == .twoSided || r.kind == .digits) ||
      match (ir.predicateT q).body with
      | .mem d [rec] (.range N) (.lookup r') =>
        decide (ir.DigitLookupFactsC G q d rec N r') ||
          (ir.commRecOf? q).isSome && match G.at (r'.digitValues.getD 0 0) with
          | .commDigit m j _ _ => ir.commLookupCB G q m j
          | _ => false
      | _ => false
  | none => true

variable (primeNodes : ℕ → List String) in
/-- **A cross-field `equal` `q` is the predicate of a MAC site whose MAC, tail and interval
facts check, or whose MAC check over a field of characteristic `2` checks**
(`CompletionFacts.macs`), as a check over the two sites of `q`. -/
def macCB (G : Gens) (q : ℕ) : Bool :=
  !ir.isCrossB q || [false, true].any fun b =>
    ir.macBaseCB primeNodes G ⟨q, b⟩ && ir.macTailCB primeNodes G ⟨q, b⟩ &&
      ir.macIvlB primeNodes ⟨q, b⟩ || ir.twoMacCB primeNodes G ⟨q, b⟩

variable (primeNodes : ℕ → List String) in
/-- **The completeness checks at predicate `q`**: the source values' intervals read source
predicates, a two-sided or digit lookup with its facts, a cross-field `equal` with its MAC. -/
def predCB (G : Gens) (q : ℕ) : Bool :=
  ir.ivlSourceB q && ir.digitLookupCB G q && ir.macCB primeNodes G q

/-- **The needles of group `g` of table `t` read only late values of the program that are generated
as no late histogram** (`LateGroupFactsC.needles`), as a check through the reads table. -/
def needlesLateCB (G : Gens) (t g : ℕ) : Bool :=
  (ir.members t g).all fun m => (ir.exprNodes (ir.needleExpr m.pred m.needle)).all fun w =>
    (ir.readsT.getD w []).all fun r =>
      match r with
      | .late u => decide (u < ir.values.length ∧ ir.IsLate u) &&
        decide (∀ t' g', G.at u ≠ .lateHist t' g')
      | _ => true

variable (primeNodes : ℕ → List String) in
/-- **A group with the late histogram `v` and the static histogram `s` has its facts**
(`MixedGroupFactsC`), as a check: the late members' MAC digits through the MAC sites
(`mixedMemberCB`). -/
def mixedGroupCB (G : Gens) (t g v s : ℕ) : Bool :=
  decide (G.at v = .lateHist t g) && !decide (ir.IsSourceValue v) &&
    decide (v < ir.values.length) && decide (ir.IsLate v) &&
    decide ((ir.value v).size ≤ ir.tableSize t) &&
    decide (ir.valueField v = ir.chalField (ir.alphaOf t)) && decide (ir.IsRange t) &&
    decide (ir.StaticGroupFactsC G t g s) && ir.noLateReadB s &&
    (ir.members t g).all (fun m => ir.memberReadsLate m ||
      (ir.exprNodes (ir.needleExpr m.pred m.needle)).all ir.noLateReadB) &&
    ir.needlesLateCB G t g && decide (ir.chalField (ir.alphaOf t) < ir.fields.length) &&
    decide (ir.tableSize t ≤ ir.charOf (ir.chalField (ir.alphaOf t))) &&
    (ir.members t g).all (fun m => !ir.memberReadsLate m ||
      ir.sites.any fun st => ir.mixedMemberCB primeNodes G t v st m)

variable (primeNodes : ℕ → List String) in
/-- **The completeness checks at group `g` of table `t`**: a late histogram with its facts, alone
(`LateGroupFactsC`) or beside a static one (`mixedGroupCB`); without one, a static histogram with
its facts (`StaticGroupFactsC`), or no members. -/
def groupCB (G : Gens) (t g : ℕ) : Bool :=
  match (ir.groupOf t g).lateMult with
  | some v =>
    ((ir.groupOf t g).staticMult.isNone && decide (G.at v = .lateHist t g) &&
      !decide (ir.IsSourceValue v) && decide (v < ir.values.length) && decide (ir.IsLate v) &&
      decide ((ir.value v).size = ir.tableSize t) &&
      decide (ir.valueField v = ir.chalField (ir.alphaOf t)) && decide (ir.IsRange t) &&
      ir.needlesLateCB G t g) ||
    match (ir.groupOf t g).staticMult with
    | some s => ir.mixedGroupCB primeNodes G t g v s
    | none => false
  | none =>
    match (ir.groupOf t g).staticMult with
    | none => (ir.members t g).isEmpty
    | some h => decide (ir.StaticGroupFactsC G t g h)

/-! ## The value passes in one zipped pass

`valueCB`, `genReadsCoveredCB`, `boundNoCopyB` and `typedNoLateB` read value `v` through
`ir.value v` and its generator through `G.at v`, each a lookup of `v` steps. The checks below visit
the values and the generators together (`allIdx2`), read the visited value and generator from the
lists, any other generator through the table `toTrie G`, and equal the checks above at
`ir.value v` and `G.at v` (`valueCV_eq`, `coveredCV_eq`). -/

/-- **Generator `g` is no MAC tag's** (`Gens.notTagAt`, on the generator). -/
def _root_.GordieHowe.RealizedProgram.Gen.notTag (g : Gen) : Bool :=
  match g with
  | .tag _ => false
  | _ => true

/-- `tagFullCB G v`, on value `x` and generator `g`. -/
def tagFullCV (x : Value) (g : Gen) : Bool :=
  match g with
  | .tag _ =>
    match x.padSpace with
    | .full => true
    | _ => false
  | _ => true

/-- `lateGenCB L v`, on value `x`. -/
def lateGenCV (L : List (ℕ × String)) (x : Value) : Bool :=
  !ir.isLateV x ||
    (ir.padNatV L x && decide (x.domain < ir.domains.length) && !cellValueV x.domain x &&
      ir.lateOfV x.domain x)

/-- `genLateTypeCB L G v`, on value `x` and generator `g`. -/
def genLateTypeCV (L : List (ℕ × String)) (x : Value) (g : Gen) : Bool :=
  !ir.isLateV x || decide (x.role = .source) || !(x.typeSource == .node) ||
    (g.notTag && ir.natTypedV L x)

/-- `valueCB L G v`, on value `x` and generator `g`. -/
def valueCV (L : List (ℕ × String)) (v : ℕ) (x : Value) (g : Gen) : Bool :=
  srcNoPadCopyV v x && srcNoMessageV v x && ir.srcLatePadV v x && ir.boundRecsV v x &&
    tagFullCV x g && ir.lateGenCV L x && ir.cellV L v x && ir.realTypeV L v x &&
    ir.genLateTypeCV L x g

/-- **The pad-space check on a value is `padNatB`.** -/
theorem padNatV_eq (L : List (ℕ × String)) (v : ℕ) : ir.padNatV L (ir.value v) = ir.padNatB L v :=
  rfl

/-- **The type check on a value is `natTypedInB`.** -/
theorem natTypedV_eq (L : List (ℕ × String)) (v : ℕ) :
    ir.natTypedV L (ir.value v) = ir.natTypedInB L v :=
  rfl

/-- **`valueCV` at value `v` and its generator is `valueCB`.** -/
theorem valueCV_eq (L : List (ℕ × String)) (G : Gens) (v : ℕ) :
    ir.valueCV L v (ir.value v) (G.at v) = ir.valueCB L G v := by
  simp only [valueCV, valueCB, srcNoPadCopyV_eq, srcNoMessageV_eq, srcLatePadV_eq,
    boundRecsV_eq, cellV_eq, realTypeV_eq]
  congr 1
  · congr 1
    · congr 2
      · simp only [lateGenCV, lateGenCB, isLateV_eq, padNatV_eq, isLateOf_eq]
        rfl
  · simp only [genLateTypeCV, genLateTypeCB, isLateV_eq, natTypedV_eq]
    rfl

/-- **A generator's check at value `u` reads only `G.at u`.** -/
theorem genCoveredCB_at (G : Gens) (rs : List Read) (u : ℕ) :
    ir.genCoveredCB [(toTrie G).getD u default] rs 0 = ir.genCoveredCB G rs u := by
  rw [toTrie_getD_eq]
  rfl

/-- `histCoveredCB G rs v`, on generator `g`, the other generators read through `GT`. -/
def histCoveredCV (GT : NatTrie Gen) (rs : List Read) (g : Gen) : Bool :=
  match g with
  | .lateHist t g => (ir.members t g).all fun m =>
      (ir.exprNodes (ir.needleExpr m.pred m.needle)).all fun w =>
        ir.srcCoveredB rs w && (ir.readsT.getD w []).all fun r =>
          match r with
          | .late u => ir.genCoveredCB [GT.getD u default] rs 0
          | _ => true
  | _ => true

/-- `genReadsCoveredCB G`'s check at value `v`, on value `x` and generator `g`, the other
generators read through `GT`. -/
def coveredCV (GT : NatTrie Gen) (_ : ℕ) (x : Value) (g : Gen) : Bool :=
  !ir.isLateV x || (ir.genCoveredCB [g] x.reads 0 && ir.histCoveredCV GT x.reads g)

/-- **`coveredCV` at value `v` and its generator is `genReadsCoveredCB`'s check.** -/
theorem coveredCV_eq (G : Gens) (v : ℕ) :
    ir.coveredCV (toTrie G) v (ir.value v) (G.at v) =
      (!decide (ir.IsLate v) ||
        (ir.genCoveredCB G (ir.value v).reads v && ir.histCoveredCB G (ir.value v).reads v)) := by
  simp only [coveredCV, isLateV_eq]
  congr 2
  unfold histCoveredCV histCoveredCB
  cases G.at v
  all_goals first
    | rfl
    | (simp only [genCoveredCB_at]
       congr 1)

/-- **The zipped value pass is `valueCB`'s.** -/
theorem allValuesB_valueCB_of_V {L : List (ℕ × String)} {G : Gens}
    (h : allIdx2 (ir.valueCV L) .none ir.values G 0 = true) :
    ir.allValuesB (ir.valueCB L G) = true := by
  unfold allValuesB
  rw [List.all_eq_true]
  intro v hv
  have := allIdx2_sound _ _ _ _ _ h v (List.mem_range.1 hv)
  rw [Nat.zero_add] at this
  rw [← valueCV_eq]
  exact this

/-- **The zipped coverage pass is `genReadsCoveredCB`.** -/
theorem genReadsCoveredCB_of_V {G : Gens}
    (h : allIdx2 (ir.coveredCV (toTrie G)) .none ir.values G 0 = true) :
    ir.genReadsCoveredCB G = true := by
  unfold genReadsCoveredCB
  rw [List.all_eq_true]
  intro v hv
  have := allIdx2_sound _ _ _ _ _ h v (List.mem_range.1 hv)
  rw [Nat.zero_add] at this
  rw [← coveredCV_eq]
  exact this

/-- **The checker of a completeness certificate** at the nodes `L`. -/
def completionB (primeNodes : ℕ → List String) (L : List (ℕ × String)) (G : Gens)
    (D : CDerivations) : Bool :=
  allIdx2 (ir.valueCV L) .none ir.values G 0 && ir.allPredsB (ir.predCB primeNodes G) &&
    ir.allGroupsB (ir.groupCB primeNodes G) && allIdx ir.boundNoCopyV ir.values 0 &&
    allIdx2 (ir.coveredCV (toTrie G)) .none ir.values G 0 &&
    allIdx ir.typedNoLateV ir.values 0 && ir.allPredsB ir.blindsB &&
    ir.allGroupsB ir.staticGroupNoLateB && ir.cderivsB primeNodes G D

end

section Sound

variable {ir : RealizedProgram} {I : Interp} {primeNodes : ℕ → List String}

/-- **A two-sided or digit lookup that passes `digitLookupCB`** has one record, a range and its
facts, of either form. -/
theorem digitLookupCB_spec {G : Gens} {q : ℕ} {r : LookupRealization}
    (h : ir.digitLookupCB G q = true) (hr : lookupOf? (ir.predicate q).body = some r)
    (hk : r.kind = .twoSided ∨ r.kind = .digits) :
    ∃ d rec N, (ir.predicate q).body = .mem d [rec] (.range N) (.lookup r) ∧
      (ir.DigitLookupFactsC G q d rec N r ∨ ∃ m j, ir.commLookupCB G q m j = true) := by
  unfold digitLookupCB at h
  rw [predicateT_eq, hr] at h
  have hk' : (r.kind == .twoSided || r.kind == .digits) = true := by
    rcases hk with h | h <;> simp [h]
  simp only [hk', Bool.not_true, Bool.false_or] at h
  split at h
  · rename_i d rec N r' hb
    rw [hb] at hr
    simp only [lookupOf?, Option.some.injEq] at hr
    subst hr
    refine ⟨d, rec, N, hb, ?_⟩
    rcases Bool.or_eq_true_iff.1 h with h | h
    · exact .inl (of_decide_eq_true h)
    · refine .inr ?_
      rw [Bool.and_eq_true] at h
      obtain ⟨-, h⟩ := h
      split at h
      · rename_i m j _ _ _
        exact ⟨m, j, h⟩
      · cases h
  · cases h

/-- **A two-sided or digit lookup that passes `digitLookupCB` and whose record is no quotient
digit** (`commRecOf? q = none`) has its facts, its digits generated as its digits. -/
theorem digitLookupCB_noComm {G : Gens} {q d N : ℕ} {rec : Expr} {r : LookupRealization}
    (h : ir.digitLookupCB G q = true)
    (hb : (ir.predicate q).body = .mem d [rec] (.range N) (.lookup r))
    (hk : r.kind = .twoSided ∨ r.kind = .digits) (hn : (ir.commRecOf? q).isNone = true) :
    ir.DigitLookupFactsC G q d rec N r := by
  unfold digitLookupCB at h
  rw [predicateT_eq, hb] at h
  have hk' : (r.kind == .twoSided || r.kind == .digits) = true := by
    rcases hk with h | h <;> simp [h]
  have hs : (ir.commRecOf? q).isSome = false := by
    revert hn
    cases ir.commRecOf? q <;> simp
  simp only [lookupOf?, hk', Bool.not_true, Bool.false_or, hs, Bool.false_and, Bool.or_false] at h
  exact of_decide_eq_true h

/-- **A group's needles that pass `needlesLateCB`** read only late values of the program that are
generated as no late histogram. -/
theorem needlesLateC_of_B (hwf : ir.WellFormed) {G : Gens} {t g : ℕ}
    (h : ir.needlesLateCB G t g = true) :
    ∀ m ∈ ir.members t g, ∀ w ∈ ir.exprNodes (ir.needleExpr m.pred m.needle),
      ∀ u, Read.late u ∈ ir.nodeReads ir.fuel w →
        (u < ir.values.length ∧ ir.IsLate u) ∧ ∀ t' g', G.at u ≠ .lateHist t' g' := by
  intro m hm w hw u hu
  unfold needlesLateCB at h
  have := List.all_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1 h m hm) w hw) _
    ((mem_readsT hwf w _).1 hu)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact this

/-- **A group with a late histogram that passes `groupCB`** has its facts (`LateGroupFactsC`). -/
theorem lateGroupFactsC_of_B (hwf : ir.WellFormed) {G : Gens} {t g v : ℕ}
    (h : ir.groupCB primeNodes G t g = true) (hv : (ir.groupOf t g).lateMult = some v)
    (hs : (ir.groupOf t g).staticMult = none) :
    ir.LateGroupFactsC G t g v := by
  unfold groupCB at h
  rw [hv, hs] at h
  simp only [Option.isNone_none, Bool.true_and, Bool.or_false, Bool.and_eq_true,
    decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h2, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨hs, h2, h3, h4, h5, h6, h7, h8, needlesLateC_of_B hwf h9⟩

/-- **A group with both histograms that passes `groupCB`** passes `mixedGroupCB`. -/
theorem mixedGroupCB_of_groupCB {G : Gens} {t g v s : ℕ} (h : ir.groupCB primeNodes G t g = true)
    (hv : (ir.groupOf t g).lateMult = some v) (hs : (ir.groupOf t g).staticMult = some s) :
    ir.mixedGroupCB primeNodes G t g v s = true := by
  unfold groupCB at h
  rw [hv, hs] at h
  simpa using h

/-- **A group with both histograms that passes `mixedGroupCB`** has its facts
(`MixedGroupFactsC`). -/
theorem mixedGroupFactsC_of_B (hwf : ir.WellFormed) {G : Gens} {t g v s : ℕ}
    (h : ir.mixedGroupCB primeNodes G t g v s = true) : ir.MixedGroupFactsC primeNodes G t g v s := by
  unfold mixedGroupCB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not,
    List.all_eq_true, Bool.or_eq_true, List.any_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, noLateRead_of_B hwf h9, fun m hm hl w hw => ?_,
    needlesLateC_of_B hwf h11, h12, h13, fun m hm hl => ?_⟩
  · rcases h10 m hm with h | h
    · rw [hl] at h
      cases h
    · exact noLateRead_of_B hwf (h w hw)
  · rcases h14 m hm with h | ⟨st, -, hst⟩
    · rw [hl] at h
      cases h
    · exact ⟨st, hst⟩

/-- **A cross-field `equal` that passes `macCB`** is the predicate of a MAC site whose MAC, tail and
interval facts check, or whose MAC check over a field of characteristic `2` checks. -/
theorem macs_of_macCB {G : Gens} {pid : ℕ} (h : ir.macCB primeNodes G pid = true)
    {dx dy : ℕ} {x y : Expr} {k : CrossKind} {real : MacRealization}
    (hb : (ir.predicate pid).body = .cross dx x dy y k real) :
    ∃ st : MacSite, st.pid = pid ∧
      ((ir.macBaseCB primeNodes G st = true ∧ ir.macTailCB primeNodes G st = true ∧
        ir.macIvlB primeNodes st = true) ∨ ir.twoMacCB primeNodes G st = true) := by
  unfold macCB at h
  rw [isCrossB_of_body hb] at h
  simp only [Bool.not_true, Bool.false_or, List.any_eq_true, List.mem_cons,
    List.not_mem_nil, or_false, Bool.or_eq_true, Bool.and_eq_true] at h
  obtain ⟨b, -, ⟨⟨h1, h2⟩, h3⟩ | h4⟩ := h
  · exact ⟨⟨pid, b⟩, rfl, .inl ⟨h1, h2, h3⟩⟩
  · exact ⟨⟨pid, b⟩, rfl, .inr h4⟩

/-- **The facts of a completeness certificate that checks** (`completionB`), at nodes known to
contain `1`, for a well-formed program whose source part is well formed (`hwf`, `hsv`, facts the
soundness proof shares). -/
theorem completionFacts_of_B {L : List (ℕ × String)} (hO : OneNodes I L) (hwf : ir.WellFormed)
    (hsv : ir.SourceValid) {G : Gens} {D : CDerivations}
    (h : ir.completionB primeNodes L G D = true) :
    ir.CompletionFacts I primeNodes G D := by
  unfold completionB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hval, hpred⟩, hgrp⟩, hbnc⟩, hcov⟩, htnl⟩, hbl⟩, hsg⟩, hder⟩ := h
  replace hval := ir.allValuesB_valueCB_of_V hval
  replace hbnc := ir.boundNoCopyV_iff.1 hbnc
  replace hcov := ir.genReadsCoveredCB_of_V hcov
  replace htnl := ir.typedNoLateV_iff.1 htnl
  have hv : ∀ v < ir.values.length, ir.valueCB L G v = true := fun v hv => of_allValuesB hval hv
  have hq : ∀ q < ir.predicates.length, ir.predCB primeNodes G q = true := fun q hq =>
    of_allPredsB hpred hq
  have hq3 : ∀ q < ir.predicates.length, ir.ivlSourceB q = true ∧ ir.digitLookupCB G q = true ∧
      ir.macCB primeNodes G q = true := fun q hlt => by
    have := hq q hlt
    unfold predCB at this
    simp only [Bool.and_eq_true] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  have hdl : ∀ pid < ir.predicates.length, ∀ r, lookupOf? (ir.predicate pid).body = some r →
      (r.kind = .twoSided ∨ r.kind = .digits) → ∃ d rec N,
        (ir.predicate pid).body = .mem d [rec] (.range N) (.lookup r) ∧
          (ir.DigitLookupFactsC G pid d rec N r ∨ ∃ m j, ir.commLookupCB G pid m j = true) :=
    fun pid hlt r hr hk =>
      digitLookupCB_spec (hq3 pid hlt).2.1 hr hk
  have hvs : ∀ v < ir.values.length, ir.srcNoPadCopyB v = true ∧ ir.srcNoMessageB v = true ∧
      ir.srcLatePadB v = true ∧ ir.boundRecsB v = true ∧
      ir.tagFullCB G v = true ∧ ir.lateGenCB L v = true ∧
      ir.cellB L v = true ∧ ir.realTypeB L v = true ∧ ir.genLateTypeCB L G v = true :=
    fun v hlt => by
    have := hv v hlt
    unfold valueCB at this
    simp only [Bool.and_eq_true] at this
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := this
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  -- the generators' facts at a late value
  have hlg : ∀ l : ir.Late, ir.padNatB L l.1 = true ∧
      (ir.value l.1).domain < ir.domains.length ∧
      ir.isCellValue (ir.value l.1).domain l.1 = false ∧
      ir.isLateOf (ir.value l.1).domain l.1 = true := fun l => by
    have := (hvs l.1 l.1.2).2.2.2.2.2.1
    unfold lateGenCB at this
    have hL : ir.IsLate l.1 := l.2
    simp only [hL, decide_true, Bool.not_true, Bool.false_or, Bool.and_eq_true,
      Bool.not_eq_true', decide_eq_true_eq] at this
    exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩
  refine
    { committed :=
        { sourceValid := hsv
          srcNoPadCopy := fun u hu hs => by
            have hB := (hvs u hu).1
            unfold srcNoPadCopyB at hB
            simpa [hs] using hB
          srcNoMessage := fun v hlt hs => by
            have hB := (hvs v hlt).2.1
            unfold srcNoMessageB at hB
            simpa [hs] using hB
          srcLatePads := fun v hlt hs hl => by
            have hB := (hvs v hlt).2.2.1
            unfold srcLatePadB at hB
            simpa [hs, hl] using hB
          ivlSource := fun q hlt => (hq3 q hlt).1
          boundRecs := fun v hlt hb => by
            have hB := (hvs v hlt).2.2.2.1
            unfold boundRecsB at hB
            simpa [hb] using hB
          digitLookups := fun pid hlt d rec N r hb hk hn =>
            digitLookupCB_noComm (hq3 pid hlt).2.1 hb hk hn
          groups := fun t ht g hg hlm => by
            have hB := of_allGroupsB hgrp ht hg
            unfold groupCB at hB
            rcases hs : (ir.groupOf t g).staticMult with _ | h'
            · simp only [hlm, hs] at hB
              exact .inl ⟨rfl, List.isEmpty_iff.1 hB⟩
            · simp only [hlm, hs] at hB
              exact .inr ⟨h', rfl, of_decide_eq_true hB⟩
          cellNodes := fun v hlt hc => by
            have hB := (hvs v hlt).2.2.2.2.2.2.1
            unfold cellB at hB
            simp only [hc, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hB
            exact hB.1
          oneMem := oneMem_of_cellNodeIn hO fun v hlt hc => by
            have hB := (hvs v hlt).2.2.2.2.2.2.1
            unfold cellB at hB
            simp only [hc, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hB
            exact hB.2
          realTypes := realTypes_of_natTypedIn hO fun v hlt hts hl hs => by
            have hB := (hvs v hlt).2.2.2.2.2.2.2.1
            unfold realTypeB at hB
            simpa [hts, hl, hs] using hB }
      gen :=
        { tagFull := fun v hlt p hp => by
            have hB := (hvs v hlt).2.2.2.2.1
            unfold tagFullCB at hB
            rw [hp] at hB
            revert hB
            cases (ir.value v).padSpace <;> simp
          natCast := fun l n => by
            have hp := (hlg l).1
            unfold padNatB at hp
            unfold FieldInterp.space
            split
            · exact AddSubgroup.mem_top _
            · rename_i S hS
              rw [hS, List.contains_iff_mem] at hp
              simpa using AddSubgroup.nsmul_mem _ (hO _ hp) n
          domain := fun l => (hlg l).2.1
          padCells := fun l i hi =>
            (ir.mem_cellKeys_pad).2 ⟨l.1.2, by simpa using (hlg l).2.2.1, (hlg l).2.2.2, hi⟩ }
      boundNoCopy := boundNoCopy_of_B hbnc
      covered := genReadsCoveredC_of_B hwf hcov
      lateTypes := fun l hs hts => by
        have hB := (hvs l.1 l.1.2).2.2.2.2.2.2.2.2
        have hL : ir.IsLate l.1 := l.2
        unfold genLateTypeCB at hB
        simp only [hL, hs, hts, decide_true, decide_false, Bool.not_true, Bool.false_or,
          beq_self_eq_true, Bool.and_eq_true] at hB
        refine ⟨fun p hp => ?_, (natTyped_of_natTypedInB hO hB.2).inType⟩
        have h1 := hB.1
        unfold Gens.notTagAt at h1
        rw [hp] at h1
        cases h1
      typedNoLate := typedNoLate_of_B hwf htnl
      staticGroups := staticGroups_of_B hwf hsg
      lateGroups := fun t ht g hg v hlm hs =>
        lateGroupFactsC_of_B hwf (of_allGroupsB hgrp ht hg) hlm hs
      mixedGroups := fun t ht g hg v s hlm hs =>
        mixedGroupFactsC_of_B hwf (mixedGroupCB_of_groupCB (of_allGroupsB hgrp ht hg) hlm hs)
      macs := fun pid hlt dx x dy y k real hb => macs_of_macCB (hq3 pid hlt).2.2 hb
      blinds := blinds_of_B hbl
      digitLookups := fun pid hlt d rec N r hb hk => by
        obtain ⟨d', rec', N', hb', hF⟩ := hdl pid hlt r (by rw [hb]; rfl) hk
        rw [hb] at hb'
        simp only [PredBody.mem.injEq, List.cons.injEq, and_true, InSet.range.injEq] at hb'
        obtain ⟨rfl, rfl, rfl, -⟩ := hb'
        exact hF
      digitShape := fun pid hlt r hr hk => by
        obtain ⟨d, rec, N, hb, -⟩ := hdl pid hlt r hr hk
        exact ⟨d, rec, N, hb⟩
      derivs := hder }

end Sound

section Ready

variable {ir : RealizedProgram} {I : Interp} {primeNodes : ℕ → List String}

variable (ir I primeNodes) in
/-- **The ready data of the honest strategy from a completeness certificate** (generators `G`,
derivations `D`): the nodes `nodes` known to contain `1`
(`OneNodes`), the program well formed, the interpretation's registry, integer readings and MAC
model, every table valid (`TableOk`, from the realization's validity), the cross-field `equal`s'
covered MAC realizations (`MacsRealizable`), the source part well formed, and the check
`completionB`. -/
structure CompletionReady (G : Gens) (D : CDerivations) where
  /-- The nodes known to contain `1`. -/
  nodes : List (ℕ × String)
  /-- They contain `1`. -/
  oneNodes : OneNodes I nodes
  /-- The program is well formed. -/
  wf : ir.WellFormed
  /-- The interpretation's registry. -/
  registered : I.Registered ir
  /-- The interpretation's integer readings. -/
  lawful : I.Lawful ir primeNodes
  /-- The MAC model. -/
  macModel : I.MacModel ir
  /-- Every table is valid. -/
  tables : ∀ t < ir.tables.length, ir.TableOk t
  /-- The cross-field `equal`s have covered MAC realizations. -/
  macsRealizable : ir.MacsRealizable primeNodes
  /-- The source part is well formed. -/
  sourceValid : ir.SourceValid
  /-- The check. -/
  ok : ir.completionB primeNodes nodes G D = true

variable {G : Gens} {D : CDerivations}

/-- **The model facts of ready data** (`DerivModel`). -/
theorem CompletionReady.model (R : ir.CompletionReady I primeNodes G D) :
    ir.DerivModel I primeNodes :=
  ⟨R.wf, R.registered, R.lawful, R.tables, R.macModel⟩

/-- **The facts of a completeness certificate passing the check** (`completionFacts_of_B`). -/
theorem CompletionReady.facts (R : ir.CompletionReady I primeNodes G D) :
    ir.CompletionFacts I primeNodes G D :=
  completionFacts_of_B R.oneNodes R.wf R.sourceValid R.ok

variable {Inp : Type} {relH : Set (ir.Valuation I × Inp)}

/-- **The honest strategy of a program whose completeness certificate passes the check, from an
execution of its source program** (`HonestStrategy.ofCompletion` at `CompletionReady.facts`). -/
def HonestStrategy.ofCompletionReady (R : ir.CompletionReady I primeNodes G D)
    (E : ir.SourceExecution I relH) : ir.HonestStrategy I relH :=
  HonestStrategy.ofCompletion R.model R.macsRealizable R.facts E

/-- **The completeness errors of the honest strategy from ready data are the execution's.** -/
theorem HonestStrategy.ofCompletionReady_δ (R : ir.CompletionReady I primeNodes G D)
    (E : ir.SourceExecution I relH) : (HonestStrategy.ofCompletionReady R E).δ = E.δ := rfl

end Ready

end GordieHowe.RealizedProgram
