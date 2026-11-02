-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Completeness.Honest
public import GordieHowe.Language.Completeness.Reader
public import GordieHowe.Language.Completeness.Roles
public import GordieHowe.Language.Honest.Check
public import GordieHowe.Language.Honest.CheckP
public import GordieHoweNative.Language.Completeness.Check

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
(`cderivsB`). Each value's, predicate's and group's check reads the generator its entry names
(`Gens.at`) or the MAC site a structure record names (`macSiteAt`: a cross-field `equal`'s record
by its first predicate, `Structure.gadgetAt`; a late member's through its predicate's completeness
step); nothing is searched. The value passes visit the values and the generators
together (`allIdx2`: `valueCV`, `coveredCV`, and `boundNoCopyV`, `typedNoLateV` of
`GordieHowe/Language/Honest/CheckValues.lean`), reading each value and its generator from the lists
rather than by a lookup per value.

The definitions are in `GordieHoweNative/Language/Completeness/Check.lean`
(the compiled library `GordieHoweNative`); this module has their lemmas.
-/

namespace GordieHowe.RealizedProgram

open Export ProofSystem.PhaseLayout IOP Range

section

variable (ir : RealizedProgram) {I : Interp}

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
late values' pad spaces), a value bound to its digits a source value and the record of the two-sided
or digit lookup its structure record names (`boundRecsV`), the generators' facts, the committed
cells' nodes, the node-typed realization values and generated late values. -/
def valueCB (L : List (ℕ × String)) (G : Gens) (S : Structure) (v : ℕ) : Bool :=
  ir.srcNoPadCopyB v && ir.srcNoMessageB v && ir.srcLatePadB v &&
    ir.boundRecsV (toTrie G) S.boundRecTab v (ir.value v) &&
    ir.tagFullCB G v && ir.lateGenCB L v && ir.cellB L v && ir.realTypeB L v &&
    ir.genLateTypeCB L G v

variable (primeNodes : ℕ → List String) in
/-- **`siteCB` as a check whose failure names the record `g` and the slot `i`** of the site
(`StructReason.siteFacts`). -/
def siteCE (S : Structure) (G : Gens) (g i : ℕ) (st : MacSite) : Except StructFailure Unit :=
  if ir.charOf (ir.domainField (ir.siteDom st)) = 2 then
    Twin.guardE (ir.twoMacCB primeNodes G st) ⟨g, i, .siteFacts⟩
  else
    Twin.seqE (Twin.guardE (ir.macBaseCB primeNodes S G st) ⟨g, i, .siteFacts⟩) <|
      Twin.seqE (Twin.guardE (ir.macTailCB G st) ⟨g, i, .siteFacts⟩)
        (Twin.guardE (ir.macIvlB primeNodes S st) ⟨g, i, .siteFacts⟩)

theorem okB_siteCE (primeNodes : ℕ → List String) (S : Structure) (G : Gens) (g i : ℕ)
    (st : MacSite) :
    Twin.okB (ir.siteCE primeNodes S G g i st) = ir.siteCB primeNodes S G st := by
  unfold siteCE siteCB
  split <;> simp only [Twin.okB_seqE, Twin.okB_guardE, Bool.and_assoc]

variable (primeNodes : ℕ → List String) in
/-- **`macCB` as a check whose failure names what is missing**: no record for `q`
(`StructReason.uncovered`), no site at the record (`macSiteAtE`), a site of another `equal`
(`StructReason.wrongSite`) or the site's facts (`siteCE`). -/
def macCE (S : Structure) (G : Gens) (q : ℕ) : Except StructFailure Unit :=
  if ir.isCrossB q then
    match S.gadgetAt.get? q with
    | some g =>
      Twin.thenE (ir.macSiteAtE S g (ir.ySlot q)) fun st =>
        Twin.seqE (Twin.guardE (st.pid == q) ⟨g, 0, .wrongSite⟩)
          (ir.siteCE primeNodes S G g (ir.ySlot q) st)
    | none => .error ⟨q, 0, .uncovered⟩
  else .ok ()

/-! ## The checkers at the program

Each checker below is its generic form (`CReader.…`, `PReader.…`) at the program's reader. Its
equation lemma states it through the program's own definitions; the shared verdicts of a site
read at the site the record names (`siteCheckAt_of_some`). -/

/-- **`CReader.mixedMemberCB` at the program, at a site**, is `mixedMemberCB`. -/
theorem mixedMemberCB_ofProgram (primeNodes : ℕ → List String) (S : Structure) (G : Gens)
    {g i t v : ℕ} {st : MacSite} (h : ir.macSiteAt S g i = some st) (m : Member) :
    @CReader.mixedMemberCB ir (CReader.ofProgram ir primeNodes S G) g i t v st m =
      ir.mixedMemberCB primeNodes S G t v st m := by
  simp only [CReader.mixedMemberCB, CReader.ofProgram_site, siteCheckAt_of_some h, SiteCheck.eval,
    CReader.ofProgram_value]
  rfl

/-- **`CReader.siteCB` at the program, at a site**, is `siteCB`. -/
theorem siteCB_ofProgram (primeNodes : ℕ → List String) (S : Structure) (G : Gens) {g i : ℕ}
    {st : MacSite} (h : ir.macSiteAt S g i = some st) :
    @CReader.siteCB ir (CReader.ofProgram ir primeNodes S G) g i st =
      ir.siteCB primeNodes S G st := by
  simp only [CReader.siteCB, CReader.ofProgram_site, siteCheckAt_of_some h, SiteCheck.eval]
  rfl

/-- **`macCB` at the program.** -/
theorem macCB_eq (primeNodes : ℕ → List String) (S : Structure) (G : Gens) (q : ℕ) :
    ir.macCB primeNodes S G q = (!ir.isCrossB q ||
      match S.gadgetAt.get? q with
      | some g =>
        match ir.macSiteAt S g (ir.ySlot q) with
        | some st => st.pid == q && ir.siteCB primeNodes S G st
        | none => false
      | none => false) := by
  simp only [macCB, CReader.macCB]
  congr 1
  cases S.gadgetAt.get? q with
  | none => rfl
  | some g =>
    dsimp only
    cases hst : ir.macSiteAt S g (ir.ySlot q) with
    | none => rfl
    | some st => exact congrArg (st.pid == q && ·) (siteCB_ofProgram ir primeNodes S G hst)

/-- **`predCB` at the program.** -/
theorem predCB_eq (primeNodes : ℕ → List String) (S : Structure) (G : Gens) (q : ℕ) :
    ir.predCB primeNodes S G q =
      (ir.ivlSourceB q && ir.digitLookupCB G q && ir.macCB primeNodes S G q) :=
  rfl

/-- **`needlesLateCB` at the program.** -/
theorem needlesLateCB_eq (G : Gens) (t g : ℕ) :
    ir.needlesLateCB G t g =
      (ir.members t g).all fun m => (ir.exprNodes (ir.needleExpr m.pred m.needle)).all fun w =>
        (ir.readsT.getD w []).all fun r =>
          match r with
          | .late u => decide (u < ir.values.length ∧ ir.IsLate u) &&
            decide (∀ t' g', G.at u ≠ .lateHist t' g')
          | _ => true :=
  rfl

/-- **`mixedGroupCB` at the program.** -/
theorem mixedGroupCB_eq (primeNodes : ℕ → List String) (S : Structure) (G : Gens)
    (D : CDerivations) (t g v s : ℕ) :
    ir.mixedGroupCB primeNodes S G D t g v s =
      (decide (G.at v = .lateHist t g) && !decide (ir.IsSourceValue v) &&
        decide (v < ir.values.length) && decide (ir.IsLate v) &&
        decide ((ir.value v).size ≤ ir.tableSize t) &&
        decide (ir.valueField v = ir.chalField (ir.alphaOf t)) && decide (ir.IsRange t) &&
        decide (ir.StaticGroupFactsC G t g s) && ir.noLateReadB s &&
        (ir.members t g).all (fun m => ir.memberReadsLate m ||
          (ir.exprNodes (ir.needleExpr m.pred m.needle)).all ir.noLateReadB) &&
        ir.needlesLateCB G t g && decide (ir.chalField (ir.alphaOf t) < ir.fields.length) &&
        decide (ir.tableSize t ≤ ir.charOf (ir.chalField (ir.alphaOf t))) &&
        (ir.members t g).all (fun m => !ir.memberReadsLate m ||
          match D.derivs[m.pred]? with
          | some [.macRow g' i _] =>
            match ir.macSiteAt S g' i with
            | some st => ir.mixedMemberCB primeNodes S G t v st m
            | none => false
          | _ => false)) := by
  simp only [mixedGroupCB, CReader.mixedGroupCB]
  congr 1
  congr 1
  funext m
  congr 1
  cases D.derivs[m.pred]? with
  | none => rfl
  | some l =>
    rcases l with _ | ⟨c, _ | ⟨c', l⟩⟩
    · rfl
    · cases c <;> try rfl
      rename_i g' i _
      dsimp only
      cases hst : ir.macSiteAt S g' i with
      | none => rfl
      | some st => exact mixedMemberCB_ofProgram ir primeNodes S G hst m
    · cases c <;> rfl

/-- **`groupCB` at the program.** -/
theorem groupCB_eq (primeNodes : ℕ → List String) (S : Structure) (G : Gens) (D : CDerivations)
    (t g : ℕ) :
    ir.groupCB primeNodes S G D t g =
      match (ir.groupOf t g).lateMult with
      | some v =>
        ((ir.groupOf t g).staticMult.isNone && decide (G.at v = .lateHist t g) &&
          !decide (ir.IsSourceValue v) && decide (v < ir.values.length) && decide (ir.IsLate v) &&
          decide ((ir.value v).size = ir.tableSize t) &&
          decide (ir.valueField v = ir.chalField (ir.alphaOf t)) && decide (ir.IsRange t) &&
          ir.needlesLateCB G t g) ||
        match (ir.groupOf t g).staticMult with
        | some s => ir.mixedGroupCB primeNodes S G D t g v s
        | none => false
      | none =>
        match (ir.groupOf t g).staticMult with
        | none => (ir.members t g).isEmpty
        | some h => decide (ir.StaticGroupFactsC G t g h) :=
  rfl

/-- **`histCoveredCV` at the program.** -/
theorem histCoveredCV_eq (GT : NatTrie Gen) (MT : NatTrie ℕ) (rs : List Read) (g : Gen) :
    ir.histCoveredCV GT MT rs g =
      match g with
      | .lateHist t g => (ir.members t g).all fun m =>
          (ir.exprNodes (ir.needleExpr m.pred m.needle)).all fun w =>
            ir.srcCoveredB MT rs w && (ir.readsT.getD w []).all fun r =>
              match r with
              | .late u => ir.genCoveredCB [GT.getD u default] MT rs 0
              | _ => true
      | _ => true :=
  rfl

/-- **`coveredCV` at the program.** -/
theorem coveredCV_def (GT : NatTrie Gen) (MT : NatTrie ℕ) (v : ℕ) (x : Value) (g : Gen) :
    ir.coveredCV GT MT v x g =
      (!ir.isLateV x || (ir.genCoveredCB [g] MT x.reads 0 && ir.histCoveredCV GT MT x.reads g)) :=
  rfl

/-- **`typedNoLateL` at the program.** -/
theorem typedNoLateL_eq (v : ℕ) (x : Value) (rs : List Read) :
    ir.typedNoLateL v x rs =
      (!(x.typeSource == .node) || ir.isLateV x ||
        rs.all fun r =>
          match r with
          | .late u => !(decide (u < ir.values.length) && ir.isLateV (ir.valueT u))
          | _ => true) :=
  rfl

/-- **`completionB` at the program.** -/
theorem completionB_eq (primeNodes : ℕ → List String) (L : List (ℕ × String)) (S : Structure)
    (G : Gens) (D : CDerivations) :
    ir.completionB primeNodes L S G D =
      (allIdx2 (ir.valueCV L (toTrie G) S.boundRecTab) .none ir.values G 0 &&
        ir.allPredsB (ir.predCB primeNodes S G) &&
        ir.allGroupsB (ir.groupCB primeNodes S G D) && allIdx ir.boundNoCopyV ir.values 0 &&
        allIdx2 (ir.coveredCV (toTrie G) S.messageTab) .none ir.values G 0 &&
        allIdx2 ir.typedNoLateL [] ir.values ir.readsL 0 && ir.allPredsB ir.blindsB &&
        ir.allGroupsB ir.staticGroupNoLateB && ir.cderivsB primeNodes S G D &&
        allIdx ir.typeRoleV ir.values 0 && ir.messageRecsB S) :=
  rfl

/-- **Compiled code runs the completeness checker at the context built once** (`completionBA`):
the context's reader is the program's (`CReader.ofCtx_build`). -/
@[csimp] theorem completionB_csimp : @completionB = @completionBA := by
  funext ir primeNodes L S G D
  show @CReader.completionB ir (CReader.ofProgram ir primeNodes S G) primeNodes L S G D =
    @CReader.completionB ir (CReader.ofCtx (CCtx.build ir primeNodes S G)) primeNodes L S G D
  rw [CReader.ofCtx_build]

theorem okB_macCE (primeNodes : ℕ → List String) (S : Structure) (G : Gens) (q : ℕ) :
    Twin.okB (ir.macCE primeNodes S G q) = ir.macCB primeNodes S G q := by
  rw [macCB_eq]
  unfold macCE macSiteAt
  cases ir.isCrossB q
  · rfl
  · simp only [Bool.not_true, Bool.false_or, if_true]
    cases S.gadgetAt.get? q with
    | some g =>
      rw [Twin.okB_thenE]
      cases h : ir.macSiteAtE S g (ir.ySlot q) <;>
        simp [h, Except.toOption, Twin.okB_seqE, Twin.okB_guardE, okB_siteCE]
    | none => rfl

/-- **The `macSite` record `G` (index `g`) has its kind's slots**, as a check whose failure names
the record and the slot (frozen §3.8's per-kind rule; no theorem reads it): no parts; a
cross-field `equal` first (`notCross`), then its tails, one per site (`ySlot`), each a realization
of the `equal`; the parameters `[macField, chunks, width]` of its MAC; the values `[tag, key]`,
`key` holding the MAC's key challenge. -/
def macSiteE (g : ℕ) (G : Gadget) : Except StructFailure Unit :=
  Twin.seqE (Twin.guardE (G.kind == .macSite) ⟨g, 0, .notMacSite⟩) <|
  Twin.seqE (Twin.guardE G.parts.isEmpty ⟨g, 0, .slotMismatch⟩) <|
  match G.preds with
  | [] => .error ⟨g, 0, .noSlot⟩
  | p :: ts =>
    Twin.seqE (Twin.guardE (ir.isCrossB p) ⟨g, 0, .notCross⟩) <|
    Twin.seqE (Twin.guardE (ts.length == ir.ySlot p) ⟨g, ts.length, .noSlot⟩) <|
    Twin.seqE (Twin.guardE (G.params == [(ir.macCross p).real.macField,
      (ir.macCross p).real.chunks, (ir.macCross p).real.width]) ⟨g, 0, .slotMismatch⟩) <|
    Twin.seqE (Twin.guardE (match G.values with
      | [tg, kv] => tg == (ir.macCross p).real.tag && decide (kv < ir.values.length) &&
          match (ir.value kv).kind with
          | .challenge c => c == (ir.macCross p).real.key
          | _ => false
      | _ => false) ⟨g, 0, .slotMismatch⟩)
    (Twin.allE (fun j t => Twin.guardE ((ir.predicateT t).role == .realization p)
      ⟨g, j, .roleMismatch⟩) 1 ts)

/-- **The `macSite` record's slots check** (`okB` of `macSiteE`). -/
def macSiteB (g : ℕ) (G : Gadget) : Bool := Twin.okB (ir.macSiteE g G)

/-! ## The value passes in one zipped pass

`valueCB`, `genReadsCoveredCB`, `boundNoCopyB` and `typedNoLateB` read value `v` through
`ir.value v` and its generator through `G.at v`, each a lookup of `v` steps. The checks below visit
the values and the generators together (`allIdx2`), read the visited value and generator from the
lists, any other generator through the table `toTrie G`, and equal the checks above at
`ir.value v` and `G.at v` (`valueCV_eq`, `coveredCV_eq`). -/

/-- **The pad-space check on a value is `padNatB`.** -/
theorem padNatV_eq (L : List (ℕ × String)) (v : ℕ) : ir.padNatV L (ir.value v) = ir.padNatB L v :=
  rfl

/-- **The type check on a value is `natTypedInB`.** -/
theorem natTypedV_eq (L : List (ℕ × String)) (v : ℕ) :
    ir.natTypedV L (ir.value v) = ir.natTypedInB L v :=
  rfl

/-- **`valueCV` at value `v` and its generator is `valueCB`.** -/
theorem valueCV_eq (L : List (ℕ × String)) (G : Gens) (S : Structure) (v : ℕ) :
    ir.valueCV L (toTrie G) S.boundRecTab v (ir.value v) (G.at v) = ir.valueCB L G S v := by
  simp only [valueCV, valueCB, srcNoPadCopyV_eq, srcNoMessageV_eq, srcLatePadV_eq,
    cellV_eq, realTypeV_eq]
  congr 1
  · congr 1
    · congr 2
      · simp only [lateGenCV, lateGenCB, isLateV_eq, padNatV_eq, isLateOf_eq]
        rfl
  · simp only [genLateTypeCV, genLateTypeCB, isLateV_eq, natTypedV_eq]
    rfl

/-- **A generator's check at value `u` reads only `G.at u`.** -/
theorem genCoveredCB_at (G : Gens) (MT : NatTrie ℕ) (rs : List Read) (u : ℕ) :
    ir.genCoveredCB [(toTrie G).getD u default] MT rs 0 = ir.genCoveredCB G MT rs u := by
  have h : Gens.at [(toTrie G).getD u default] 0 = G.at u := by
    rw [Gens.at_eq_getD, Gens.at_eq_getD, toTrie_getD_eq]
    rfl
  rw [genCoveredCB_eq, genCoveredCB_eq]
  unfold genInputsOf
  rw [h]

/-- **`coveredCV` at value `v` and its generator is `genReadsCoveredCB`'s check.** -/
theorem coveredCV_eq (G : Gens) (MT : NatTrie ℕ) (v : ℕ) :
    ir.coveredCV (toTrie G) MT v (ir.value v) (G.at v) =
      (!decide (ir.IsLate v) ||
        (ir.genCoveredCB G MT (ir.value v).reads v &&
          ir.histCoveredCB G MT (ir.value v).reads v)) := by
  simp only [coveredCV_def, isLateV_eq]
  congr 2

/-- **The zipped value pass is `valueCB`'s.** -/
theorem allValuesB_valueCB_of_V {L : List (ℕ × String)} {G : Gens} {S : Structure}
    (h : allIdx2 (ir.valueCV L (toTrie G) S.boundRecTab) .none ir.values G 0 = true) :
    ir.allValuesB (ir.valueCB L G S) = true := by
  unfold allValuesB
  rw [List.all_eq_true]
  intro v hv
  have := allIdx2_sound _ _ _ _ _ h v (List.mem_range.1 hv)
  rw [Nat.zero_add, ← value_eq_getD, ← Gens.at_eq_getD] at this
  rw [← valueCV_eq]
  exact this

/-- **The zipped coverage pass is `genReadsCoveredCB`.** -/
theorem genReadsCoveredCB_of_V {G : Gens} {MT : NatTrie ℕ}
    (h : allIdx2 (ir.coveredCV (toTrie G) MT) .none ir.values G 0 = true) :
    ir.genReadsCoveredCB G MT = true := by
  unfold genReadsCoveredCB
  rw [List.all_eq_true]
  intro v hv
  have := allIdx2_sound _ _ _ _ _ h v (List.mem_range.1 hv)
  rw [Nat.zero_add, ← value_eq_getD, ← Gens.at_eq_getD] at this
  rw [← coveredCV_eq]
  exact this

/-- **The zipped pass of `typedNoLateL` is `typedNoLateV`'s.** -/
theorem typedNoLateV_of_L (h : allIdx2 ir.typedNoLateL [] ir.values ir.readsL 0 = true) :
    allIdx ir.typedNoLateV ir.values 0 = true := by
  rw [allIdx_iff]
  intro j hj
  have := allIdx2_sound _ _ _ _ _ h j hj
  rw [getD_readsL, Nat.zero_add] at this
  rw [Nat.zero_add]
  exact this

end

section Sound

variable {ir : RealizedProgram} {I : Interp} {primeNodes : ℕ → List String} {S : Structure}

/-- **A two-sided or digit lookup that passes `digitLookupCB`** has one record, a range and its
facts, of either form. -/
theorem digitLookupCB_spec {G : Gens} {q : ℕ} {r : LookupRealization}
    (h : ir.digitLookupCB G q = true) (hr : lookupOf? (ir.predicate q).body = some r)
    (hk : r.kind = .twoSided ∨ r.kind = .digits) :
    ∃ d rec N, (ir.predicate q).body = .mem d [rec] (.range N) (.lookup r) ∧
      (ir.DigitLookupFactsC G q d rec N r ∨ ∃ m j, ir.commLookupCB G q m j = true) := by
  unfold digitLookupCB digitLookupCE at h
  rw [predicateT_eq, hr] at h
  have hk' : (r.kind == .twoSided || r.kind == .digits) = true := by
    rcases hk with h | h <;> simp [h]
  dsimp only at h
  rw [hk'] at h
  dsimp only at h
  split at h
  · rename_i d rec N r' hb
    rw [hb] at hr
    simp only [lookupOf?, Option.some.injEq] at hr
    subst hr
    refine ⟨d, rec, N, hb, ?_⟩
    split at h
    · rename_i m j _
      rw [Twin.okB_guardE] at h
      exact .inr ⟨m, j, h⟩
    · rw [Twin.okB_guardE] at h
      exact .inl (of_decide_eq_true h)
  · cases h

/-- **A two-sided or digit lookup that passes `digitLookupCB` and whose digits are generated as no
quotient digit's** (`G.commOf? r = none`) has its facts, its digits generated as its digits. -/
theorem digitLookupCB_noComm {G : Gens} {q d N : ℕ} {rec : Expr} {r : LookupRealization}
    (h : ir.digitLookupCB G q = true)
    (hb : (ir.predicate q).body = .mem d [rec] (.range N) (.lookup r))
    (hk : r.kind = .twoSided ∨ r.kind = .digits) (hn : G.commOf? r = none) :
    ir.DigitLookupFactsC G q d rec N r := by
  unfold digitLookupCB digitLookupCE at h
  rw [predicateT_eq, hb] at h
  have hk' : (r.kind == .twoSided || r.kind == .digits) = true := by
    rcases hk with h | h <;> simp [h]
  simp only [lookupOf?, hk', hn, Twin.okB_guardE] at h
  exact of_decide_eq_true h

/-- **A group's needles that pass `needlesLateCB`** read only late values of the program that are
generated as no late histogram. -/
theorem needlesLateC_of_B (hwf : ir.WellFormed) {G : Gens} {t g : ℕ}
    (h : ir.needlesLateCB G t g = true) :
    ∀ m ∈ ir.members t g, ∀ w ∈ ir.exprNodes (ir.needleExpr m.pred m.needle),
      ∀ u, Read.late u ∈ ir.nodeReads ir.fuel w →
        (u < ir.values.length ∧ ir.IsLate u) ∧ ∀ t' g', G.at u ≠ .lateHist t' g' := by
  intro m hm w hw u hu
  rw [needlesLateCB_eq] at h
  have := List.all_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1 h m hm) w hw) _
    ((mem_readsT hwf w _).1 hu)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact this

/-- **A group with a late histogram that passes `groupCB`** has its facts (`LateGroupFactsC`). -/
theorem lateGroupFactsC_of_B (hwf : ir.WellFormed) {G : Gens} {D : CDerivations} {t g v : ℕ}
    (h : ir.groupCB primeNodes S G D t g = true) (hv : (ir.groupOf t g).lateMult = some v)
    (hs : (ir.groupOf t g).staticMult = none) :
    ir.LateGroupFactsC G t g v := by
  rw [groupCB_eq] at h
  rw [hv, hs] at h
  simp only [Option.isNone_none, Bool.true_and, Bool.or_false, Bool.and_eq_true,
    decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h2, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨hs, h2, h3, h4, h5, h6, h7, h8, needlesLateC_of_B hwf h9⟩

/-- **A group with both histograms that passes `groupCB`** passes `mixedGroupCB`. -/
theorem mixedGroupCB_of_groupCB {G : Gens} {D : CDerivations} {t g v s : ℕ}
    (h : ir.groupCB primeNodes S G D t g = true)
    (hv : (ir.groupOf t g).lateMult = some v) (hs : (ir.groupOf t g).staticMult = some s) :
    ir.mixedGroupCB primeNodes S G D t g v s = true := by
  rw [groupCB_eq] at h
  rw [hv, hs] at h
  simpa using h

/-- **A group with both histograms that passes `mixedGroupCB`** has its facts
(`MixedGroupFactsC`). -/
theorem mixedGroupFactsC_of_B (hwf : ir.WellFormed) {G : Gens} {D : CDerivations} {t g v s : ℕ}
    (h : ir.mixedGroupCB primeNodes S G D t g v s = true) :
    ir.MixedGroupFactsC primeNodes S G t g v s := by
  rw [mixedGroupCB_eq] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not,
    List.all_eq_true, Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, noLateRead_of_B hwf h9, fun m hm hl w hw => ?_,
    needlesLateC_of_B hwf h11, h12, h13, fun m hm hl => ?_⟩
  · rcases h10 m hm with h | h
    · rw [hl] at h
      cases h
    · exact noLateRead_of_B hwf (h w hw)
  · rcases h14 m hm with h | h
    · rw [hl] at h
      cases h
    · split at h
      · split at h
        · exact ⟨_, h⟩
        · cases h
      · cases h

/-- **A cross-field `equal` that passes `macCB`** is the predicate of a MAC site whose MAC, tail and
interval facts check, or whose MAC check over a field of characteristic `2` checks. -/
theorem macs_of_macCB {G : Gens} {pid : ℕ} (h : ir.macCB primeNodes S G pid = true)
    {dx dy : ℕ} {x y : Expr} {k : CrossKind} {real : MacRealization}
    (hb : (ir.predicate pid).body = .cross dx x dy y k real) :
    ∃ st : MacSite, st.pid = pid ∧
      ((ir.macBaseCB primeNodes S G st = true ∧ ir.macTailCB G st = true ∧
        ir.macIvlB primeNodes S st = true) ∨ ir.twoMacCB primeNodes G st = true) := by
  rw [macCB_eq] at h
  rw [isCrossB_of_body hb] at h
  simp only [Bool.not_true, Bool.false_or] at h
  split at h
  · split at h
    · rename_i st _
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨hp, hs⟩ := h
      refine ⟨st, hp, ?_⟩
      unfold siteCB at hs
      split at hs
      · exact .inr hs
      · simp only [Bool.and_eq_true] at hs
        exact .inl ⟨hs.1.1, hs.1.2, hs.2⟩
    · cases h
  · cases h

/-- **The facts of a completeness certificate that checks** (`completionB`), at nodes known to
contain `1`, for a well-formed program whose source part is well formed (`hwf`, `hsv`, facts the
soundness proof shares). -/
theorem completionFacts_of_B {L : List (ℕ × String)} (hO : OneNodes I L) (hwf : ir.WellFormed)
    (hsv : ir.SourceValid) {S : Structure} {G : Gens} {D : CDerivations}
    (h : ir.completionB primeNodes L S G D = true) :
    ir.CompletionFacts I primeNodes S G D := by
  rw [completionB_eq] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hval, hpred⟩, hgrp⟩, hbnc⟩, hcov⟩, htnl⟩, hbl⟩, hsg⟩, hder⟩, htr⟩, hmsg⟩ := h
  replace hval := ir.allValuesB_valueCB_of_V hval
  replace hbnc := ir.boundNoCopyV_iff.1 hbnc
  replace hcov := ir.genReadsCoveredCB_of_V hcov
  replace htnl := ir.typedNoLateV_iff.1 (ir.typedNoLateV_of_L htnl)
  have hv : ∀ v < ir.values.length, ir.valueCB L G S v = true := fun v hv =>
    of_allValuesB hval hv
  have hq : ∀ q < ir.predicates.length, ir.predCB primeNodes S G q = true := fun q hq =>
    of_allPredsB hpred hq
  have hq3 : ∀ q < ir.predicates.length, ir.ivlSourceB q = true ∧ ir.digitLookupCB G q = true ∧
      ir.macCB primeNodes S G q = true := fun q hlt => by
    have := hq q hlt
    rw [predCB_eq] at this
    simp only [Bool.and_eq_true] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  have hdl : ∀ pid < ir.predicates.length, ∀ r, lookupOf? (ir.predicate pid).body = some r →
      (r.kind = .twoSided ∨ r.kind = .digits) → ∃ d rec N,
        (ir.predicate pid).body = .mem d [rec] (.range N) (.lookup r) ∧
          (ir.DigitLookupFactsC G pid d rec N r ∨ ∃ m j, ir.commLookupCB G pid m j = true) :=
    fun pid hlt r hr hk =>
      digitLookupCB_spec (hq3 pid hlt).2.1 hr hk
  have hvs : ∀ v < ir.values.length, ir.srcNoPadCopyB v = true ∧ ir.srcNoMessageB v = true ∧
      ir.srcLatePadB v = true ∧ ir.boundRecsV (toTrie G) S.boundRecTab v (ir.value v) = true ∧
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
          typeRoles := typeRoles_of_typeRoleV htr
          boundRecs := fun v hlt hb => ir.boundRecsV_sound (hvs v hlt).2.2.2.1 hb
          digitLookups := fun pid hlt d rec N r hb hk hn =>
            digitLookupCB_noComm (hq3 pid hlt).2.1 hb hk hn
          groups := fun t ht g hg hlm => by
            have hB := of_allGroupsB hgrp ht hg
            rw [groupCB_eq] at hB
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
      covered := genReadsCoveredC_of_B hwf (messagesCovered_of_B hmsg) hcov
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

variable {ir : RealizedProgram} {I : Interp} {primeNodes : ℕ → List String} {S : Structure}

variable (ir I primeNodes) in
/-- **The ready data of the honest strategy from a completeness certificate** (generators `G`,
derivations `D`): the nodes `nodes` known to contain `1`
(`OneNodes`), the program well formed, the interpretation's registry, integer readings and MAC
model, every table valid (`TableOk`, from the realization's validity), the cross-field `equal`s'
covered MAC realizations (`MacsRealizable`), the source part well formed, the check `completionB`
and the honest roles' check (`honestRolesB`). -/
structure CompletionReady (S : Structure) (G : Gens) (D : CDerivations) where
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
  ok : ir.completionB primeNodes nodes S G D = true
  /-- The honest roles' check. -/
  rolesOk : ir.honestRolesB nodes S = true

variable {S : Structure} {G : Gens} {D : CDerivations}

/-- **The model facts of ready data** (`DerivModel`). -/
theorem CompletionReady.model (R : ir.CompletionReady I primeNodes S G D) :
    ir.DerivModel I primeNodes :=
  ⟨R.wf, R.registered, R.lawful, R.tables, R.macModel⟩

/-- **The honest roles of ready data** (`honestRoles_of_B`). -/
theorem CompletionReady.roles (R : ir.CompletionReady I primeNodes S G D) :
    ir.HonestRoles R.nodes S :=
  honestRoles_of_B R.rolesOk

/-- **The facts of a completeness certificate passing the check** (`completionFacts_of_B`). -/
theorem CompletionReady.facts (R : ir.CompletionReady I primeNodes S G D) :
    ir.CompletionFacts I primeNodes S G D :=
  completionFacts_of_B R.oneNodes R.wf R.sourceValid R.ok

variable {Inp : Type} {relH : Set (ir.Valuation I × Inp)}

/-- **The honest strategy of a program whose completeness certificate passes the check, from an
execution of its source program** (`HonestStrategy.ofCompletion` at `CompletionReady.facts`). -/
def HonestStrategy.ofCompletionReady (R : ir.CompletionReady I primeNodes S G D)
    (E : ir.SourceExecution I relH) : ir.HonestStrategy I relH :=
  HonestStrategy.ofCompletion R.model R.macsRealizable R.facts E

/-- **The completeness errors of the honest strategy from ready data are the execution's.** -/
theorem HonestStrategy.ofCompletionReady_δ (R : ir.CompletionReady I primeNodes S G D)
    (E : ir.SourceExecution I relH) : (HonestStrategy.ofCompletionReady R E).δ = E.δ := rfl

end Ready

/-! ## The check in ranges

`completionB` splits into checks of ranges `[i, j)` of the values (`completionValuesIn`: the value
passes in one walk, each value with its generator) and of the predicates (`completionPredsIn`: the
predicates' checks and their completeness derivations, each predicate with its derivation), which
join with no re-check (`…In_append`) and give the check from `[0, n)`, `n` at least the list's
length, with the groups' checks, the message records and the derivations' count
(`completionRestB`, `completionB_of_parts`). -/

section Ranges

variable (ir : RealizedProgram)

/-- **`completionB`'s checks at value `v`** (`x`) with generator `g`, the generators read through
`GT`, the bound values' records through `T`, the messages through `MT` and the reads through
`RT`. -/
def valueAllCV (L : List (ℕ × String)) (GT : NatTrie Gen) (T MT : NatTrie ℕ)
    (RT : NatTrie (List Read)) (v : ℕ) (x : Value) (g : Gen) : Bool :=
  ir.valueCV L GT T v x g && ir.boundNoCopyV v x && ir.coveredCV GT MT v x g &&
    ir.typedNoLateL v x (RT.getD v []) && ir.typeRoleV v x

/-- **`completionB`'s checks of the values `[i, j)`**, each with its generator. -/
def completionValuesIn (L : List (ℕ × String)) (S : Structure) (G : Gens) (i j : ℕ) : Bool :=
  allIdx2In (ir.valueAllCV L (toTrie G) S.boundRecTab S.messageTab ir.readsT) .none ir.values G i j

/-- **`completionB`'s checks at predicate `pid`** (`pr`) with completeness derivation `s`. -/
def predAllCB (primeNodes : ℕ → List String) (S : Structure) (G : Gens) (D : CDerivations)
    (pid : ℕ) (pr : Predicate) (s : List CStep) : Bool :=
  ir.predCB primeNodes S G pid && ir.blindsB pid &&
    ir.cderivStepsB primeNodes S G D.ranks (rankOf D.ranks pid) pid pr s

/-- **`completionB`'s checks of the predicates `[i, j)`**, each with its completeness
derivation. -/
def completionPredsIn (primeNodes : ℕ → List String) (S : Structure) (G : Gens)
    (D : CDerivations) (i j : ℕ) : Bool :=
  allIdx2In (ir.predAllCB primeNodes S G D) [] ir.predicates D.derivs i j

/-- **`completionB`'s checks of the groups and the message records**, and one completeness
derivation per predicate. -/
def completionRestB (primeNodes : ℕ → List String) (S : Structure) (G : Gens)
    (D : CDerivations) : Bool :=
  ir.allGroupsB (ir.groupCB primeNodes S G D) && ir.allGroupsB ir.staticGroupNoLateB &&
    ir.messageRecsB S && Nat.beq D.derivs.length ir.predicates.length

variable {ir}

theorem completionValuesIn_append {L : List (ℕ × String)} {S : Structure} {G : Gens}
    {i j k : ℕ} (h₁ : ir.completionValuesIn L S G i j = true)
    (h₂ : ir.completionValuesIn L S G j k = true) : ir.completionValuesIn L S G i k = true :=
  allIdx2In_append h₁ h₂

theorem completionPredsIn_append {primeNodes : ℕ → List String} {S : Structure} {G : Gens}
    {D : CDerivations} {i j k : ℕ} (h₁ : ir.completionPredsIn primeNodes S G D i j = true)
    (h₂ : ir.completionPredsIn primeNodes S G D j k = true) :
    ir.completionPredsIn primeNodes S G D i k = true :=
  allIdx2In_append h₁ h₂

theorem allCDerivsB_of_forall {primeNodes : ℕ → List String} {S : Structure} {G : Gens} {P : ℕ} :
    ∀ {pid : ℕ} {ps : List Predicate} {ds : List (List CStep)}, ds.length = ps.length →
      (∀ k < ps.length, ir.cderivStepsB primeNodes S G P (rankOf P (pid + k)) (pid + k)
        (ps.getD k default) (ds.getD k []) = true) →
      ir.allCDerivsB primeNodes S G P pid ps ds = true
  | _, [], [], _, _ => rfl
  | _, [], _ :: _, hl, _ => by simp at hl
  | _, _ :: _, [], hl, _ => by simp at hl
  | pid, pr :: ps, s :: ds, hl, h => by
    simp only [allCDerivsB, CReader.allCDerivsB, Bool.and_eq_true]
    have h0 := h 0 (by simp)
    simp only [Nat.add_zero, List.getD_cons_zero] at h0
    refine ⟨h0, allCDerivsB_of_forall (by simpa using hl) fun k hk => ?_⟩
    have := h (k + 1) (by simpa using hk)
    rw [show pid + (k + 1) = pid + 1 + k by omega] at this
    simpa using this

/-- **`completionB` from its checks of the values and the predicates**, each on `[0, n)` for `n`
at least the list's length, and of the groups and the message records. -/
theorem completionB_of_parts {primeNodes : ℕ → List String} {L : List (ℕ × String)}
    {S : Structure} {G : Gens} {D : CDerivations} {nv np : ℕ}
    (h : ir.completionRestB primeNodes S G D = true)
    (hv : ir.completionValuesIn L S G 0 nv = true) (hnv : ir.values.length ≤ nv)
    (hp : ir.completionPredsIn primeNodes S G D 0 np = true) (hnp : ir.predicates.length ≤ np) :
    ir.completionB primeNodes L S G D = true := by
  simp only [completionRestB, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨hg, hsg⟩, hm⟩, hd⟩ := h
  have hv' := allIdx2_sound _ _ _ _ _ (allIdx2_of_allIdx2In hv hnv)
  have hp' := allIdx2_sound _ _ _ _ _ (allIdx2_of_allIdx2In hp hnp)
  have hvk : ∀ k < ir.values.length, _ := fun k hk => by
    have := hv' k hk
    simp only [Nat.zero_add, valueAllCV, Bool.and_eq_true] at this
    exact this
  have hpk : ∀ k < ir.predicates.length, _ := fun k hk => by
    have := hp' k hk
    simp only [Nat.zero_add, predAllCB, Bool.and_eq_true] at this
    exact this
  have hrange : ∀ (P : ℕ → Bool), (∀ k < ir.predicates.length, P k = true) →
      ir.allPredsB P = true := fun P hP => by
    rw [allPredsB, List.all_eq_true]
    exact fun k hk => hP k (List.mem_range.1 hk)
  rw [completionB_eq]
  rw [(allIdx2_iff _ _ _ _ _).2 fun k hk => by simpa using (hvk k hk).1.1.1.1,
    hrange _ fun k hk => (hpk k hk).1.1, hg, (allIdx_iff _ _ _).2 fun k hk => by
      simpa using (hvk k hk).1.1.1.2,
    (allIdx2_iff _ _ _ _ _).2 fun k hk => by simpa using (hvk k hk).1.1.2,
    (allIdx2_iff _ _ _ _ _).2 fun k hk => by
      rw [getD_readsL]
      simpa using (hvk k hk).1.2,
    hrange _ fun k hk => (hpk k hk).1.2, hsg,
    show ir.cderivsB primeNodes S G D = true from
      allCDerivsB_of_forall (by omega) fun k hk => by simpa using (hpk k hk).2,
    (allIdx_iff _ _ _).2 fun k hk => by simpa using (hvk k hk).2, hm]
  rfl

end Ranges

end GordieHowe.RealizedProgram
