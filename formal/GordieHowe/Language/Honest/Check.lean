-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Honest.Exec
public import GordieHowe.Language.Realizations.Derivation.Events

@[expose] public section

/-!
# GordieHowe: the MAC sites and the Boolean checks on a program's values and groups

The pieces of a program the completeness certificate's checks read
(`GordieHowe/Language/Completeness/Check.lean`), each stated for any realized program:

* **the MAC sites** (`MacSite`, `macSitesOf`): the MAC check over `y`'s field for every cross-field
  `equal` its `x` domain hosts, and the checks over both fields for every cross-field `equal` no
  domain hosts (compiler/mac.h, `mac_odd`), with the parts of each site's tail (`macTail`,
  `macTailParts`, `macGrouping`, `macLow`, `macTop`) and its check over a field (`macFieldCheckB`);
* **the predicates' roles**: the Boolean role checks of the tail forms (`groupedRoleB`,
  `digitsRoleB`, `oneDigitRoleB`, `twoTail`);
* **the groups** (`staticGroupNoLateB`, `allGroupsB`): a late histogram the only one of its group or
  beside a static one;
* **the values** (`allValuesB`, `typedNoLateB`, `blindsB`, `noGenReadB`, `srcNoPadCopyB`,
  `srcNoMessageB`, `srcLatePadB`, `boundRecsB`, `cellB`, `realTypeB`), each with its soundness
  lemma.
-/

namespace GordieHowe.RealizedProgram

open Export ProofSystem.PhaseLayout IOP
open scoped NNReal

/-! ## The parts of a cross-field `equal` and of a `mod_q` -/

/-- **The operands and the realization of a cross-field `equal`.** -/
structure CrossParts where
  /-- The `x` domain. -/
  dx : ℕ
  /-- The `x` operand. -/
  x : Expr
  /-- The `y` domain. -/
  dy : ℕ
  /-- The `y` operand. -/
  y : Expr
  /-- The kind. -/
  k : CrossKind
  /-- The MAC realization. -/
  real : MacRealization
  deriving Inhabited

/-- **The parts of a cross-field `equal`**, none for any other predicate. -/
def PredBody.crossParts? : PredBody → Option CrossParts
  | .cross dx x dy y k real => some ⟨dx, x, dy, y, k, real⟩
  | _ => none

theorem PredBody.eq_of_crossParts? {b : PredBody} {c : CrossParts} (h : b.crossParts? = some c) :
    b = .cross c.dx c.x c.dy c.y c.k c.real := by
  unfold crossParts? at h
  split at h
  · cases h
    rfl
  · cases h

/-- **The domain, modulus, sides and realization of a `mod_q`.** -/
structure ModParts where
  /-- The domain. -/
  d : ℕ
  /-- The modulus. -/
  q : ℕ
  /-- The left side. -/
  lhs : Expr
  /-- The right side. -/
  rhs : Expr
  /-- The realization. -/
  real : ModRealization
  deriving Inhabited

/-- **The parts of a `mod_q`**, none for any other predicate. -/
def PredBody.modParts? : PredBody → Option ModParts
  | .mod d q lhs rhs real => some ⟨d, q, lhs, rhs, real⟩
  | _ => none

theorem PredBody.eq_of_modParts? {b : PredBody} {m : ModParts} (h : b.modParts? = some m) :
    b = .mod m.d m.q m.lhs m.rhs m.real := by
  unfold modParts? at h
  split at h
  · cases h
    rfl
  · cases h

/-- **Whether an expression is a leaf.** -/
def Expr.isLeaf : Expr → Bool
  | .leaf _ => true
  | _ => false

theorem Expr.eq_leaf_of_isLeaf {e : Expr} (h : e.isLeaf = true) : ∃ v, e = .leaf v := by
  cases e <;> simp_all [isLeaf]

/-- **A MAC site**: the cross-field `equal` `pid` and one of its MAC checks over a field, over `x`'s
field (`xSide`) or over `y`'s field. A MAC its `x` domain hosts has one site, the check over `y`'s
field; a MAC no domain hosts has two (compiler/mac.h, `mac_odd`). -/
structure MacSite where
  /-- The cross-field `equal`. -/
  pid : ℕ
  /-- Whether the site is the check over `x`'s field. -/
  xSide : Bool

section

variable {ir : RealizedProgram} {I : Interp} {primeNodes : ℕ → List String}
  {L : ℕ → ℕ → Option Ivl}

/-! ## The MAC of a cross-field `equal` -/

section Parts

variable (ir)

/-- **Whether predicate `pid` is a cross-field `equal`.** -/
def isCrossB (pid : ℕ) : Bool := (ir.predicateT pid).body.crossParts?.isSome

/-- **The cross-field `equal`s of the program**, by index. -/
def crossPids : List ℕ := (List.range ir.predicates.length).filter ir.isCrossB

/-- **The parts of cross-field `equal` `pid`.** -/
def macCross (pid : ℕ) : CrossParts := (ir.predicateT pid).body.crossParts?.getD default

/-- **The MAC sites of cross-field `equal` `pid`**: the check over `y`'s field where its `x` domain
hosts the MAC (no blind for `x`'s field), the checks over both fields where no domain hosts it
(`mac_odd`: one tail per field), the check over `x`'s field first. -/
def macSitesOf (pid : ℕ) : List MacSite :=
  if (ir.macCross pid).real.blindX.isSome then [⟨pid, true⟩, ⟨pid, false⟩] else [⟨pid, false⟩]

/-- **The MAC sites of the program**: the sites of every cross-field `equal`. -/
def sites : List MacSite := ir.crossPids.flatMap ir.macSitesOf

/-- **The domain of MAC site `st`**: the `x` domain for the check over `x`'s field, the `y` domain
otherwise. -/
def siteDom (st : MacSite) : ℕ := if st.xSide then (ir.macCross st.pid).dx else (ir.macCross st.pid).dy

/-- **The operand of MAC site `st`**: the `x` operand for the check over `x`'s field, the `y`
operand otherwise. -/
def siteOp (st : MacSite) : Expr := if st.xSide then (ir.macCross st.pid).x else (ir.macCross st.pid).y

/-- **The blind of MAC site `st`**: `blindX` for the check over `x`'s field, `blind` otherwise. -/
def macBlind (st : MacSite) : ℕ :=
  if st.xSide then (ir.macCross st.pid).real.blindX.getD 0 else (ir.macCross st.pid).real.blind.getD 0

/-- **The operand a MAC tail `pr` checks**: the operand of its left side's MAC convolution. -/
def tailOperandOf (pr : Predicate) : Expr :=
  match pr.body with
  | .mod _ _ (.add _ (.apply _ z')) _ _ => z'
  | _ => default

/-- **The operand `z'` of a check of MAC site `st` reads the site's operand**: padded by zeros to
`chunks · width` coordinates (`zeroPadB`) where `x`'s domain hosts the MAC; the operand itself where
no domain does. -/
def macOpOkB (st : MacSite) (z' : Expr) : Bool :=
  match (ir.macCross st.pid).real.blindX with
  | none => ir.zeroPadB (ir.domainField (ir.siteDom st))
      ((ir.macCross st.pid).real.chunks * (ir.macCross st.pid).real.width) z' (ir.siteOp st)
  | some _ => z'.beq (ir.siteOp st)

/-- **The tail of MAC site `st`**: the first predicate that is the tail of its check (`macTailAtB`)
at its operand, which reads the site's operand (`macOpOkB`). -/
def macTail (st : MacSite) : ℕ :=
  ((List.range ir.predicates.length).find? fun t =>
    ir.macTailAtOfB st.pid (ir.siteDom st) (tailOperandOf (ir.predicateT t)) (ir.macBlind st)
      (ir.macCross st.pid).real (ir.predicateT t) &&
    ir.macOpOkB st (tailOperandOf (ir.predicateT t))).getD 0

/-- **The operand the tail of MAC site `st` checks** (`tailOperandOf`). -/
def macCheckOp (st : MacSite) : Expr := tailOperandOf (ir.predicateT (ir.macTail st))

/-- **The parts of the tail of the MAC of `st`.** -/
def macTailParts (st : MacSite) : ModParts :=
  (ir.predicateT (ir.macTail st)).body.modParts?.getD default

/-- **The units of the tail of the MAC of `st`.** -/
def macUnitsAt (st : MacSite) : MacUnits :=
  (macUnits? (ir.macTailParts st).lhs).getD ⟨0, 0, 0, 0, [], default⟩

/-- **The largest entry of the MAC convolution's matrices** of the tail of `st`
(`macConvMax?`, `0` when none). -/
def macConvMaxAt (st : MacSite) : ℕ :=
  (macConvMax? (ir.macUnitsAt st).width (ir.macUnitsAt st).taps).getD 0

variable (primeNodes) in
/-- **The MAC check over the field of site `st`** (`MacFieldCheck`): the check over `y`'s field
with its blind (`macBlindCoreB`) where the `x` domain hosts the MAC; where no domain hosts it, the
check over either field, of odd characteristic (`MacOddFieldOk`, at the values' intervals
`honestIvl`), both operands' domains of characteristic above `1`. -/
def macFieldCheckB (st : MacSite) : Bool :=
  match (ir.macCross st.pid).real.blindX with
  | none => !st.xSide &&
      ir.macBlindCoreB (ir.siteDom st) (ir.macBlind st) (ir.macCross st.pid).real
  | some _ => decide (ir.MacOddFieldOk (ir.honestIvl primeNodes) st.pid (ir.siteDom st)
      (ir.siteOp st) (ir.macBlind st) (ir.macCross st.pid).real) &&
      decide (MacChars ir (ir.macCross st.pid).dx (ir.macCross st.pid).dy)

end Parts

/-- **A cross-field `equal` is its parts** (`macCross`). -/
theorem body_eq_macCross {pid : ℕ} (h : ir.isCrossB pid = true) :
    (ir.predicate pid).body = .cross (ir.macCross pid).dx (ir.macCross pid).x (ir.macCross pid).dy
      (ir.macCross pid).y (ir.macCross pid).k (ir.macCross pid).real := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 h
  have hm : ir.macCross pid = c := by simp [macCross, hc]
  rw [hm, ← predicateT_eq]
  exact PredBody.eq_of_crossParts? hc

/-- **The MAC convolution's largest entry is `macConvMaxAt`** where `macConvMax?` succeeds. -/
theorem convMax_eq_macConvMaxAt {st : MacSite}
    (h : (macConvMax? (ir.macUnitsAt st).width (ir.macUnitsAt st).taps).isSome = true) :
    Conv.convMax (ir.macUnitsAt st).width (ir.macUnitsAt st).taps.toFinset = ir.macConvMaxAt st := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 h
  rw [convMax_of_macConvMax? hc]
  simp [macConvMaxAt, hc]

/-! ## The grouped tail -/

section Grouped

variable (ir)

/-- **The grouping of the tail of the MAC of `st`.** -/
def macGrouping (st : MacSite) : GroupedMod := (ir.macTailParts st).real.grouped.getD default

/-- **The accumulators of the grouped tail of `st`.** -/
def macGroupAcc (st : MacSite) : ℕ :=
  match (ir.macGrouping st).accumulators with
  | some (.leaf a) => a
  | _ => 0

/-- **The quotient digits of the grouped tail of `st`.** -/
def macGroupGq (st : MacSite) : ℕ :=
  match (ir.macGrouping st).groupDigits with
  | .leaf g => g
  | _ => 0

end Grouped

/-! ## The ungrouped digit tail -/

section Digits

variable (ir)

/-- **The lower digit of the digit tail of `st`**: the first of its two digits. -/
def macLow (st : MacSite) : ℕ :=
  match (ir.macTailParts st).real.digits with
  | [.leaf l, _] => l
  | _ => 0

/-- **The derived top digit of the digit tail of `st`**: the second of its two digits. -/
def macTop (st : MacSite) : Expr :=
  match (ir.macTailParts st).real.digits with
  | [_, t] => t
  | _ => default

/-- **The accumulator of the digit tail of `st`** (`digitsAcc`). -/
def macDigitsAcc (st : MacSite) : ℕ := ir.digitsAcc (ir.macTailParts st).real

/-- **The no-wrap range's expression of the digit tail of `st`**: `2 low + 2 B top`. -/
def macWrapExpr (st : MacSite) : Expr :=
  .add (.scale (.const 2) (.leaf (ir.macLow st)))
    (.scale (.const (2 * (ir.macTailParts st).real.radix)) (ir.macTop st))

end Digits

/-! ## The one-digit tail -/

section OneDigit

variable (ir)

/-- **The accumulator of the one-digit tail of `st`** (`oneDigitAcc`). -/
def macOneAcc (st : MacSite) : ℕ := ir.oneDigitAcc (ir.macTailParts st).real

end OneDigit

/-! ## The MAC checks over the fields of characteristic `2` -/

section TwoSides

variable (ir)

/-- **The tail of a MAC check over a field of characteristic `2`**: the first predicate that is its
field `equal` tail (`macTailTwoB`). -/
def twoTail (st : MacSite) : ℕ :=
  ((List.range ir.predicates.length).find? fun t => ir.macTailTwoOfB st.pid (ir.siteDom st)
    (ir.siteOp st) (ir.macBlind st) (ir.macCross st.pid).real (ir.predicateT t)).getD 0

end TwoSides

theorem isCrossB_of_body {pid dx dy : ℕ} {x y : Expr} {k : CrossKind} {real : MacRealization}
    (hb : (ir.predicate pid).body = .cross dx x dy y k real) : ir.isCrossB pid = true := by
  simp [isCrossB, predicateT_eq, hb, PredBody.crossParts?]

/-! ## The roles of the predicates -/

section Roles

variable (ir primeNodes)

/-- **Predicate body `b` is a predicate of the grouped tail of `st`**, as a check: an accumulator row of a group, the residues' check, a
lookup on the quotient digits or on the final quotient. -/
def groupedRoleB (st : MacSite) (b : PredBody) : Bool :=
  (List.range (ir.macGrouping st).groups.length).any (fun g =>
      ir.groupRowB (ir.honestIvl primeNodes) (ir.siteDom st) (ir.macUnitsAt st) (ir.macGrouping st)
        (ir.macGroupAcc st) g ((ir.macGrouping st).groups.getD g default) b) ||
    (match b with
      | .equal d (.mul R₁ R₂) R₃ _ => d == (ir.siteDom st) &&
          R₁.beq (ir.macGrouping st).residues && R₂.beq (ir.macGrouping st).residues &&
          R₃.beq (ir.macGrouping st).residues
      | _ => false) ||
    (match b with
      | .mem _ [.leaf g] (.range _) (.lookup _) => g == ir.macGroupGq st
      | _ => false) ||
    (match b with
      | .mem _ [D] (.range _) (.lookup _) => D.beq (ir.macTailParts st).real.quotExpr
      | _ => false)

/-- **Predicate body `b` is a predicate of the digit tail of `st`**, as a check: the accumulator row, a lookup on the lower or the top
digit, the no-wrap range. -/
def digitsRoleB (st : MacSite) (b : PredBody) : Bool :=
  (match b with
    | .equal d Lr (.leaf z) _ => d == (ir.siteDom st) &&
        ir.constAll z 0 (ir.exprLen (ir.macTailParts st).lhs) (ir.domainField (ir.siteDom st)) &&
        accTerms (ir.charOf (ir.domainField (ir.siteDom st))) (ir.macDigitsAcc st) Lr
          (ir.macTailParts st).lhs
    | _ => false) ||
    (match b with
      | .mem _ [.leaf l] (.range _) (.lookup _) => l == ir.macLow st
      | _ => false) ||
    (match b with
      | .mem _ [D] (.range _) (.lookup _) => D.beq (ir.macTop st)
      | _ => false) ||
    (match b with
      | .mem _ [D] (.range _) _ => D.beq (ir.macWrapExpr st)
      | _ => false)

/-- **Predicate body `b` is a predicate of the one-digit tail of `st`**, as a check: the accumulator row, a lookup on the quotient. -/
def oneDigitRoleB (st : MacSite) (b : PredBody) : Bool :=
  (match b with
    | .equal d Lr (.leaf z) _ => d == (ir.siteDom st) &&
        ir.constAll z 0 (ir.exprLen (ir.macTailParts st).lhs) (ir.domainField (ir.siteDom st)) &&
        accTerms (ir.charOf (ir.domainField (ir.siteDom st))) (ir.macOneAcc st) Lr
          (ir.macTailParts st).lhs
    | _ => false) ||
    (match b with
      | .mem _ [D] (.range _) (.lookup _) => D.beq (ir.macTailParts st).real.quotExpr
      | _ => false)

end Roles

/-! ## The groups and their histograms -/

section Groups

variable (ir)

/-- **A group without a late histogram reads no late value, nor do its table's rows**
(`RealizeFacts.staticGroups`), as a check. -/
def staticGroupNoLateB (t g : ℕ) : Bool :=
  match (ir.groupOf t g).lateMult with
  | none => (ir.members t g).all (fun m =>
        (ir.exprNodes (ir.needleExpr m.pred m.needle)).all ir.noLateReadB) &&
      (ir.groupOf t g).staticMult.toList.all ir.noLateReadB && (ir.tableRowReads t).all ir.noLateReadB
  | some _ => true

/-- **A property of every group of every table**, as a check. -/
def allGroupsB (P : ℕ → ℕ → Bool) : Bool :=
  (List.range ir.tables.length).all fun t => (List.range (ir.groupCountOf t)).all (P t)

end Groups

theorem of_allGroupsB {P : ℕ → ℕ → Bool} (h : ir.allGroupsB P = true) {t g : ℕ}
    (ht : t < ir.tables.length) (hg : g < ir.groupCountOf t) : P t g = true :=
  List.all_eq_true.1 (List.all_eq_true.1 h t (List.mem_range.2 ht)) g (List.mem_range.2 hg)

/-- **The table's entries are distinct in the challenge's field** below its characteristic. -/
theorem natCast_inj_of_le_char (hI : I.Registered ir) {f n : ℕ} (hf : f < ir.fields.length)
    (hn : n ≤ ir.charOf f) {a b : ℕ} (ha : a < n) (hb : b < n)
    (h : ((a : ℕ) : (I f).K) = (b : ℕ)) : a = b := by
  have := charP_field hI hf
  exact ((CharP.natCast_eq_natCast (I f).K (ir.field f).characteristic).1 h).eq_of_lt_of_lt
    (lt_of_lt_of_le ha hn) (lt_of_lt_of_le hb hn)

theorem staticGroups_of_B (hwf : ir.WellFormed) (h : ir.allGroupsB ir.staticGroupNoLateB = true) :
    ∀ t < ir.tables.length, ∀ g < ir.groupCountOf t,
      (ir.groupOf t g).lateMult = none →
        (∀ m ∈ ir.members t g, ∀ w ∈ ir.exprNodes (ir.needleExpr m.pred m.needle),
          ir.NoLateRead w) ∧ (∀ v ∈ (ir.groupOf t g).staticMult.toList, ir.NoLateRead v) ∧
          ∀ w ∈ ir.tableRowReads t, ir.NoLateRead w := by
  intro t ht g hg hv
  have hB := of_allGroupsB h ht hg
  unfold staticGroupNoLateB at hB
  rw [hv] at hB
  simp only [Bool.and_eq_true, List.all_eq_true] at hB
  exact ⟨fun m hm w hw => noLateRead_of_B hwf (hB.1.1 m hm w hw),
    fun v hv => noLateRead_of_B hwf (hB.1.2 v hv), fun w hw => noLateRead_of_B hwf (hB.2 w hw)⟩

/-! ## The values -/

section Values

variable (ir)

/-- **A property of every value of the program**, as a check. -/
def allValuesB (P : ℕ → Bool) : Bool := (List.range ir.values.length).all P

/-- **A property of every predicate of the program**, as a check. -/
def allPredsB (P : ℕ → Bool) : Bool := (List.range ir.predicates.length).all P

/-- **The pad space of value `v` contains the naturals by a listed node**, as a check: the whole
field, or a node of `L` in the value's field. -/
def padNatB (L : List (ℕ × String)) (v : ℕ) : Bool :=
  match (ir.value v).padSpace with
  | .full => true
  | .node S => L.contains (ir.valueField v, S)

/-- **A node-typed value that is not late reads no late value** (`RealizeFacts.typedNoLate`), as a
check at value `v`. -/
def typedNoLateB (v : ℕ) : Bool :=
  !((ir.value v).typeSource == .node) || decide (ir.IsLate v) || ir.noLateReadB v

/-- **Every blind of a cross-field `equal`'s MAC is the pad copy `polynomialBits` of its tag's pad**
(`BlindsArePadCopies`), as a check at predicate `q`: a committed cell of a domain of the program at
each of its `width` coordinates, the tag's pad a cell of its domain at coordinate `0`. -/
def blindsB (q : ℕ) : Bool :=
  match (ir.predicateT q).body with
  | .cross _ _ _ _ _ real =>
    (real.blind.toList ++ real.blindX.toList).all fun b =>
      ir.isPadCopyB b real.tag "polynomialBits" &&
        decide ((ir.value b).domain < ir.domains.length) &&
        decide (b < ir.values.length) && ir.isCellValue (ir.value b).domain b &&
        decide (real.width ≤ (ir.value b).size) &&
        decide ((ir.value real.tag).domain < ir.domains.length) &&
        decide (real.tag < ir.values.length) &&
        !ir.isCellValue (ir.value real.tag).domain real.tag &&
        ir.isLateOf (ir.value real.tag).domain real.tag &&
        decide (0 < (ir.value real.tag).size)
  | _ => true

/-- **`NoGenRead`, through the reads table.** -/
def noGenReadB (w : ℕ) : Bool :=
  (ir.readsT.getD w []).all fun r =>
    match r with
    | .late u => !decide (u < ir.values.length ∧ ir.IsLate u) || decide (ir.IsSourceValue u)
    | _ => true

/-- **`NoGenPred`, as a check**, through the closure table (`predNodesM`). -/
def noGenPredB (b : PredBody) : Bool := (ir.predNodesM b).all ir.noGenReadB

end Values

theorem of_allValuesB {P : ℕ → Bool} (h : ir.allValuesB P = true) {v : ℕ}
    (hv : v < ir.values.length) : P v = true :=
  List.all_eq_true.1 h v (List.mem_range.2 hv)

theorem of_allPredsB {P : ℕ → Bool} (h : ir.allPredsB P = true) {q : ℕ}
    (hq : q < ir.predicates.length) : P q = true :=
  List.all_eq_true.1 h q (List.mem_range.2 hq)

theorem noGenRead_of_B (hwf : ir.WellFormed) {w : ℕ} (h : ir.noGenReadB w = true) :
    ir.NoGenRead w := by
  intro u hu hlt hl
  have := List.all_eq_true.1 h _ ((mem_readsT hwf w _).1 hu)
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
    not_and] at this
  rcases this with h1 | h1
  · exact absurd hl (h1 hlt)
  · exact h1

theorem noGenPred_of_B (hwf : ir.WellFormed) {b : PredBody}
    (hr : ir.BodyRefsOk b) (h : ir.noGenPredB b = true) :
    ir.NoGenPred b := fun w hw =>
  noGenRead_of_B hwf (List.all_eq_true.1 h w ((mem_predNodesM hwf.refsOrdered hr w).2 hw))

theorem typedNoLate_of_B (hwf : ir.WellFormed) (h : ir.allValuesB ir.typedNoLateB = true) :
    ∀ v < ir.values.length, (ir.value v).typeSource = .node → ¬ ir.IsLate v → ir.NoLateRead v := by
  intro v hv hts hl
  have hB := of_allValuesB h hv
  unfold typedNoLateB at hB
  simp only [hts, beq_self_eq_true, Bool.not_true, Bool.false_or, hl, decide_false] at hB
  exact noLateRead_of_B hwf hB

theorem blinds_of_B (h : ir.allPredsB ir.blindsB = true) : ir.BlindsArePadCopies := by
  intro p hp dx x dy y k real hb b hbm
  obtain ⟨q, hq, rfl⟩ := exists_index_of_mem hp
  have hB := of_allPredsB h hq
  unfold blindsB at hB
  rw [predicateT_eq, hb] at hB
  simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hB
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := hB b hbm
  exact ⟨kind_of_isPadCopyB h1, h2, fun i hi => (ir.mem_cellKeys_val).2 ⟨h3, h4, by omega⟩, h6,
    (ir.mem_cellKeys_pad).2 ⟨h7, h8, h9, h10⟩⟩

/-! ## The value facts -/

section Honest

variable (ir)

/-- **No source value is a pad copy** (`HonestFacts.srcNoPadCopy`), as a check at value `u`. -/
def srcNoPadCopyB (u : ℕ) : Bool := !decide (ir.IsSourceValue u) || !(ir.value u).kind.isPadCopy

/-- **No source value is a message** (`SrcNoMessage`), as a check at value `v`. -/
def srcNoMessageB (v : ℕ) : Bool := !decide (ir.IsSourceValue v) || !(ir.value v).kind.isMessage

/-- **A source late value's pad space contains its type** (`HonestFacts.srcLatePads`), as a check
at value `v`. -/
def srcLatePadB (v : ℕ) : Bool :=
  !decide (ir.IsSourceValue v) || !decide (ir.IsLate v) || ir.latePadTypeB v

/-- **A value bound to its digits is a source value, the record of a lookup**
(`HonestFacts.boundRecs`), as a check at value `v`. -/
def boundRecsB (v : ℕ) : Bool :=
  !(ir.value v).kind.isBound || (decide (ir.IsSourceValue v) && ir.boundRecB v)

/-- **A committed cell is at a node of its source value's type, a node of `L`**
(`HonestFacts.cellNodes`, `HonestFacts.oneMem`), as a check at value `v`. -/
def cellB (L : List (ℕ × String)) (v : ℕ) : Bool :=
  !ir.isCellValue (ir.value v).domain v || (ir.cellNodeB v && ir.cellNodeInB L v)

/-- **A node-typed value that is no source value and no late value is a committed cell whose type
contains the naturals by a node of `L`** (`HonestFacts.realTypes`), as a check at value `v`. -/
def realTypeB (L : List (ℕ × String)) (v : ℕ) : Bool :=
  !((ir.value v).typeSource == .node) || decide (ir.IsLate v) || decide (ir.IsSourceValue v) ||
    (ir.privCellB v && ir.natTypedInB L v)

variable (L) in
/-- **The cross-field `equal` of MAC site `st` is a source predicate and the site's operand reads
within `[0, 1]` by the source values' intervals** (`HonestFacts.macIvls`), as a check at the values'
intervals `L`. -/
def macIvlAtB (st : MacSite) : Bool :=
  ir.inSource (ir.predicateT st.pid) &&
    decide (IvlWithin (ir.srcIvl L (ir.domainField (ir.siteDom st)) (ir.macCheckOp st)) 0 1)

variable (primeNodes) in
/-- **`macIvlAtB` at the values' intervals `srcLeafIvl`.** -/
def macIvlB (st : MacSite) : Bool := ir.macIvlAtB (ir.srcLeafIvl primeNodes) st

/-- **A late member of a mixed group at the late histogram `v` of table `t` reads a digit of the
digit tail of `st`**, as a check. -/
def lateMemberAtB (st : MacSite) (t v : ℕ) (m : Member) : Bool :=
  decide (ir.chalField (ir.alphaOf t) = ir.domainField (ir.siteDom st)) &&
    decide (m.first + m.count ≤ (ir.macUnitsAt st).width) &&
    (((ir.needleExpr m.pred m.needle).beq (.leaf (ir.macLow st)) &&
        decide ((ir.macTailParts st).real.radix ≤ (ir.value v).size)) ||
      (ir.needleExpr m.pred m.needle).beq (ir.macTop st))

/-- **A late member of a mixed group reads the quotient of the one-digit tail of `st`**, as a check at table `t`. -/
def lateMemberOneAtB (st : MacSite) (t : ℕ) (m : Member) : Bool :=
  decide (ir.chalField (ir.alphaOf t) = ir.domainField (ir.siteDom st)) &&
    decide (m.first + m.count ≤ (ir.macUnitsAt st).width) &&
    (ir.needleExpr m.pred m.needle).beq (ir.macTailParts st).real.quotExpr

/-- **The bound on the honest quotient of the one-digit tail of `st`**. -/
def macQuotMax (st : MacSite) : ℕ := (1 + (ir.macUnitsAt st).chunks * ir.macConvMaxAt st) / 2

/-- **The bound on the honest top digit of the digit tail of `st`**. -/
def macTopMax (st : MacSite) : ℕ :=
  (1 + (ir.macUnitsAt st).chunks * ir.macConvMaxAt st) / 2 / (ir.macTailParts st).real.radix

end Honest

/-! ## The checker -/

variable {Inp : Type} {relH : Set (ir.Valuation I × Inp)}

end

end GordieHowe.RealizedProgram
