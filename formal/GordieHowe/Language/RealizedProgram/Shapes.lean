-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.ValueShape
public import GordieHoweNative.Language.RealizedProgram.Shapes
public import GordieHoweNative.Language.ProgramData
public import GordieHowe.Language.RealizedProgram.Embed

@[expose] public section

/-!
# The shape claims about a realized program

A program's shapes (the kinds of the values and the bodies of the predicates its applications'
frontends name) are data: a list of claims (`ShapeClaim`) the compiler emits per program
(`GordieHowe/Generated/<P>/Shapes.lean`). Their check `shapesB` is one part of the program's
checks; this module has its condition and soundness:

* **the condition** (`ShapesHold ir cs`): every claim of the list holds (`ShapeClaim.Holds`, the
  claim's fact about `ir.value v` or `ir.predicate p`, stated over the claim's parts only);
* **the soundness lemma** (`shapes_sound`): `shapesB ir cs = true` gives `ShapesHold ir cs`, from
  one soundness lemma per constructor (`ShapeClaim.kindPriv_sound` … `ShapeClaim.modParts_sound`);
  at a program's data (`ProgramData.shapesB`, the part), `ProgramData.shapes_sound`;
* **the claim at a position** (`ShapesHold.kindPriv` … `ShapesHold.modParts`): under the
  condition, the claim at position `k` of the list (`cs[k]? = some c`, by `rfl` on the list) is
  its fact.

The generated named facts (`GordieHowe/Generated/<P>/ShapeFacts.lean`) are the last, one per
claim. A frontend reads a value's kind or a predicate's body off a named fact and compares its
parts with its own terms by `rfl` on small closed expressions, never through the program.

The definitions are in `GordieHoweNative/Language/RealizedProgram/Shapes.lean` (the compiled
library `GordieHoweNative`); this module has their lemmas.
-/
namespace GordieHowe.RealizedProgram

variable {ir : RealizedProgram}

/-- **Equality-body parts and the small headers determine the whole predicate.** -/
theorem Predicate.eq_of_equalParts {a b : Predicate} {d : Nat} {l r : Expr}
    (ha : ∃ t, a.body = .equal d l r t)
    (hb : ∃ t, b.body = .equal d l r t)
    (hmeta : a.equalHeader = b.equalHeader) : a = b := by
  obtain ⟨ta, ha⟩ := ha
  obtain ⟨tb, hb⟩ := hb
  cases a with | mk an ab ar ad ak =>
    cases b with | mk bn bb br bd bk =>
      dsimp at ha hb
      cases ha
      cases hb
      simp only [Predicate.equalHeader, Prod.mk.injEq, Option.some.injEq] at hmeta
      rcases hmeta with ⟨rfl, rfl, rfl, rfl, rfl⟩
      rfl

/-- Membership in the cross-field summary is exactly a valid cross-field body. -/
theorem mem_crossPredicateIds_iff {p : ℕ} :
    p ∈ ir.crossPredicateIds ↔ p < ir.predicates.length ∧ (ir.predicate p).body.isCross = true := by
  simp only [crossPredicateIds, List.mem_filter, List.mem_range, predicateT_eq]

/-- Equal declared types have equal type-node projections, independently of packing nodes. -/
theorem valueType_nodeName {v : ℕ} {type : VType} (h : (ir.value v).type = type) :
    (ir.value v).type.nodeName = type.nodeName := congrArg VType.nodeName h

namespace ShapeClaim

/-- A checked source-challenge summary is exhaustive. -/
theorem sourceChallenges_sound {ids : List ℕ}
    (h : (sourceChallenges ids).check ir = true) : ir.sourceChallengeIds = ids :=
  of_decide_eq_true h

/-- A checked full-field challenge has the claimed scalar parts. -/
theorem fullChallenge_sound {c field size : ℕ}
    (h : (fullChallenge c field size).check ir = true) :
    c < ir.challenges.length ∧ (ir.challenge c).sampler = .full ∧
      ir.chalField c = field ∧ (ir.challenge c).size = size := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨h.1.1.1, ?_, h.1.2, h.2⟩
  have hs := h.1.1.2
  cases he : (ir.challenge c).sampler <;> simp_all only [Challenge.isFullB, Bool.false_eq_true, and_false, false_and]

/-- A checked declared type includes validity of the value index. -/
theorem valueType_sound {v : ℕ} {type : VType}
    (h : (valueType v type).check ir = true) :
    v < ir.values.length ∧ (ir.value v).type = type := by
  simpa only [check, Bool.and_eq_true, decide_eq_true_eq, valueT_eq] using h

/-- The checked public-expression part identifies its exact body. -/
theorem kindExprEq_sound {v : ℕ} {e : Expr}
    (h : (kindExprEq v e).check ir = true) : (ir.value v).kind = .pub (.expr e) := by
  rw [check, valueT_eq] at h
  revert h
  rcases (ir.value v).kind with _ | (_ | _ | e') | _ | _ | _ | _ | _ | _ | _ <;>
    simp only [Kind.isExprEqB, Bool.false_eq_true, false_implies]
  exact fun h => by rw [Expr.eq_of_beq h]


/-- A checked cross-field summary covers every cross-field predicate. -/
theorem crossPredicates_sound {ids : List ℕ}
    (h : (crossPredicates ids).check ir = true) : ir.crossPredicateIds = ids :=
  of_decide_eq_true h

/-- A checked statement summary covers every member check. -/
theorem statementChecks_sound {checks : List MemberCheck}
    (h : (statementChecks checks).check ir = true) : ir.statement.checks = checks :=
  of_decide_eq_true h

/-- A checked range summary covers every declared statement-value bound. -/
theorem statementRanges_sound {ranges : List (ℕ × ℕ)}
    (h : (statementRanges ranges).check ir = true) : ir.declaredRanges = ranges :=
  of_decide_eq_true h

/-- Checked finite metadata includes a valid value index. -/
theorem valueHeader_sound {v : ℕ} {header : ValueShape}
    (h : (valueHeader v header).check ir = true) :
    v < ir.values.length ∧ ir.valueShape v = header := by
  simpa only [check, Bool.and_eq_true, decide_eq_true_eq, valueShapeT_eq] using h

/-- A checked value count is the actual length. -/
theorem valueCount_sound {n : ℕ} (h : (valueCount n).check ir = true) :
    ir.values.length = n := by
  simpa only [check, beq_iff_eq] using h

/-- A checked predicate count is the actual length. -/
theorem predicateCount_sound {n : ℕ} (h : (predicateCount n).check ir = true) :
    ir.predicates.length = n := by
  simpa only [check, beq_iff_eq] using h

/-- A checked expr count is the actual length. -/
theorem exprCount_sound {n : ℕ} (h : (exprCount n).check ir = true) :
    ir.exprs.length = n := by
  simpa only [check, beq_iff_eq] using h

/-- A checked domain count is the actual length. -/
theorem domainCount_sound {n : ℕ} (h : (domainCount n).check ir = true) :
    ir.domains.length = n := by
  simpa only [check, beq_iff_eq] using h

/-- A checked challenge count is the actual length. -/
theorem challengeCount_sound {n : ℕ} (h : (challengeCount n).check ir = true) :
    ir.challenges.length = n := by
  simpa only [check, beq_iff_eq] using h

/-- Checked ownership includes a valid predicate index. -/
theorem predicateRole_sound {p : ℕ} {role : PredRole}
    (h : (predicateRole p role).check ir = true) :
    p < ir.predicates.length ∧ (ir.predicate p).role = role := by
  simpa only [check, Bool.and_eq_true, decide_eq_true_eq, predicateT_eq] using h

/-- **`kindConstant v entries`**: value `v` is the constant vector `entries`. -/
theorem kindConstant_sound {v : ℕ} {entries : List ℕ}
    (h : (kindConstant v entries).check ir = true) :
    (ir.value v).kind = .constant entries := by
  rw [check, valueT_eq] at h
  revert h
  cases (ir.value v).kind <;> simp [Kind.isConstantB]

/-- A checked pad-copy target and map determine its kind. -/
theorem kindPadCopy_sound {v w : ℕ} {map : String}
    (h : (kindPadCopy v w map).check ir = true) :
    (ir.value v).kind = .padCopy w map := by
  rw [check, valueT_eq] at h
  revert h
  cases (ir.value v).kind <;> simp [Kind.isPadCopyB]

/-- Checked field ownership covers every valid private cell in that field. -/
theorem privateFieldSources_sound {field : ℕ}
    (h : (privateFieldSources field).check ir = true) :
    ∀ v, v < ir.values.length → ir.privCellB v = true →
      ir.valueField v = field → ir.IsSourceValue v := by
  intro v hv hp hf
  have ha := List.all_eq_true.mp h v (List.mem_range.mpr hv)
  simpa only [hp, hf, beq_self_eq_true, Bool.not_true, Bool.false_or, decide_eq_true_eq] using ha

/-- **`kindPriv v`**: value `v` is committed in phase `0`. -/
theorem kindPriv_sound {v : ℕ} (h : (kindPriv v).check ir = true) : (ir.value v).kind = .priv := by
  rw [check, valueT_eq] at h
  revert h
  cases (ir.value v).kind <;> simp [Kind.isPrivB]

/-- **`kindOpaque v name args`**: value `v` is the opaque public value `name` of `args`. -/
theorem kindOpaque_sound {v : ℕ} {name : String} {args : List ℕ}
    (h : (kindOpaque v name args).check ir = true) :
    (ir.value v).kind = .pub (.opaque name args) := by
  rw [check, valueT_eq] at h
  revert h
  rcases (ir.value v).kind with _ | (_ | ⟨n, a⟩ | _) | _ | _ | _ | _ | _ | _ | _ <;>
    simp [Kind.isOpaqueB]

/-- **`kindChallenge v c`**: value `v` is the challenge `c`. -/
theorem kindChallenge_sound {v c : ℕ} (h : (kindChallenge v c).check ir = true) :
    (ir.value v).kind = .challenge c := by
  rw [check, valueT_eq] at h
  revert h
  cases (ir.value v).kind <;> simp [Kind.isChallengeB]

/-- **`kindExpr v`**: value `v` is a public expression. -/
theorem kindExpr_sound {v : ℕ} (h : (kindExpr v).check ir = true) :
    ∃ e, (ir.value v).kind = .pub (.expr e) := by
  rw [check, valueT_eq] at h
  revert h
  rcases (ir.value v).kind with _ | (_ | _ | e) | _ | _ | _ | _ | _ | _ | _ <;>
    simp [Kind.isExprB]

/-- **`kindBits v w sel`**: value `v` is the bit view of the words `sel` of value `w`. -/
theorem kindBits_sound {v w : ℕ} {sel : IndexMap} (h : (kindBits v w sel).check ir = true) :
    (ir.value v).kind = .bits w sel := by
  rw [check, valueT_eq] at h
  revert h
  rcases (ir.value v).kind with _ | _ | _ | _ | _ | ⟨w', sel'⟩ | _ | _ | _ <;>
    simp only [Kind.isBitsB, Bool.and_eq_true, beq_iff_eq, Bool.false_eq_true, false_implies]
  rintro ⟨rfl, rfl⟩
  rfl

/-- **`kindBound v e`**: value `v` is the bound value read as `e`. -/
theorem kindBound_sound {v : ℕ} {e : Expr} (h : (kindBound v e).check ir = true) :
    (ir.value v).kind = .bound e := by
  rw [check, valueT_eq] at h
  revert h
  rcases (ir.value v).kind with _ | _ | _ | _ | _ | _ | _ | _ | e' <;> simp only [Kind.isBoundB,
    Bool.false_eq_true, false_implies]
  exact fun h => by rw [Expr.eq_of_beq h]

/-- **`exprEq k e`**: shared expression `k` is `e`. -/
theorem exprEq_sound {k : ℕ} {e : Expr} (h : (exprEq k e).check ir = true) : ir.expr k = e :=
  Expr.eq_of_beq h

/-- **Equality metadata is checked independently of the large body expressions.** -/
theorem equalHeader_sound {p : ℕ} {header : Predicate.EqualHeader}
    (h : (equalHeader p header).check ir = true) :
    (ir.predicate p).equalHeader = header := by
  rw [check, predicateT_eq] at h
  exact of_decide_eq_true h

/-- **`equalParts p d lhs rhs`**: predicate `p` is the field equality `lhs = rhs` in domain `d`. -/
theorem equalParts_sound {p d : ℕ} {lhs rhs : Expr} (h : (equalParts p d lhs rhs).check ir = true) :
    ∃ t, (ir.predicate p).body = .equal d lhs rhs t := by
  rw [check, predicateT_eq] at h
  revert h
  rcases (ir.predicate p).body with ⟨d', l, r, t⟩ | _ | _ | _ <;> simp only [PredBody.isEqualB,
    Bool.and_eq_true, beq_iff_eq, Bool.false_eq_true, false_implies]
  rintro ⟨⟨rfl, hl⟩, hr⟩
  exact ⟨t, by rw [Expr.eq_of_beq hl, Expr.eq_of_beq hr]⟩

/-- **`memParts p d records set`**: predicate `p` is the lookup of `records` in `set` in domain
`d`. -/
theorem memParts_sound {p d : ℕ} {records : List Expr} {set : InSet}
    (h : (memParts p d records set).check ir = true) :
    ∃ r, (ir.predicate p).body = .mem d records set r := by
  rw [check, predicateT_eq] at h
  revert h
  rcases (ir.predicate p).body with _ | ⟨d', rs, s, r⟩ | _ | _ <;> simp only [PredBody.isMemB,
    Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.false_eq_true, false_implies]
  rintro ⟨⟨rfl, hr⟩, rfl⟩
  exact ⟨r, by rw [Expr.eq_of_beqList hr]⟩

/-- **`crossParts p dx x dy y kind`**: predicate `p` is the cross-field equality of `x` in domain
`dx` and `y` in domain `dy`, of kind `kind`. -/
theorem crossParts_sound {p dx dy : ℕ} {x y : Expr} {kind : CrossKind}
    (h : (crossParts p dx x dy y kind).check ir = true) :
    ∃ c, (ir.predicate p).body = .cross dx x dy y kind c := by
  rw [check, predicateT_eq] at h
  revert h
  rcases (ir.predicate p).body with _ | _ | _ | ⟨dx', x', dy', y', k, c⟩ <;>
    simp only [PredBody.isCrossB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
      Bool.false_eq_true, false_implies]
  rintro ⟨⟨⟨⟨rfl, hx⟩, rfl⟩, hy⟩, rfl⟩
  exact ⟨c, by rw [Expr.eq_of_beq hx, Expr.eq_of_beq hy]⟩

/-- **Structurally equal optional expressions are equal.** -/
theorem _root_.GordieHowe.RealizedProgram.Expr.eq_of_beqOpt :
    ∀ {e e' : Option Expr}, Expr.beqOpt e e' = true → e = e'
  | none, none, _ => rfl
  | some _, some _, h => by rw [Expr.eq_of_beq h]
  | none, some _, h | some _, none, h => absurd h Bool.false_ne_true

/-- **`modParts p d q lhs rhs form quotient quotientLo qmax`**: predicate `p` is the congruence
`lhs ≡ rhs (mod q)` in domain `d`, its realization of the given form, quotient, quotient's lower
end and range. -/
theorem modParts_sound {p d q : ℕ} {lhs rhs : Expr} {form : ModForm} {quotient : Option Expr}
    {quotientLo : ℤ} {qmax : ℕ}
    (h : (modParts p d q lhs rhs form quotient quotientLo qmax).check ir = true) :
    ∃ real, (ir.predicate p).body = .mod d q lhs rhs real ∧ real.form = form ∧
      real.quotient = quotient ∧ real.quotientLo = quotientLo ∧ real.qmax = qmax := by
  rw [check, predicateT_eq] at h
  revert h
  rcases (ir.predicate p).body with _ | _ | ⟨d', q', l, r, real⟩ | _ <;> simp only [PredBody.isModB,
    Bool.and_eq_true, beq_iff_eq, Bool.false_eq_true, false_implies]
  rintro ⟨⟨⟨⟨⟨⟨⟨rfl, rfl⟩, hl⟩, hr⟩, hf⟩, hq⟩, hlo⟩, hm⟩
  exact ⟨real, by rw [Expr.eq_of_beq hl, Expr.eq_of_beq hr], hf, Expr.eq_of_beqOpt hq, hlo, hm⟩

theorem sourcePredicates_sound {lo hi : ℕ} (h : (sourcePredicates lo hi).check ir = true) :
    ∀ p, lo ≤ p → p ≤ hi → p < ir.predicates.length ∧ ir.inSource (ir.predicate p) = true := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range'_1] at h
  intro p h1 h2
  exact ⟨by omega, h.2 p ⟨h1, by omega⟩⟩

theorem exprTable_sound {es : List Expr} (h : (exprTable es).check ir = true) :
    es.length ≤ ir.exprs.length ∧ ∀ k < es.length, ir.expr k = es.getD k default := by
  simp only [check, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_range] at h
  exact ⟨h.1, fun k hk => Expr.eq_of_beq (h.2 k hk)⟩

/-- **What a shape claim states** of the program. -/
def Holds (ir : RealizedProgram) : ShapeClaim → Prop
  | .exprTable es => es.length ≤ ir.exprs.length ∧ ∀ k < es.length, ir.expr k = es.getD k default
  | .embedding d => ∀ σ, d.Agrees σ → d.Holds ir σ
  | .phaseCount n => ir.phases = n
  | .sourcePredicates lo hi => ∀ p, lo ≤ p → p ≤ hi →
      p < ir.predicates.length ∧ ir.inSource (ir.predicate p) = true
  | .sourceChallenges ids => ir.sourceChallengeIds = ids
  | .fullChallenge c field size => c < ir.challenges.length ∧
      (ir.challenge c).sampler = .full ∧ ir.chalField c = field ∧ (ir.challenge c).size = size
  | .valueType v type => v < ir.values.length ∧ (ir.value v).type = type
  | .kindExprEq v e => (ir.value v).kind = .pub (.expr e)
  | .crossPredicates ids => ir.crossPredicateIds = ids
  | .statementChecks checks => ir.statement.checks = checks
  | .statementRanges ranges => ir.declaredRanges = ranges
  | .valueHeader v header => v < ir.values.length ∧ ir.valueShape v = header
  | .valueCount n => ir.values.length = n
  | .predicateCount n => ir.predicates.length = n
  | .exprCount n => ir.exprs.length = n
  | .domainCount n => ir.domains.length = n
  | .challengeCount n => ir.challenges.length = n
  | .predicateRole p role => p < ir.predicates.length ∧ (ir.predicate p).role = role
  | .kindConstant v entries => (ir.value v).kind = .constant entries
  | .privateFieldSources field => ∀ v, v < ir.values.length → ir.privCellB v = true →
      ir.valueField v = field → ir.IsSourceValue v
  | .kindPadCopy v w map => (ir.value v).kind = .padCopy w map
  | .kindPriv v => (ir.value v).kind = .priv
  | .kindOpaque v name args => (ir.value v).kind = .pub (.opaque name args)
  | .kindChallenge v c => (ir.value v).kind = .challenge c
  | .kindExpr v => ∃ e, (ir.value v).kind = .pub (.expr e)
  | .kindBits v w sel => (ir.value v).kind = .bits w sel
  | .kindBound v e => (ir.value v).kind = .bound e
  | .exprEq k e => ir.expr k = e
  | .equalHeader p header => (ir.predicate p).equalHeader = header
  | .equalParts p d lhs rhs => ∃ t, (ir.predicate p).body = .equal d lhs rhs t
  | .memParts p d records set => ∃ r, (ir.predicate p).body = .mem d records set r
  | .crossParts p dx x dy y kind => ∃ c, (ir.predicate p).body = .cross dx x dy y kind c
  | .modParts p d q lhs rhs form quotient quotientLo qmax =>
    ∃ real, (ir.predicate p).body = .mod d q lhs rhs real ∧ real.form = form ∧
      real.quotient = quotient ∧ real.quotientLo = quotientLo ∧ real.qmax = qmax
  | .family _ _ => False

/-- **What a claim states, a family at each of its rows.** -/
def HoldsFamily (ir : RealizedProgram) : ShapeClaim → Prop
  | .family rows template => ∀ r ∈ rows, ∀ c ∈ template, Holds ir (c.atRow r)
  | c => Holds ir c

/-- **A claim that checks holds.** -/
theorem holds_of_check : ∀ {c : ShapeClaim}, c.check ir = true → c.Holds ir
  | .embedding _, h => fun _ ha => embeddingB_sound h ha
  | .exprTable _, h => exprTable_sound h
  | .phaseCount n, h => beq_iff_eq.mp (show (ir.phases == n) = true from h)
  | .sourcePredicates _ _, h => sourcePredicates_sound h
  | .sourceChallenges _, h => sourceChallenges_sound h
  | .fullChallenge _ _ _, h => fullChallenge_sound h
  | .valueType _ _, h => valueType_sound h
  | .kindExprEq _ _, h => kindExprEq_sound h
  | .crossPredicates _, h => crossPredicates_sound h
  | .statementChecks _, h => statementChecks_sound h
  | .statementRanges _, h => statementRanges_sound h
  | .valueHeader _ _, h => valueHeader_sound h
  | .valueCount _, h => valueCount_sound h
  | .predicateCount _, h => predicateCount_sound h
  | .exprCount _, h => exprCount_sound h
  | .domainCount _, h => domainCount_sound h
  | .challengeCount _, h => challengeCount_sound h
  | .predicateRole _ _, h => predicateRole_sound h
  | .kindConstant _ _, h => kindConstant_sound h
  | .privateFieldSources _, h => privateFieldSources_sound h
  | .kindPadCopy _ _ _, h => kindPadCopy_sound h
  | .kindPriv _, h => kindPriv_sound h
  | .kindOpaque _ _ _, h => kindOpaque_sound h
  | .kindChallenge _ _, h => kindChallenge_sound h
  | .kindExpr _, h => kindExpr_sound h
  | .kindBits _ _ _, h => kindBits_sound h
  | .kindBound _ _, h => kindBound_sound h
  | .exprEq _ _, h => exprEq_sound h
  | .equalHeader _ _, h => equalHeader_sound h
  | .equalParts _ _ _ _, h => equalParts_sound h
  | .memParts _ _ _ _, h => memParts_sound h
  | .crossParts _ _ _ _ _ _, h => crossParts_sound h
  | .modParts _ _ _ _ _ _ _ _ _, h => modParts_sound h
  | .family _ _, h => nomatch h

/-- **A claim or family that checks holds.** -/
theorem holdsFamily_of_checkFamily {c : ShapeClaim} (h : c.checkFamily ir = true) :
    c.HoldsFamily ir := by
  cases c with
  | family rows template =>
    intro r hr c hc
    rw [checkFamily, allK_eq, List.all_eq_true] at h
    have hrow := h r hr
    rw [allK_eq, List.all_eq_true] at hrow
    exact holds_of_check (hrow c hc)
  | _ =>
    simp only [checkFamily] at h
    exact holds_of_check h

end ShapeClaim

/-- **The shapes condition**: every claim of the list holds of the program. -/
def ShapesHold (ir : RealizedProgram) (cs : List ShapeClaim) : Prop :=
  ∀ c ∈ cs, c.HoldsFamily ir

/-- **The shapes check is sound** (`shapesB`, the part's soundness lemma). -/
theorem shapes_sound {cs : List ShapeClaim} (h : ir.shapesB cs = true) : ShapesHold ir cs :=
  fun _ hc => ShapeClaim.holdsFamily_of_checkFamily
    (by rw [shapesB, allK_eq, List.all_eq_true] at h; exact h _ hc)

namespace ShapesHold

variable {cs : List ShapeClaim} (h : ShapesHold ir cs) {k : ℕ}
include h

/-- **The claim at position `k`** holds. -/
theorem at_ {c : ShapeClaim} (hk : cs[k]? = some c) : c.HoldsFamily ir :=
  h c (List.mem_of_getElem? hk)

/-- **Template claim `j` of the family at position `k`**, at one of its rows. -/
theorem family {rows : List (List ℕ)} {template : List ShapeClaim} {j : ℕ} {c : ShapeClaim}
    {r : List ℕ} (hk : cs[k]? = some (.family rows template)) (hj : template[j]? = some c)
    (hr : r ∈ rows) : (c.atRow r).Holds ir :=
  h.at_ hk r hr c (List.mem_of_getElem? hj)

/-- The program holds the part the data lists, at every renaming that agrees with its data. -/
theorem embedding {d : EmbedData} (hk : cs[k]? = some (.embedding d)) :
    ∀ σ, d.Agrees σ → d.Holds ir σ :=
  h.at_ hk

/-- The program's first shared expressions. -/
theorem exprTable {es : List Expr} (hk : cs[k]? = some (.exprTable es)) :
    es.length ≤ ir.exprs.length ∧ ∀ j < es.length, ir.expr j = es.getD j default :=
  h.at_ hk

/-- The program's exact number of challenge phases. -/
theorem phaseCount {n : ℕ} (hk : cs[k]? = some (.phaseCount n)) : ir.phases = n :=
  h.at_ hk

/-- A checked range of source predicates. -/
theorem sourcePredicates {lo hi : ℕ} (hk : cs[k]? = some (.sourcePredicates lo hi)) :
    ∀ p, lo ≤ p → p ≤ hi → p < ir.predicates.length ∧ ir.inSource (ir.predicate p) = true :=
  h.at_ hk

/-- All cross-field predicate indices, from their checked summary. -/
theorem crossPredicates {ids : List ℕ}
    (hk : cs[k]? = some (.crossPredicates ids)) : ir.crossPredicateIds = ids := h.at_ hk

/-- The complete member-check list, from its checked summary. -/
theorem statementChecks {checks : List MemberCheck}
    (hk : cs[k]? = some (.statementChecks checks)) : ir.statement.checks = checks := h.at_ hk

/-- All declared statement-value bounds, from their checked summary. -/
theorem statementRanges {ranges : List (ℕ × ℕ)}
    (hk : cs[k]? = some (.statementRanges ranges)) : ir.declaredRanges = ranges := h.at_ hk

/-- Finite metadata at a valid value index, from a checked named claim. -/
theorem valueHeader {v : ℕ} {header : ValueShape}
    (hk : cs[k]? = some (.valueHeader v header)) :
    v < ir.values.length ∧ ir.valueShape v = header := h.at_ hk

/-- The exhaustive checked source-challenge list. -/
theorem sourceChallenges {ids : List ℕ} (hk : cs[k]? = some (.sourceChallenges ids)) :
    ir.sourceChallengeIds = ids := h.at_ hk

/-- Full-field sampling and scalar parts, from a checked named challenge. -/
theorem fullChallenge {c field size : ℕ} (hk : cs[k]? = some (.fullChallenge c field size)) :
    c < ir.challenges.length ∧ (ir.challenge c).sampler = .full ∧
      ir.chalField c = field ∧ (ir.challenge c).size = size := h.at_ hk

/-- The declared type at a valid named value, independently of its packing node. -/
theorem valueType {v : ℕ} {type : VType} (hk : cs[k]? = some (.valueType v type)) :
    v < ir.values.length ∧ (ir.value v).type = type := h.at_ hk

/-- The exact checked public-expression body. -/
theorem kindExprEq {v : ℕ} {e : Expr} (hk : cs[k]? = some (.kindExprEq v e)) :
    (ir.value v).kind = .pub (.expr e) := h.at_ hk

/-- The actual number of values, from a checked count claim. -/
theorem valueCount {n : ℕ} (hk : cs[k]? = some (.valueCount n)) :
    ir.values.length = n := h.at_ hk

/-- The actual number of predicates, from a checked count claim. -/
theorem predicateCount {n : ℕ} (hk : cs[k]? = some (.predicateCount n)) :
    ir.predicates.length = n := h.at_ hk

/-- The actual number of shared expressions, from a checked count claim. -/
theorem exprCount {n : ℕ} (hk : cs[k]? = some (.exprCount n)) :
    ir.exprs.length = n := h.at_ hk

/-- The actual number of domains, from a checked count claim. -/
theorem domainCount {n : ℕ} (hk : cs[k]? = some (.domainCount n)) :
    ir.domains.length = n := h.at_ hk

/-- The actual number of challenges, from a checked count claim. -/
theorem challengeCount {n : ℕ} (hk : cs[k]? = some (.challengeCount n)) :
    ir.challenges.length = n := h.at_ hk

/-- Ownership at a valid predicate index, from a checked named claim. -/
theorem predicateRole {p : ℕ} {role : PredRole}
    (hk : cs[k]? = some (.predicateRole p role)) :
    p < ir.predicates.length ∧ (ir.predicate p).role = role := h.at_ hk

/-- **A constant vector**, the claim at position `k`. -/
theorem kindConstant {v : ℕ} {entries : List ℕ}
    (hk : cs[k]? = some (.kindConstant v entries)) :
    (ir.value v).kind = .constant entries :=
  h.at_ hk

/-- A pad-copy kind, from its checked claim. -/
theorem kindPadCopy {v w : ℕ} {map : String}
    (hk : cs[k]? = some (.kindPadCopy v w map)) :
    (ir.value v).kind = .padCopy w map := h.at_ hk

/-- Every private cell of a checked field has source ownership. -/
theorem privateFieldSources {field : ℕ}
    (hk : cs[k]? = some (.privateFieldSources field)) :
    ∀ v, v < ir.values.length → ir.privCellB v = true →
      ir.valueField v = field → ir.IsSourceValue v := h.at_ hk

/-- **A committed value**, the claim at position `k`. -/
theorem kindPriv {v : ℕ} (hk : cs[k]? = some (.kindPriv v)) : (ir.value v).kind = .priv :=
  h.at_ hk

/-- **An opaque public value**, the claim at position `k`. -/
theorem kindOpaque {v : ℕ} {name : String} {args : List ℕ}
    (hk : cs[k]? = some (.kindOpaque v name args)) :
    (ir.value v).kind = .pub (.opaque name args) :=
  h.at_ hk

/-- **A challenge**, the claim at position `k`. -/
theorem kindChallenge {v c : ℕ} (hk : cs[k]? = some (.kindChallenge v c)) :
    (ir.value v).kind = .challenge c :=
  h.at_ hk

/-- **A public expression**, the claim at position `k`. -/
theorem kindExpr {v : ℕ} (hk : cs[k]? = some (.kindExpr v)) :
    ∃ e, (ir.value v).kind = .pub (.expr e) :=
  h.at_ hk

/-- **A bit view**, the claim at position `k`. -/
theorem kindBits {v w : ℕ} {sel : IndexMap} (hk : cs[k]? = some (.kindBits v w sel)) :
    (ir.value v).kind = .bits w sel :=
  h.at_ hk

/-- **A bound value**, the claim at position `k`. -/
theorem kindBound {v : ℕ} {e : Expr} (hk : cs[k]? = some (.kindBound v e)) :
    (ir.value v).kind = .bound e :=
  h.at_ hk

/-- **A shared expression**, the claim at position `k`. -/
theorem exprEq {j : ℕ} {e : Expr} (hk : cs[k]? = some (.exprEq j e)) : ir.expr j = e :=
  h.at_ hk

/-- **Equality metadata**, the claim at position `k`. -/
theorem equalHeader {p : ℕ} {header : Predicate.EqualHeader}
    (hk : cs[k]? = some (.equalHeader p header)) :
    (ir.predicate p).equalHeader = header :=
  h.at_ hk

/-- **A field equality**, the claim at position `k`. -/
theorem equalParts {p d : ℕ} {lhs rhs : Expr} (hk : cs[k]? = some (.equalParts p d lhs rhs)) :
    ∃ t, (ir.predicate p).body = .equal d lhs rhs t :=
  h.at_ hk

/-- **A lookup**, the claim at position `k`. -/
theorem memParts {p d : ℕ} {records : List Expr} {set : InSet}
    (hk : cs[k]? = some (.memParts p d records set)) :
    ∃ r, (ir.predicate p).body = .mem d records set r :=
  h.at_ hk

/-- **A cross-field equality**, the claim at position `k`. -/
theorem crossParts {p dx dy : ℕ} {x y : Expr} {kind : CrossKind}
    (hk : cs[k]? = some (.crossParts p dx x dy y kind)) :
    ∃ c, (ir.predicate p).body = .cross dx x dy y kind c :=
  h.at_ hk

/-- **A congruence**, the claim at position `k`. -/
theorem modParts {p d q : ℕ} {lhs rhs : Expr} {form : ModForm} {quotient : Option Expr}
    {quotientLo : ℤ} {qmax : ℕ}
    (hk : cs[k]? = some (.modParts p d q lhs rhs form quotient quotientLo qmax)) :
    ∃ real, (ir.predicate p).body = .mod d q lhs rhs real ∧ real.form = form ∧
      real.quotient = quotient ∧ real.quotientLo = quotientLo ∧ real.qmax = qmax :=
  h.at_ hk

end ShapesHold

end GordieHowe.RealizedProgram

namespace GordieHowe.ProgramData

open RealizedProgram

/-- **The shapes part is sound**: the shapes of a program's data hold of its program. -/
theorem shapes_sound (d : ProgramData) (h : d.shapesB = true) : ShapesHold d.program d.shapes :=
  RealizedProgram.shapes_sound h

end GordieHowe.ProgramData
