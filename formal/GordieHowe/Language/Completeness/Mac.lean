-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Completeness.Digits

@[expose] public section

/-!
# GordieHowe: completeness certificates, the honest MACs

The honest MAC values with their generators read off a completeness certificate: at the honest
environment of the certificate (`genLateOf`) a generated tag, digit-form accumulator, lower digit,
grouped accumulator and grouped quotient digit read as their generators read the honest environment
(`macTagC_honest`, `reader_digitsAccC_honest`, `reader_lowDigitC_honest`, `reader_accC_honest`,
`reader_quotDigitC_honest`), and a MAC with an ungrouped digit tail (`DigitsMacC`), a one-digit
tail (`OneDigitMacC`) or a grouped tail (`GroupedMacC`) satisfies its predicates
(`DigitsMacC.role_holds`, `OneDigitMacC.role_holds`, `GroupedMacC.role_holds`).
-/

namespace GordieHowe.RealizedProgram

open Export ProofSystem.PhaseLayout IOP
open scoped NNReal

section

variable {ir : RealizedProgram} {I : Interp} {primeNodes : ℕ → List String}

section HonestEnv

variable {Inp : Type} {G : Gens} (hG : ir.CGenFacts I G) (stmtOf val : Inp → ir.Valuation I)
  (SL : ir.SrcLate I Inp) (y : Inp) (c : ∀ k, (ir.layout I).Ch k) (π : (ir.layout I).Pads)

set_option hygiene false in
/-- The honest environment of the honest inputs `y`. -/
local notation "HE" => ir.honestEnv I (stmtOf y) (val y) (ir.genLateOf I hG stmtOf val SL y) c π

set_option hygiene false in
/-- The source environment of the honest inputs `y` with the source late values. -/
local notation "SE" => ir.srcEnvL I (stmtOf y) (val y) (SL.late y c) c π

/-- **The honest environment reads a generated value other than a late histogram as its generator
reads the source environment** (`genSrcOf`; `reader_honestEnv_genSrc`): the honest late value is the
generated value there (`honestEnvC_late_eq`). -/
theorem reader_honestEnvC_genSrcOf {v : ℕ} (hv : v < ir.values.length) (hl : ir.IsLate v)
    (hns : ¬ ir.IsSourceValue v) (hhist : ∀ t g, G.at v ≠ .lateHist t g) {n : ℕ}
    (hn : n < (ir.value v).size) :
    ir.reader HE v n = ir.genSrcOf G SE v n := by
  rw [reader_of_late _ (kind_of_isLate hl), honestEnvC_late_eq hG stmtOf val SL y c π _ hv hl hns,
    genValOf]
  rw [ite_eq_left_of_eq_true _ _ (eq_true hn)]
  split
  · rename_i t g h
    exact absurd h (hhist t g)
  · rfl

/-- **Values reading no late value read alike** at the source environment and the honest
environment (`reader_honestEnvC_srcEnvL_of_noGen`). -/
theorem reader_srcEnvL_eq_honestEnvC {N : List ℕ} (hN : ∀ w ∈ N, ir.NoLateRead w) :
    ∀ w ∈ N, ir.reader SE w = ir.reader HE w := fun w hw =>
  (reader_honestEnvC_srcEnvL_of_noGen hG stmtOf val SL y c π (hN w hw).noGen).symm

/-- **The honest tag is the MAC's honest tag** (`MacTagAt`; `macTag_honest`) at the honest
environment: the tag's generated value (`tagGen`, its generator the tag of the cross-field `equal`
`pid`) at the source environment, which reads the `x` operand alike (`hx`: it reads no late
value). -/
theorem macTagC_honest {pid dx : ℕ} {x : Expr} {dy : ℕ} {y' : Expr} {k : CrossKind}
    {real : MacRealization} (hb : (ir.predicate pid).body = .cross dx x dy y' k real)
    (htagB : ir.macTagB real = true) (hgen : G.at real.tag = .tag pid)
    (hns : ¬ ir.IsSourceValue real.tag) (hlate : ir.IsLate real.tag)
    (hx : ∀ v ∈ ir.exprNodes x, ir.NoLateRead v) :
    ir.MacTagAt (ir.reader HE) dx x real (castElt ((HE).chal real.key 0)) := by
  have htag := htagB
  unfold macTagB at htag
  simp only [Bool.and_eq_true, decide_eq_true_eq] at htag
  obtain ⟨⟨⟨htl, htagf⟩, htsz⟩, -⟩ := htag
  have htg : (castElt (ir.reader HE real.tag 0) : (I real.macField).K) =
      ir.tagGen (ir.reader HE) dx x real (castElt ((HE).chal real.key 0)) := by
    rw [reader_honestEnvC_genSrcOf hG stmtOf val SL y c π htl hlate hns
      (by rw [hgen]; exact fun _ _ h => Gen.noConfusion h) htsz]
    simp only [genSrcOf, hgen, hb, ite_true]
    rw [castElt_castElt_of_eq htagf.symm,
      tagGen_congr (rd' := ir.reader HE) (reader_srcEnvL_eq_honestEnvC hG stmtOf val SL y c π hx)]
    rfl
  unfold MacTagAt
  split
  · rename_i hbx
    unfold MacHHoldsAt
    rw [htg]
    simp only [tagGen, hbx]
  · rename_i bx hbx
    unfold MacTwoTagAt
    rw [htg]
    simp only [tagGen, hbx]

/-- **The honest accumulator of an ungrouped digit-form `mod_q`** at the honest environment: its generated value (`digitsAccNat`, its generator the accumulator of
the `mod_q` `t`) at the source environment, which reads the left side alike (`hL`: it reads no late
value). -/
theorem reader_digitsAccC_honest {t d q : ℕ} {L R : Expr} {real : ModRealization} {acc : ℕ}
    (hb : (ir.predicate t).body = .mod d q L R real) (hgen : G.at acc = .digitsAcc t)
    (hns : ¬ ir.IsSourceValue acc) (hlt : acc < ir.values.length) (hlate : ir.IsLate acc)
    (hf : ir.valueField acc = ir.domainField d) (hL : ∀ v ∈ ir.exprNodes L, ir.NoLateRead v)
    {n : ℕ} (hn : n < (ir.value acc).size) :
    (castElt (ir.reader HE acc n) : (I (ir.domainField d)).K) =
      (ir.digitsAccNat (ir.reader HE) d L n : (I (ir.domainField d)).K) := by
  rw [reader_honestEnvC_genSrcOf hG stmtOf val SL y c π hlt hlate hns
    (by rw [hgen]; exact fun _ _ h => Gen.noConfusion h) hn]
  simp only [genSrcOf, hgen, hb, digitsAccNat,
    evalIntWith_congr (reader_srcEnvL_eq_honestEnvC hG stmtOf val SL y c π hL)]
  exact castElt_natCast hf _

/-- **The honest lower digit `j` of an ungrouped digit-form `mod_q`** at the honest environment: its generated value (`lowDigitNat`, its generator lower digit `j` of the
`mod_q` `t`) at the source environment, which reads the left side alike (`hL`). -/
theorem reader_lowDigitC_honest {t j d q : ℕ} {L R : Expr} {real : ModRealization} {low : ℕ}
    (hb : (ir.predicate t).body = .mod d q L R real) (hgen : G.at low = .lowDigit t j)
    (hns : ¬ ir.IsSourceValue low) (hlt : low < ir.values.length) (hlate : ir.IsLate low)
    (hf : ir.valueField low = ir.domainField d) (hL : ∀ v ∈ ir.exprNodes L, ir.NoLateRead v)
    {n : ℕ} (hn : n < (ir.value low).size) :
    (castElt (ir.reader HE low n) : (I (ir.domainField d)).K) =
      (ir.lowDigitNat (ir.reader HE) d q L real.radix j n : (I (ir.domainField d)).K) := by
  rw [reader_honestEnvC_genSrcOf hG stmtOf val SL y c π hlt hlate hns
    (by rw [hgen]; exact fun _ _ h => Gen.noConfusion h) hn]
  simp only [genSrcOf, hgen, hb, lowDigitNat, digitsAccNat,
    evalIntWith_congr (reader_srcEnvL_eq_honestEnvC hG stmtOf val SL y c π hL)]
  exact castElt_natCast hf _

/-- **The honest accumulators of a grouped `mod_q`** at the honest environment: their generated value (`accNat`, their generator the accumulators of the
`mod_q` `t`) at the source environment, which reads the powers and the operand alike (`hr`, `hy`:
they read no late value). -/
theorem reader_accC_honest {t d q : ℕ} {L R : Expr} {real : ModRealization} {Gm : GroupedMod}
    {u : MacUnits} {acc : ℕ} (hb : (ir.predicate t).body = .mod d q L R real)
    (hG' : real.grouped = some Gm) (hu : macUnits? L = some u) (hgen : G.at acc = .acc t)
    (hns : ¬ ir.IsSourceValue acc) (hlt : acc < ir.values.length) (hlate : ir.IsLate acc)
    (hf : ir.valueField acc = ir.domainField d) (hr : ir.NoLateRead u.powers)
    (hy : ∀ v ∈ ir.exprNodes u.operand, ir.NoLateRead v) {n : ℕ} (hn : n < (ir.value acc).size) :
    (castElt (ir.reader HE acc n) : (I (ir.domainField d)).K) =
      (ir.accNat (ir.reader HE) d u Gm n : (I (ir.domainField d)).K) := by
  rw [reader_honestEnvC_genSrcOf hG stmtOf val SL y c π hlt hlate hns
    (by rw [hgen]; exact fun _ _ h => Gen.noConfusion h) hn]
  simp only [genSrcOf, hgen, hb, hG', hu,
    accNat_congr (rd' := ir.reader HE)
      (reader_srcEnvL_eq_honestEnvC hG stmtOf val SL y c π (N := [u.powers])
        (by simpa using hr) _ (List.mem_singleton_self _))
      (reader_srcEnvL_eq_honestEnvC hG stmtOf val SL y c π hy)]
  exact castElt_natCast hf _

/-- **The honest quotient digits of a grouped `mod_q`** at the honest environment: their generated value (`digitNat`, their generator the quotient digits of
the `mod_q` `t`) at the source environment. -/
theorem reader_quotDigitC_honest {t d q : ℕ} {L R : Expr} {real : ModRealization}
    {Gm : GroupedMod} {u : MacUnits} {gq : ℕ} (hb : (ir.predicate t).body = .mod d q L R real)
    (hG' : real.grouped = some Gm) (hu : macUnits? L = some u) (hgen : G.at gq = .quotDigit t)
    (hns : ¬ ir.IsSourceValue gq) (hlt : gq < ir.values.length) (hlate : ir.IsLate gq)
    (hf : ir.valueField gq = ir.domainField d) (hr : ir.NoLateRead u.powers)
    (hy : ∀ v ∈ ir.exprNodes u.operand, ir.NoLateRead v) {n : ℕ} (hn : n < (ir.value gq).size) :
    (castElt (ir.reader HE gq n) : (I (ir.domainField d)).K) =
      (ir.digitNat (ir.reader HE) d q u Gm n : (I (ir.domainField d)).K) := by
  rw [reader_honestEnvC_genSrcOf hG stmtOf val SL y c π hlt hlate hns
    (by rw [hgen]; exact fun _ _ h => Gen.noConfusion h) hn]
  simp only [genSrcOf, hgen, hb, hG', hu,
    digitNat_congr (rd' := ir.reader HE)
      (reader_srcEnvL_eq_honestEnvC hG stmtOf val SL y c π (N := [u.powers])
        (by simpa using hr) _ (List.mem_singleton_self _))
      (reader_srcEnvL_eq_honestEnvC hG stmtOf val SL y c π hy)]
  exact castElt_natCast hf _

end HonestEnv

variable (ir primeNodes) in
/-- **A MAC check over a field with its tail, at the certificate's generators `G`** (compiler/mac.h;
`MacBase` with the tag's generator read off `G`): the cross-field `equal` `pid` with its MAC
realization, the check over a field that its tail performs (`MacFieldCheck`: the check over `y`'s
field for a hosted MAC, or over either field for a MAC no domain hosts), with the check's domain
`dy`, operand `y` and blind `sb`; its tail `t`, a `mod_2` whose left side is in the MAC unit form
with units `u` (the blind and the check's operand), and the facts every honest MAC needs: the tag
generated as this MAC's tag, a late value and no source value; the `x` operand, the cross-field
`equal`'s `y` operand, the check's operand and the powers read no late value; the blind is the tag's
pad copy. Data and properties of the program, decided per program. -/
structure MacBaseC (G : Gens) where
  /-- The cross-field `equal`. -/
  pid : ℕ
  /-- Its `x` domain (the H domain of a hosted MAC). -/
  dx : ℕ
  /-- Its `x` operand, the operand the tag is computed from. -/
  x : Expr
  /-- Its `y` domain. -/
  cdy : ℕ
  /-- Its `y` operand. -/
  cy : Expr
  /-- Its kind. -/
  k : CrossKind
  /-- Its MAC realization. -/
  real : MacRealization
  hpid : pid < ir.predicates.length
  hb : (ir.predicate pid).body = .cross dx x cdy cy k real
  /-- The check's domain. -/
  dy : ℕ
  /-- The check's operand. -/
  y : Expr
  /-- The check's blind. -/
  sb : ℕ
  hside : ir.MacFieldCheck primeNodes pid dx x cdy cy k real dy y sb
  /-- The check's domain is a domain of the program. -/
  dyLt : dy < ir.domains.length
  /-- The check's operand is well formed in its domain's field. -/
  yOk : ir.ExprOk (ir.domainField dy) y
  /-- The tail. -/
  t : ℕ
  ht : t < ir.predicates.length
  htB : ir.macTailAtB pid dy y sb real t = true
  /-- The tail's realization. -/
  realT : ModRealization
  /-- The tail's left side. -/
  L : Expr
  /-- The tail's right side. -/
  R : Expr
  hbt : (ir.predicate t).body = .mod dy 2 L R realT
  /-- The units. -/
  u : MacUnits
  hu : macUnits? L = some u
  /-- The tag is generated as this MAC's tag. -/
  tagGen : G.at real.tag = .tag pid
  /-- The tag is no source value. -/
  tagNotSource : ¬ ir.IsSourceValue real.tag
  tagLate : ir.IsLate real.tag
  xNoLate : ∀ v ∈ ir.exprNodes x, ir.NoLateRead v
  cyNoLate : ∀ v ∈ ir.exprNodes cy, ir.NoLateRead v
  yNoLate : ∀ v ∈ ir.exprNodes u.operand, ir.NoLateRead v
  powNoLate : ir.NoLateRead u.powers
  blindCopy : (ir.value sb).kind = .padCopy real.tag "polynomialBits"
  macChar : ir.charOf real.macField = 2


namespace MacBaseC

variable {G : Gens} (M : ir.MacBaseC primeNodes G)

/-- **The check is over one of the cross-field `equal`'s operands**: the `y` operand padded by zeros
(`zeroPadB`), or the `x` operand. -/
theorem side_eq : (M.dy = M.cdy ∧
      ir.zeroPadB (ir.domainField M.dy) (M.real.chunks * M.real.width) M.y M.cy = true) ∨
    (M.dy = M.dx ∧ M.y = M.x) := by
  rcases M.hside with ⟨-, h1, h2, -⟩ | ⟨b, -, -, -, -, -, h1, h2⟩ | ⟨bx, -, -, h, -, -, h1, h2⟩
  · exact .inl ⟨h1, h1 ▸ h2⟩
  · exact .inr ⟨h1, h2⟩
  · refine .inl ⟨h1, ?_⟩
    rw [h2]
    exact zeroPadB_self h.lenY

/-- **The check's operand reads bits where the cross-field `equal`'s operands do**: it is `y`
padded by zeros (`PadsTo`), or `x`. -/
theorem ybits_of {rd : ir.Valuation I} (hwf : ir.WellFormed) (hI : I.Registered ir)
    (hL : I.Lawful ir primeNodes)
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0))
    (hx : ∀ j < ir.exprLen M.x, ir.evalWith rd M.dx M.x j = 0 ∨ ir.evalWith rd M.dx M.x j = 1)
    (hy : ∀ j < ir.exprLen M.cy, ir.evalWith rd M.cdy M.cy j = 0 ∨ ir.evalWith rd M.cdy M.cy j = 1)
    (hc0 : 0 < ir.charOf (ir.domainField M.dy)) :
    ∀ j < ir.exprLen M.y, ir.evalWith rd M.dy M.y j = 0 ∨ ir.evalWith rd M.dy M.y j = 1 := by
  intro j hj
  rcases M.side_eq with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hpo := hwf.predicates _ (predicate_mem M.hpid)
    rw [M.hb] at hpo
    have hcyF := domainField_lt hwf (hpo.1 (M.cdy, M.cy) (by simp [PredBody.exprs])).1
    rw [h1] at h2 hc0 ⊢
    have hP := padsTo_of_zeroPadB hwf.refsOrdered hI hL hK hcyF hc0 h2
    have h3 := hP.2.2.1 j
    rw [evalPad_of_lt hj] at h3
    rw [h3]
    by_cases hjc : j < ir.exprLen M.cy
    · rw [evalPad_of_lt hjc]
      exact hy j hjc
    · rw [evalPad_of_le (Nat.le_of_not_lt hjc)]
      exact .inl rfl
  · rw [h2] at hj
    rw [h1, h2]
    exact hx j hj

/-- **The check's domain has characteristic above `2`.** -/
theorem char : 2 < ir.charOf (ir.domainField M.dy) := by
  rcases M.hside with ⟨hok, h1, -, -⟩ | ⟨b, -, -, -, -, hs, h1, -⟩ |
    ⟨bx, -, -, -, -, hs, h1, -⟩
  · rw [h1]
    exact hok.char
  · rw [h1]
    exact hs.char
  · rw [h1]
    exact hs.char

/-- **The chunk width is positive.** -/
theorem pos : 0 < M.real.width := by
  rcases M.hside with ⟨hok, -⟩ | ⟨b, -, -, h, -⟩ | ⟨bx, -, -, h, -⟩
  exacts [hok.pos, h.pos, h.pos]

/-- **The MAC field is a field of the program.** -/
theorem field : M.real.macField < ir.fields.length := by
  rcases M.hside with ⟨hok, -⟩ | ⟨b, -, -, h, -⟩ | ⟨bx, -, -, h, -⟩
  exacts [hok.field, h.field, h.field]

/-- **The tag** (`macTagB`). -/
theorem tag : ir.macTagB M.real = true := by
  rcases M.hside with ⟨hok, -⟩ | ⟨b, -, -, h, -⟩ | ⟨bx, -, -, h, -⟩
  exacts [hok.tag, h.tag, h.tag]

/-- **The cross-field `equal` compares bits.** -/
theorem width : M.k.width = 1 := by
  rcases M.hside with ⟨hok, -⟩ | ⟨b, -, -, h, -⟩ | ⟨bx, -, -, h, -⟩
  exacts [hok.width, h.width, h.width]

/-- **The `x` operand has at most `chunks · width` coordinates.** -/
theorem lenX : ir.exprLen M.x ≤ M.real.chunks * M.real.width := by
  rcases M.hside with ⟨hok, -⟩ | ⟨b, -, -, h, -⟩ | ⟨bx, -, -, h, -⟩
  exacts [hok.lenX, h.lenX.le, h.lenX.le]

/-- **The check's operand has `chunks · width` coordinates.** -/
theorem lenY : ir.exprLen M.y = M.real.chunks * M.real.width := by
  rcases M.hside with ⟨hok, -, h2, -⟩ | ⟨b, -, -, h, -, -, -, h2⟩ | ⟨bx, -, -, h, -, -, -, h2⟩
  · exact (zeroPadB_len h2).1
  · rw [h2]
    exact h.lenX
  · rw [h2]
    exact h.lenY

/-- **The check's blind** (`macBlindCoreB`). -/
theorem blindAt : ir.macBlindCoreB M.dy M.sb M.real = true := by
  rcases M.hside with ⟨-, h1, -, -, hbl⟩ | ⟨b, -, -, -, -, hs, h1, -⟩ |
    ⟨bx, -, -, -, -, hs, h1, -⟩
  · rw [h1]
    exact hbl
  · rw [h1]
    exact macBlindCoreB_of_at hs.blind
  · rw [h1]
    exact macBlindCoreB_of_at hs.blind

/-- **The check's blind is one of the MAC's blinds.** -/
theorem blind_mem : M.sb ∈ M.real.blind.toList ++ M.real.blindX.toList := by
  rcases M.hside with ⟨-, -, -, hbl, -⟩ | ⟨b, hbx, -⟩ | ⟨bx, -, hbl, -⟩
  · exact List.mem_append_left _ (by rw [hbl]; simp)
  · exact List.mem_append_right _ (by rw [hbx]; simp)
  · exact List.mem_append_left _ (by rw [hbl]; simp)

/-- **A MAC with an H predicate is hosted** (`MacTwoCore.noH`). -/
theorem hok_of_hPred {q : ℕ} (hq : M.real.hPredicate = some q) :
    ir.MacHostedCore M.pid M.dx M.x M.cdy M.cy M.k M.real := by
  rcases M.hside with ⟨hok, -⟩ | ⟨b, -, -, h, -⟩ | ⟨bx, -, -, h, -⟩
  · exact hok
  · rw [h.noH] at hq
    cases hq
  · rw [h.noH] at hq
    cases hq

/-- **The tail's units are the check's**: the blind, the operand, the chunk width and the chunks. -/
theorem units : M.u.blind = M.sb ∧ M.u.operand = M.y ∧ M.u.width = M.real.width ∧
    M.u.chunks = M.real.chunks ∧ ir.powersB M.u.powers M.real.key M.real.chunks M.real.macField = true := by
  have htB := M.htB
  unfold macTailAtB at htB
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at htB
  obtain ⟨-, htB⟩ := htB
  rw [M.hbt] at htB
  have hL := eq_of_macUnits? M.hu
  split at htB
  · rename_i d b r w nch taps y' tb real' hbt
    simp only [Bool.and_eq_true, beq_iff_eq] at htB
    obtain ⟨⟨⟨⟨⟨⟨⟨-, hbl⟩, hw⟩, hnch⟩, hy'⟩, hpow⟩, -⟩, -⟩ := htB
    simp only [PredBody.mod.injEq] at hbt
    obtain ⟨-, -, hLe, -, -⟩ := hbt
    rw [hL] at hLe
    simp only [Expr.add.injEq, Expr.leaf.injEq, Expr.apply.injEq, NamedOp.macConv.injEq] at hLe
    obtain ⟨hb', ⟨hr', hw', hn', ht'⟩, hy''⟩ := hLe
    refine ⟨by rw [hb', hbl], by rw [hy'', Expr.eq_of_beq hy'], by rw [hw', hw], by rw [hn', hnch],
      by rw [hr']; exact hpow⟩
  · cases htB

/-- **The tail's blind is one of the MAC's blinds.** -/
theorem ublind_mem : M.u.blind ∈ M.real.blind.toList ++ M.real.blindX.toList := by
  rw [M.units.1]
  exact M.blind_mem

/-- **The tail's blind is the tag's pad copy.** -/
theorem blindKind : (ir.value M.u.blind).kind = .padCopy M.real.tag "polynomialBits" := by
  rw [M.units.1]
  exact M.blindCopy

end MacBaseC

namespace MacBaseC

variable {G : Gens} (M : ir.MacBaseC primeNodes G)

/-- **The source facts a MAC check over a field's honest values need**, at a reader `rd`: the cross-field `equal`
holds, the `x` operand and the check's operand read bits, and the check's operand's integer reading
is its indicator. -/
structure Source (rd : ir.Valuation I) : Prop where
  /-- The cross-field `equal` holds. -/
  cross : ir.HoldsWith rd (.cross M.dx M.x M.cdy M.cy M.k M.real)
  /-- The `x` operand reads bits. -/
  xbits : ∀ i < ir.exprLen M.x, ir.evalWith rd M.dx M.x i = 0 ∨ ir.evalWith rd M.dx M.x i = 1
  /-- The check's operand reads bits. -/
  ybits : ∀ j < ir.exprLen M.y, ir.evalWith rd M.dy M.y j = 0 ∨ ir.evalWith rd M.dy M.y j = 1
  /-- The check's operand's integer reading is its indicator. -/
  yint : ∀ j < ir.exprLen M.y, ir.evalIntWith rd M.dy M.y j =
    if ir.evalWith rd M.dy M.y j = 1 then 1 else 0

/-- **A coordinate of the `x` operand is `1` exactly where the `y` operand's is**, where the
cross-field `equal` holds on bits (`hcyb`: the `y` operand's coordinates are bits) and both domains
have characteristic above `1`. -/
theorem Source.x_iff {rd : ir.Valuation I} (hwf : ir.WellFormed) (hL : I.Lawful ir primeNodes)
    (hS : M.Source rd) (hcx : 1 < ir.charOf (ir.domainField M.dx))
    (hcy : 1 < ir.charOf (ir.domainField M.cdy))
    (hcyb : ∀ i < ir.exprLen M.x, ir.evalWith rd M.cdy M.cy i = 0 ∨ ir.evalWith rd M.cdy M.cy i = 1)
    {i : ℕ} (hi : i < ir.exprLen M.x) :
    ir.evalWith rd M.dx M.x i = 1 ↔ ir.evalWith rd M.cdy M.cy i = 1 := by
  have hpo := hwf.predicates _ (predicate_mem M.hpid)
  rw [M.hb] at hpo
  have hdxF := domainField_lt hwf (hpo.1 (M.dx, M.x) (by simp [PredBody.exprs])).1
  have hdyF := domainField_lt hwf (hpo.1 (M.cdy, M.cy) (by simp [PredBody.exprs])).1
  simp only [charOf] at hcx hcy
  have hone : ∀ {a : ℕ}, a < ir.fields.length → 1 < (ir.field a).characteristic →
      (I a).toNat 1 = 1 := fun ha h1 => by simpa using hL.toNat_natCast _ ha 1 h1
  have hzero : ∀ {a : ℕ}, a < ir.fields.length → 1 < (ir.field a).characteristic →
      (I a).toNat 0 = 0 := fun ha h1 => by simpa using hL.toNat_natCast _ ha 0 (by omega)
  have hxlt : ∀ i < ir.exprLen M.x, (I (ir.domainField M.dx)).toNat (ir.evalWith rd M.dx M.x i) <
      2 ^ M.k.width := by
    intro i hi
    rw [M.width, pow_one]
    rcases hS.xbits i hi with h | h <;> rw [h]
    · rw [hzero hdxF hcx]; norm_num
    · rw [hone hdxF hcx]; norm_num
  have heq := hS.cross.2 hxlt _ hi
  rcases hS.xbits _ hi with hx | hx <;> rcases hcyb _ hi with hy | hy <;> rw [hx, hy] at heq ⊢
  · simp
  · rw [hzero hdxF hcx, hone hdyF hcy] at heq
    exact absurd heq (by norm_num)
  · rw [hone hdxF hcx, hzero hdyF hcy] at heq
    exact absurd heq (by norm_num)
  · simp

/-- **The honest tag is the MAC of the chunks of the check's operand**: where the tag is honest
(`MacTagAt`) and the source facts hold, `castElt U = Σ_c β^(c+1) · chunk_c(z)`, the chunks of the
coordinates of the check's operand `z` equal to `1`. Where `x`'s domain hosts the MAC, the H operand
read into the MAC field is its indicator (`macChunkH_eq_macChunkA`), which is the check's
(`Source.x_iff`); where no domain hosts it, the tag is the `x` operand's chunks, which are the
chunks of the check's operand or agree with them. -/
theorem Source.sideTag {rd : ir.Valuation I} (hwf : ir.WellFormed) (hI : I.Registered ir)
    (hL : I.Lawful ir primeNodes)
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0))
    (hS : M.Source rd) {β : (I M.real.macField).K} (hT : ir.MacTagAt rd M.dx M.x M.real β) :
    (castElt (rd M.real.tag 0) : (I M.real.macField).K) =
      ∑ c : Fin M.real.chunks, β ^ ((c : ℕ) + 1) *
        ir.macChunkA rd M.real.macField M.dy M.y M.real.width c := by
  have hpo := hwf.predicates _ (predicate_mem M.hpid)
  rw [M.hb] at hpo
  have hcyF : ir.domainField M.cdy < ir.fields.length :=
    domainField_lt hwf (hpo.1 (M.cdy, M.cy) (by simp [PredBody.exprs])).1
  have hcy : M.dy = M.cdy → 1 < ir.charOf (ir.domainField M.cdy) := fun h1 => by
    have := M.char
    rw [h1] at this
    omega
  have hxp : ∀ j, ir.evalPad rd M.dx M.x j = 0 ∨ ir.evalPad rd M.dx M.x j = 1 := fun j => by
    by_cases hj : j < ir.exprLen M.x
    · rw [evalPad_of_lt hj]
      exact hS.xbits j hj
    · rw [evalPad_of_le (Nat.le_of_not_lt hj)]
      exact .inl rfl
  -- the `x` operand's chunks are the check's, `y` padded by zeros being read as `x`
  have hcongr : M.dy = M.cdy →
      ir.PadsTo rd M.cdy M.y M.cy (M.real.chunks * M.real.width) →
      ir.exprLen M.cy = ir.exprLen M.x → 1 < ir.charOf (ir.domainField M.dx) →
      ∀ c, ir.macChunkA rd M.real.macField M.dx M.x M.real.width c =
        ir.macChunkA rd M.real.macField M.dy M.y M.real.width c := by
    intro h1 hP hlc hcx c
    rw [h1, macChunkA_of_padsTo hP]
    have hcyb : ∀ i < ir.exprLen M.x,
        ir.evalWith rd M.cdy M.cy i = 0 ∨ ir.evalWith rd M.cdy M.cy i = 1 := by
      intro i hi
      have hiN : i < ir.exprLen M.y := by rw [hP.1]; exact lt_of_lt_of_le hi M.lenX
      have h3 := hP.2.2.1 i
      rw [evalPad_of_lt hiN, evalPad_of_lt (hlc ▸ hi)] at h3
      rw [← h3]
      have := hS.ybits i hiN
      rwa [h1] at this
    exact macChunkA_congr fun i => by
      by_cases hj : c * M.real.width + i < ir.exprLen M.x
      · rw [evalPad_of_lt hj, evalPad_of_lt (hlc ▸ hj)]
        exact hS.x_iff M hwf hL hcx (hcy h1) hcyb hj
      · rw [evalPad_of_le (Nat.le_of_not_lt hj),
          evalPad_of_le (by rw [hlc]; exact Nat.le_of_not_lt hj)]
        simp
  rcases M.hside with ⟨hok, h1, h2, -⟩ | ⟨b, hbx, -, -, -, -, h1, h2⟩ |
    ⟨bx, hbx, -, h, hcx', -, h1, h2⟩
  · have hH := hT.hosted hok.noBlindX
    unfold MacHHoldsAt at hH
    rw [hH]
    have hcx : 1 < ir.charOf (ir.domainField M.dx) := by
      rw [hok.hField, M.macChar]
      norm_num
    have hP := padsTo_of_zeroPadB hwf.refsOrdered hI hL hK hcyF (by have := hcy h1; omega) h2
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [macChunkH_eq_macChunkA hok.hField fun i => hxp _, hcongr h1 hP hok.lenY hcx c]
  · unfold MacTagAt at hT
    rw [hbx] at hT
    unfold MacTwoTagAt at hT
    rw [hT, h1, h2]
  · unfold MacTagAt at hT
    rw [hbx] at hT
    unfold MacTwoTagAt at hT
    rw [hT]
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    have hP : ir.PadsTo rd M.cdy M.y M.cy (M.real.chunks * M.real.width) := by
      rw [h2]
      exact padsTo_of_zeroPadB hwf.refsOrdered hI hL hK hcyF (by have := hcy h1; omega)
        (zeroPadB_self h.lenY)
    exact hcongr h1 hP (h.lenY.trans h.lenX.symm) hcx' c

end MacBaseC

namespace MacBaseC

variable {G : Gens} (M : ir.MacBaseC primeNodes G) {Inp : Type} (hgen : ir.CGenFacts I G)
  (stmtOf val : Inp → ir.Valuation I) (SL : ir.SrcLate I Inp) (y : Inp) (c : ∀ k, (ir.layout I).Ch k)
  (π : (ir.layout I).Pads)

/-- **The A operand's integer readings are bits** at a reader with the source facts. -/
theorem Source.yint01 {rd : ir.Valuation I} (hS : M.Source rd) {j : ℕ}
    (hj : j < ir.exprLen M.y) :
    ir.evalIntWith rd M.dy M.y j = 0 ∨ ir.evalIntWith rd M.dy M.y j = 1 := by
  rw [hS.yint j hj]
  split_ifs <;> simp

/-- **The A operand reads the casts of its integer readings** at a reader with the source facts. -/
theorem Source.ycast {rd : ir.Valuation I} (hS : M.Source rd) {j : ℕ}
    (hj : j < ir.exprLen M.y) :
    ir.evalWith rd M.dy M.y j = ((ir.evalIntWith rd M.dy M.y j : ℤ) : (I (ir.domainField M.dy)).K) := by
  rw [hS.yint j hj]
  rcases hS.ybits j hj with h | h <;> rw [h] <;> simp

variable (hwf : ir.WellFormed) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)

variable (hM : I.MacModel ir)

include hwf hI hL hM in
/-- **The tail holds at the honest values** (`tail_holds_of_honest`): the honest tag
(`macTagC_honest`) as the MAC of the chunks of the check's operand (`Source.sideTag`), the blind the
pad copy (`macBlinds_honestEnv`). -/
theorem tail_honest (hB : ir.BlindsArePadCopies) (hS : M.Source (ir.reader (ir.honestEnv I
      (stmtOf y) (val y) (ir.genLateOf I hgen stmtOf val SL y) c π))) :
    ir.HoldsWith (ir.reader (ir.honestEnv I (stmtOf y) (val y)
      (ir.genLateOf I hgen stmtOf val SL y) c π)) (ir.predicate M.t).body := by
  have hbl0 := M.blindAt
  exact tail_holds_of_honest hwf hI hL hM _ M.char M.pos M.field M.tag hbl0 M.lenY M.ht M.htB
    (hS.sideTag M hwf hI hL (fun _ _ hk i => reader_of_constant _ hk i)
      (macTagC_honest hgen stmtOf val SL y c π M.hb M.tag M.tagGen M.tagNotSource M.tagLate M.xNoLate))
    M.blindCopy
    (macBlinds_honestEnv hB (stmtOf y) (val y) _ c π _ (predicate_mem M.hpid) _ _ _ _ _ _ M.hb M.sb
      M.blind_mem)
    M.dyLt hS.yint

/-- **The tail's right side is the target's bits** (`macTailAtB`). -/
theorem rhs : ∃ tb, M.R = .leaf tb ∧ ir.targetBitsB tb M.dy M.real.tag = true := by
  have htB := M.htB
  unfold macTailAtB at htB
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at htB
  obtain ⟨-, htB⟩ := htB
  rw [M.hbt] at htB
  split at htB
  · rename_i d b r w nch taps y' tb real' hbt
    simp only [Bool.and_eq_true, beq_iff_eq] at htB
    simp only [PredBody.mod.injEq] at hbt
    exact ⟨tb, hbt.2.2.2.1, htB.1.2⟩
  · cases htB

/-- **The A domain is a domain of the program.** -/
theorem dy_lt (hwf : ir.WellFormed) : M.dy < ir.domains.length := M.dyLt

include hwf hL in
/-- **The honest blind is a bit**: at an output coordinate `i < w`, its integer reading is a bit
`bI` and its value the cast of `bI` (`macBlinds_honestEnv`). -/
theorem blind_honest (hB : ir.BlindsArePadCopies) {i : ℕ} (hi : i < M.u.width) :
    ∃ bI : ℕ, bI ≤ 1 ∧ ir.intOf (ir.reader (ir.honestEnv I (stmtOf y) (val y) (ir.genLateOf I hgen stmtOf val SL y) c π)) M.u.blind i = bI ∧
      (castElt (ir.reader (ir.honestEnv I (stmtOf y) (val y) (ir.genLateOf I hgen stmtOf val SL y) c π) M.u.blind i) : (I (ir.domainField M.dy)).K) = ((bI : ℤ) : _) := by
  have hdy := M.dy_lt hwf
  have hdF := domainField_lt hwf hdy
  have h2 := M.char
  have hbl0 := M.blindAt
  unfold macBlindCoreB at hbl0
  rw [← M.units.1] at hbl0
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hbl0
  obtain ⟨⟨-, hbf⟩, -⟩ := hbl0
  have hbv := macBlinds_honestEnv hB (stmtOf y) (val y) (ir.genLateOf I hgen stmtOf val SL y) c π _
    (predicate_mem M.hpid) _ _ _ _ _ _ M.hb M.u.blind
    M.ublind_mem i (M.units.2.2.1 ▸ hi)
  set bit := ((I (ir.valueField M.real.tag)).toNat ((ir.honestEnv I (stmtOf y) (val y)
    (ir.genLateOf I hgen stmtOf val SL y) c π).asg.pad M.real.tag 0)).testBit i
  have hone : (I (ir.valueField M.u.blind)).toNat 1 = 1 := by
    simpa using hL.toNat_natCast _ (hbf ▸ hdF) 1 (by rw [hbf]; simp only [charOf] at h2; omega)
  have hzero : (I (ir.valueField M.u.blind)).toNat 0 = 0 := by
    simpa using hL.toNat_natCast _ (hbf ▸ hdF) 0 (by rw [hbf]; simp only [charOf] at h2; omega)
  refine ⟨if bit then 1 else 0, by split_ifs <;> omega, ?_, ?_⟩
  · rw [intOf_of_ne_constant _ (fun es h => by rw [M.blindKind] at h; cases h) _
      (fun x h => by rw [M.blindKind] at h; cases h), hbv]
    split_ifs <;> simp_all
  · rw [hbv]
    split_ifs
    · rw [castElt_one_of_eq hbf]; simp
    · rw [castElt_zero]; simp

/-- **The tail's left side has the chunk width's length.** -/
theorem lLen : ir.exprLen M.L = M.u.width := by
  have hbl0 := M.blindAt
  unfold macBlindCoreB at hbl0
  rw [← M.units.1] at hbl0
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hbl0
  obtain ⟨-, hbsz⟩ := hbl0
  rw [eq_of_macUnits? M.hu]
  change (ir.value M.u.blind).size = _
  rw [hbsz, ← M.units.2.2.1]


include hwf hL hM in
/-- **The tail's right side reads a bit** `bt`, on the integers and in the field (`rhs`,
`reader_targetBits_int`). -/
theorem target_honest (e : ir.Env I) (i : ℕ) :
    ∃ bt : ℕ, bt < 2 ∧ ir.evalIntWith (ir.reader e) M.dy M.R i = bt ∧
      ir.evalWith (ir.reader e) M.dy M.R i = (bt : (I (ir.domainField M.dy)).K) := by
  obtain ⟨tb, hR, htb⟩ := M.rhs
  obtain ⟨-, htf⟩ := hM.mod M.t M.ht _ _ _ _ _ _ _ _ _ (by
    have := M.hbt
    rw [eq_of_macUnits? M.hu, hR] at this
    exact this)
  obtain ⟨bt, hbt, hint, hcast, -⟩ :=
    reader_targetBits_int hwf hL e htb (M.dy_lt hwf) (by have := M.char; omega) htf i
  rw [hR]
  exact ⟨bt, hbt, hint, hcast⟩
end MacBaseC

variable (ir primeNodes) in
/-- **A MAC whose tail is a `mod_2` in the ungrouped digit form, at the certificate's generators** (compiler/mac.h with
compiler/mod.h `kDigits`; `DigitsMac` with the generators read off `G`): a MAC (`MacBaseC`) whose
tail has the digits `[low, top]` (`low` a value, `top` derived from the accumulator `acc`, which
commits the left side by a row), and the facts the honest values need: the accumulator and the lower
digit generated as the tail's, late values of their domain's field and no source values; the left side reads no late value; the convolutions fit the characteristic;
the lookups on the digits and the no-wrap range `2 low + 2 B top` have room (`lowRoom`, `topRoom`,
`wrapRoom`). Data and properties of the program, decided per program. -/
structure DigitsMacC (G : Gens) extends ir.MacBaseC primeNodes G where
  /-- The accumulator. -/
  acc : ℕ
  /-- The lower digit. -/
  low : ℕ
  /-- The derived top digit. -/
  top : Expr
  hdig : realT.digits = [.leaf low, top]
  hT : realT.isDigitsTail = true
  hacc : ir.digitsAcc realT = acc
  accRow : ir.accRowB dy acc L = true
  derived : ir.topDerivedB dy 2 R realT acc = true
  /-- The accumulator is generated as the tail's. -/
  accGen : G.at acc = .digitsAcc t
  /-- The accumulator is no source value. -/
  accNotSource : ¬ ir.IsSourceValue acc
  accLt : acc < ir.values.length
  accLate : ir.IsLate acc
  accField : ir.valueField acc = ir.domainField dy
  /-- The lower digit is generated as the tail's lower digit `0`. -/
  lowGen : G.at low = .lowDigit t 0
  /-- The lower digit is no source value. -/
  lowNotSource : ¬ ir.IsSourceValue low
  lowLt : low < ir.values.length
  lowLate : ir.IsLate low
  lowField : ir.valueField low = ir.domainField dy
  lowSize : (ir.value low).size = u.width
  accSize : (ir.value acc).size = u.width
  topLen : ir.exprLen top = u.width
  lNoLate : ∀ v ∈ ir.exprNodes L, ir.NoLateRead v
  hw : 0 < u.width
  convFit : 2 * u.width < ir.charOf (ir.domainField dy)
  accMax : 1 + u.chunks * Conv.convMax u.width u.taps.toFinset < ir.charOf (ir.domainField dy)
  radixPos : 0 < realT.radix
  radixChar : 2 * realT.radix < ir.charOf (ir.domainField dy)
  lowRoom : ∀ p ∈ ir.predicates, ∀ d N r, p.body = .mem d [.leaf low] (.range N) (.lookup r) →
    d = dy ∧ realT.radix ≤ N
  topRoom : ∀ p ∈ ir.predicates, ∀ d D N r, p.body = .mem d [D] (.range N) (.lookup r) →
    D.beq top = true →
      d = dy ∧ (1 + u.chunks * Conv.convMax u.width u.taps.toFinset) / (2 * realT.radix) < N
  wrapRoom : ∀ p ∈ ir.predicates, ∀ d D N r, p.body = .mem d [D] (.range N) r →
    D.beq (.add (.scale (.const 2) (.leaf low)) (.scale (.const (2 * realT.radix)) top)) = true →
      d = dy ∧ 1 + u.chunks * Conv.convMax u.width u.taps.toFinset < N

namespace MacBaseC

variable {G : Gens} (M : ir.MacBaseC primeNodes G) {Inp : Type} (hgen : ir.CGenFacts I G)
  (stmtOf val : Inp → ir.Valuation I) (SL : ir.SrcLate I Inp) (y : Inp) (c : ∀ k, (ir.layout I).Ch k)
  (π : (ir.layout I).Pads) (hwf : ir.WellFormed) (hI : I.Registered ir)
  (hL : I.Lawful ir primeNodes)

set_option hygiene false in
local notation "HE" =>
  ir.reader (ir.honestEnv I (stmtOf y) (val y) (ir.genLateOf I hgen stmtOf val SL y) c π)

include hwf hI hL in
/-- **The tail's left side on the integers**: at an output coordinate `i < w`, the blind's integer
reading plus the chunks' integer convolutions (`evalIntWith_macUnits`). -/
theorem lhs_int (hw : 0 < M.u.width)
    (hfit : 2 * M.u.width < ir.charOf (ir.domainField M.dy)) {i : ℕ}
    (hi : i < M.u.width) :
    ir.evalIntWith HE M.dy M.L i = ir.intOf HE M.u.blind i +
      ∑ c' ∈ Finset.range M.u.chunks, ir.chunkTerm HE M.dy M.u.powers M.u.width M.u.taps
        M.u.operand i c' hw := by
  rw [eq_of_macUnits? M.hu]
  exact evalIntWith_macUnits hwf hI hL _ (M.dy_lt hwf) M.char M.u hw hfit hi

include hwf hI hL in
/-- **The tail's left side on the integers is a natural below `1 + nch · convMax`** at the honest
values, where the operand reads bits. -/
theorem lhs_bounds (hw : 0 < M.u.width)
    (hfit : 2 * M.u.width < ir.charOf (ir.domainField M.dy))
    (hB : ir.BlindsArePadCopies) (hS : M.Source HE) {i : ℕ} (hi : i < M.u.width) :
    0 ≤ ir.evalIntWith HE M.dy M.L i ∧
      ir.evalIntWith HE M.dy M.L i ≤ 1 + M.u.chunks * Conv.convMax M.u.width M.u.taps.toFinset := by
  obtain ⟨bI, hb1, hbint, -⟩ := M.blind_honest hgen stmtOf val SL y c π hwf hL hB hi
  rw [M.lhs_int hgen stmtOf val SL y c π hwf hI hL hw hfit hi, hbint]
  have hmem := fun c' (hc' : c' ∈ Finset.range M.u.chunks) =>
    chunkTerm_mem HE (d := M.dy) (r := M.u.powers) (taps := M.u.taps) (y := M.u.operand) hw i c'
      fun j => by
      have hlen : c' * M.u.width + j < ir.exprLen M.y := by
        rw [M.lenY, ← M.units.2.2.1, ← M.units.2.2.2.1]
        have := j.2
        have := Finset.mem_range.1 hc'
        nlinarith
      rw [M.units.2.1]
      exact hS.yint01 M hlen
  have h0 := Finset.sum_nonneg fun c' hc' => (hmem c' hc').1
  have hle : ∑ c' ∈ Finset.range M.u.chunks, ir.chunkTerm HE M.dy M.u.powers M.u.width M.u.taps
      M.u.operand i c' hw ≤ ∑ _c ∈ Finset.range M.u.chunks,
        (Conv.convMax M.u.width M.u.taps.toFinset : ℤ) :=
    Finset.sum_le_sum fun c' hc' => (hmem c' hc').2
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hle
  constructor
  · positivity
  · omega

include hwf hI hL in
/-- **The tail's left side reads the cast of its integer reading** at the honest values, where the
operand reads bits (the field convolution is the integer one, `NamedOp.apply_macConv`). -/
theorem lhs_field (hw : 0 < M.u.width)
    (hfit : 2 * M.u.width < ir.charOf (ir.domainField M.dy))
    (hB : ir.BlindsArePadCopies) (hS : M.Source HE) {i : ℕ} (hi : i < M.u.width) :
    ir.evalWith HE M.dy M.L i =
      ((ir.evalIntWith HE M.dy M.L i : ℤ) : (I (ir.domainField M.dy)).K) := by
  obtain ⟨bI, -, hbint, hbcast⟩ := M.blind_honest hgen stmtOf val SL y c π hwf hL hB hi
  rw [M.lhs_int hgen stmtOf val SL y c π hwf hI hL hw hfit hi, hbint, eq_of_macUnits? M.hu]
  simp only [evalWith, evalE_add, evalE_leaf, evalE_apply]
  rw [hbcast, NamedOp.apply_macConv ir _ hw, Nat.div_eq_of_lt hi, zero_mul]
  simp only [zero_add]
  push_cast
  congr 1
  rw [← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun c' _ => ?_
  simp only [chunkTerm]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  have hlen : (c' : ℕ) * M.u.width + j < ir.exprLen M.y := by
    rw [M.lenY, ← M.units.2.2.1, ← M.units.2.2.2.1]
    have := j.2
    have := c'.2
    nlinarith
  congr 1
  have h := hS.ycast M hlen
  rw [← M.units.2.1] at h
  exact h

end MacBaseC

namespace DigitsMacC

variable {G : Gens} (M : ir.DigitsMacC primeNodes G) {Inp : Type} (hgen : ir.CGenFacts I G)
  (stmtOf val : Inp → ir.Valuation I) (SL : ir.SrcLate I Inp) (y : Inp) (c : ∀ k, (ir.layout I).Ch k)
  (π : (ir.layout I).Pads) (hwf : ir.WellFormed) (hI : I.Registered ir)
  (hL : I.Lawful ir primeNodes) (hM : I.MacModel ir)

set_option hygiene false in
local notation "HE" =>
  ir.reader (ir.honestEnv I (stmtOf y) (val y) (ir.genLateOf I hgen stmtOf val SL y) c π)

/-- **The left side's honest integer reading as a natural**, at coordinate `i`. -/
noncomputable abbrev lhsNat (i : ℕ) : ℕ := (ir.evalIntWith HE M.dy M.L i).toNat

include hwf hI hL in
/-- **The honest left side's integer reading is its natural.** -/
theorem lhsNat_eq (hB : ir.BlindsArePadCopies) (hS : M.Source HE) {i : ℕ} (hi : i < M.u.width) :
    ((M.lhsNat hgen stmtOf val SL y c π i : ℕ) : ℤ) = ir.evalIntWith HE M.dy M.L i :=
  Int.toNat_of_nonneg (M.lhs_bounds hgen stmtOf val SL y c π hwf hI hL M.hw M.convFit hB hS hi).1

include hwf hI hL in
/-- **The honest left side's natural is at most `1 + nch · convMax`.** -/
theorem lhsNat_le (hB : ir.BlindsArePadCopies) (hS : M.Source HE) {i : ℕ} (hi : i < M.u.width) :
    M.lhsNat hgen stmtOf val SL y c π i ≤ 1 + M.u.chunks * Conv.convMax M.u.width M.u.taps.toFinset := by
  have h := M.lhs_bounds hgen stmtOf val SL y c π hwf hI hL M.hw M.convFit hB hS hi
  have h2 := M.lhsNat_eq hgen stmtOf val SL y c π hwf hI hL hB hS hi
  omega

/-- **The honest accumulator** is the cast of the left side's natural (`reader_digitsAccC_honest`). -/
theorem acc_honest {i : ℕ} (hi : i < M.u.width) :
    (castElt (HE M.acc i) : (I (ir.domainField M.dy)).K) =
      ((M.lhsNat hgen stmtOf val SL y c π i : ℕ) : (I (ir.domainField M.dy)).K) :=
  reader_digitsAccC_honest hgen stmtOf val SL y c π M.hbt M.accGen M.accNotSource M.accLt
    M.accLate M.accField M.lNoLate (by rw [M.accSize]; exact hi)

/-- **The honest lower digit** is the first base-`B` digit of half the left side's natural
(`reader_lowDigitC_honest`). -/
theorem low_honest {i : ℕ} (hi : i < M.u.width) :
    (castElt (HE M.low i) : (I (ir.domainField M.dy)).K) =
      ((M.lhsNat hgen stmtOf val SL y c π i / 2 % M.realT.radix : ℕ) :
        (I (ir.domainField M.dy)).K) := by
  rw [reader_lowDigitC_honest hgen stmtOf val SL y c π M.hbt M.lowGen M.lowNotSource M.lowLt
    M.lowLate M.lowField M.lNoLate
    (by rw [M.lowSize]; exact hi)]
  simp only [lowDigitNat, digitsAccNat, pow_zero, Nat.div_one]

include hwf hI hL hM in
/-- **The honest target's bit is the left side's parity** (the tail's congruence,
`reader_targetBits`): the right side reads the cast of the left side's natural modulo `2`. -/
theorem rhs_honest (hB : ir.BlindsArePadCopies) (hS : M.Source HE) {i : ℕ} (hi : i < M.u.width) :
    ir.evalWith HE M.dy M.R i =
      ((M.lhsNat hgen stmtOf val SL y c π i % 2 : ℕ) : (I (ir.domainField M.dy)).K) := by
  obtain ⟨bt, hbt2, heint, hecast⟩ := M.target_honest hwf hL hM
    (ir.honestEnv I (stmtOf y) (val y) (ir.genLateOf I hgen stmtOf val SL y) c π) i
  have htail := M.tail_honest hgen stmtOf val SL y c π hwf hI hL hM hB hS
  rw [M.hbt] at htail
  have hLlen : i < ir.exprLen M.L := M.lLen ▸ hi
  have hcong := htail i hLlen
  rw [heint, ← M.lhsNat_eq hgen stmtOf val SL y c π hwf hI hL hB hS hi] at hcong
  rw [hecast]
  congr 1
  omega

include hwf hI hL hM in
/-- **The honest top digit** is the cast of the quotient of half the left side's natural by `B`
(`fieldEq_of_topDerived`: `acc − R = 2 (low + B top)`, cancelling `2 B < p`). -/
theorem top_honest (hB : ir.BlindsArePadCopies) (hS : M.Source HE) {i : ℕ} (hi : i < M.u.width) :
    ir.evalWith HE M.dy M.top i =
      ((M.lhsNat hgen stmtOf val SL y c π i / 2 / M.realT.radix : ℕ) :
        (I (ir.domainField M.dy)).K) := by
  have hdy := M.dy_lt hwf
  obtain ⟨-, hcharF, -, -⟩ := modData hwf hI hL hdy M.char
  have hf := fieldEq_of_topDerived hwf hI hL HE hdy M.derived i
  rw [M.hdig] at hf
  simp only [List.map_cons, List.map_nil, digitsVal, List.foldr_cons, List.foldr_nil, mul_zero,
    add_zero] at hf
  have hacc : ir.evalWith HE M.dy (.leaf M.acc) i = _ := M.acc_honest hgen stmtOf val SL y c π hi
  have hlow : ir.evalWith HE M.dy (.leaf M.low) i = _ := M.low_honest hgen stmtOf val SL y c π hi
  rw [hacc, hlow, M.rhs_honest hgen stmtOf val SL y c π hwf hI hL hM hB hS hi] at hf
  set A := M.lhsNat hgen stmtOf val SL y c π i
  set B := M.realT.radix
  have hdecomp : A = A % 2 + 2 * (A / 2 % B + B * (A / 2 / B)) := by
    have h1 := Nat.mod_add_div A 2
    have h2 := Nat.mod_add_div (A / 2) B
    omega
  have hcast : ((A : ℕ) : (I (ir.domainField M.dy)).K) - ((A % 2 : ℕ) : _) =
      (2 : (I (ir.domainField M.dy)).K) * (((A / 2 % B : ℕ) : _) + (B : _) * ((A / 2 / B : ℕ) : _)) := by
    have e := congrArg (Nat.cast : ℕ → (I (ir.domainField M.dy)).K) hdecomp
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at e
    linear_combination e
  rw [hcast] at hf
  have hne : ((2 * B : ℕ) : (I (ir.domainField M.dy)).K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff _ (ir.charOf (ir.domainField M.dy))]
    intro hd
    have := Nat.le_of_dvd (by have := M.radixPos; omega) hd
    have := M.radixChar
    omega
  have h2 : ((2 : ℕ) : (I (ir.domainField M.dy)).K) * (B : _) *
      (ir.evalWith HE M.dy M.top i - ((A / 2 / B : ℕ) : _)) = 0 := by
    linear_combination hf.symm
  rw [← Nat.cast_mul] at h2
  rcases mul_eq_zero.1 h2 with h | h
  · exact absurd h hne
  · exact sub_eq_zero.1 h

end DigitsMacC

namespace DigitsMacC

variable {G : Gens} (M : ir.DigitsMacC primeNodes G)

/-- **The no-wrap range's expression** `2 low + 2 B top`. -/
def wrapExpr : Expr :=
  .add (.scale (.const 2) (.leaf M.low)) (.scale (.const (2 * M.realT.radix)) M.top)


/-- **The predicates the MAC's honest values satisfy**: its tail, the accumulator row, a lookup on
its lower digit or on its top digit, the no-wrap range, its H predicate. -/
def Role (b : PredBody) : Prop :=
  b = (ir.predicate M.t).body ∨
    (∃ Lr z tg, b = .equal M.dy Lr (.leaf z) tg ∧
      ir.constAll z 0 (ir.exprLen M.L) (ir.domainField M.dy) = true ∧
      accTerms (ir.charOf (ir.domainField M.dy)) M.acc Lr M.L = true) ∨
    (∃ d N r, b = .mem d [.leaf M.low] (.range N) (.lookup r)) ∨
    (∃ d D N r, b = .mem d [D] (.range N) (.lookup r) ∧ D.beq M.top = true) ∨
    (∃ d D N r, b = .mem d [D] (.range N) r ∧ D.beq M.wrapExpr = true) ∨
    ∃ hp, M.real.hPredicate = some hp ∧ b = (ir.predicate hp).body

variable {Inp : Type} (hgen : ir.CGenFacts I G) (stmtOf val : Inp → ir.Valuation I) (SL : ir.SrcLate I Inp) (y : Inp)
  (c : ∀ k, (ir.layout I).Ch k) (π : (ir.layout I).Pads)
  (hwf : ir.WellFormed) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes) (hM : I.MacModel ir)

set_option hygiene false in
local notation "HE" =>
  ir.reader (ir.honestEnv I (stmtOf y) (val y) (ir.genLateOf I hgen stmtOf val SL y) c π)

include hwf hI hL hM in
/-- **The MAC's predicates hold at the honest values** (`Role`), where the source facts hold. -/
theorem role_holds (hB : ir.BlindsArePadCopies)
    (hpow2 : ∀ j < M.real.width, (I M.real.macField).decode (2 ^ j) = (I M.real.macField).decode 2 ^ j)
    (htag1 : (ir.value M.real.tag).size = 1) (hS : M.Source HE)
    {p : Predicate} (hp : p ∈ ir.predicates) (hr : M.Role p.body) :
    ir.HoldsWith HE p.body := by
  have hdy := M.dy_lt hwf
  have hdF := domainField_lt hwf hdy
  obtain ⟨-, hcharF, -, hdec⟩ := modData hwf hI hL hdy M.char
  have hp2 : 2 < ir.charOf (ir.domainField M.dy) := M.char
  have hBmax := fun {i : ℕ} (hi : i < M.u.width) =>
    M.lhsNat_le hgen stmtOf val SL y c π hwf hI hL hB hS hi
  rcases hr with h | ⟨Lr, z, tg, h, hz, hacc⟩ | ⟨d, N, r, h⟩ | ⟨d, D, N, r, h, hD⟩ |
    ⟨d, D, N, r, h, hD⟩ | ⟨q, hq, h⟩
  · rw [h]
    exact M.tail_honest hgen stmtOf val SL y c π hwf hI hL hM hB hS
  · rw [h]
    have hneg : ∀ c, c + 1 = ir.charOf (ir.domainField M.dy) →
        (I (ir.domainField M.dy)).decode c = -1 := by
      intro c hc
      rw [hL.decode_natCast _ hdF c (by simp only [charOf] at hc ⊢; omega), eq_neg_iff_add_eq_zero,
        ← Nat.cast_one, ← Nat.cast_add, hc, CharP.cast_eq_zero]
    have hlen := exprLen_of_accTerms (ir := ir) _ M.L Lr (Nat.lt_succ_self _) hacc
    intro i hi
    rw [hlen, M.accSize] at hi
    simp only [evalWith]
    rw [evalE_of_accTerms _ hneg _ M.L Lr (Nat.lt_succ_self _) hacc i,
      evalE_leaf_constAll_reader hL _ hz hdF (by omega) (by rw [M.lLen]; exact hi),
      M.acc_honest hgen stmtOf val SL y c π hi]
    have hf := M.lhs_field hgen stmtOf val SL y c π hwf hI hL M.hw M.convFit hB hS hi
    simp only [evalWith] at hf
    rw [hf, ← M.lhsNat_eq hgen stmtOf val SL y c π hwf hI hL hB hS hi, Int.cast_natCast, sub_self, Nat.cast_zero]
  · obtain ⟨rfl, hN⟩ := M.lowRoom p hp d N r h
    rw [h]
    intro i hi e he
    simp only [List.mem_singleton] at he
    subst he
    have hi' : i < M.u.width := by
      rw [← M.lowSize]
      simpa [exprLen, Expr.len] using hi
    refine ⟨M.lhsNat hgen stmtOf val SL y c π i / 2 % M.realT.radix,
      (Nat.mod_lt _ M.radixPos).trans_le hN, ?_⟩
    simp only [evalWith, evalE_leaf]
    exact M.low_honest hgen stmtOf val SL y c π hi'
  · obtain ⟨rfl, hN⟩ := M.topRoom p hp d D N r h hD
    rw [h, Expr.eq_of_beq hD]
    intro i hi e he
    simp only [List.mem_singleton] at he
    subst he
    have hi' : i < M.u.width := by
      rw [← M.topLen]
      simpa using hi
    refine ⟨M.lhsNat hgen stmtOf val SL y c π i / 2 / M.realT.radix, ?_,
      M.top_honest hgen stmtOf val SL y c π hwf hI hL hM hB hS hi'⟩
    refine lt_of_le_of_lt ?_ hN
    rw [Nat.div_div_eq_div_mul]
    exact Nat.div_le_div_right (hBmax hi')
  · obtain ⟨rfl, hN⟩ := M.wrapRoom p hp d D N r h hD
    rw [h, Expr.eq_of_beq hD]
    intro i hi e he
    simp only [List.mem_singleton] at he
    subst he
    have hi' : i < M.u.width := by
      rw [← M.lowSize]
      simpa [wrapExpr, exprLen, Expr.len] using hi
    set A := M.lhsNat hgen stmtOf val SL y c π i
    refine ⟨A - A % 2, lt_of_le_of_lt (Nat.sub_le _ _) (lt_of_le_of_lt (hBmax hi') hN), ?_⟩
    have hlow := M.low_honest hgen stmtOf val SL y c π hi'
    have htop := M.top_honest hgen stmtOf val SL y c π hwf hI hL hM hB hS hi'
    simp only [evalWith] at htop
    simp only [wrapExpr, evalWith, evalE_add, evalE_scale_const, evalE_leaf]
    rw [hlow, htop, hdec 2 hp2, hdec _ M.radixChar]
    have hdecomp : A - A % 2 = 2 * (A / 2 % M.realT.radix) +
        2 * M.realT.radix * (A / 2 / M.realT.radix) := by
      have h1 := Nat.mod_add_div A 2
      have h2 := Nat.mod_add_div (A / 2) M.realT.radix
      have h3 : M.realT.radix * (A / 2 / M.realT.radix) * 2 =
          2 * M.realT.radix * (A / 2 / M.realT.radix) := by ring
      omega
    rw [hdecomp]
    push_cast
    ring
  · have hok := M.hok_of_hPred hq
    have hhalf := hok.half
    unfold macHalfB at hhalf
    rw [hq] at hhalf
    rw [h]
    exact hPred_holds_of_macHHolds hwf.refsOrdered hI hL _ hhalf hok.hField hok.field hok.tag hpow2 htag1
      ((macTagC_honest hgen stmtOf val SL y c π M.hb hok.tag M.tagGen M.tagNotSource M.tagLate
        M.xNoLate).hosted hok.noBlindX)

end DigitsMacC

namespace DigitsMacC

variable {G : Gens} (M : ir.DigitsMacC primeNodes G) {Inp : Type} (hgen : ir.CGenFacts I G)
  (stmtOf val : Inp → ir.Valuation I) (SL : ir.SrcLate I Inp) (y : Inp)
  (c : ∀ k, (ir.layout I).Ch k) (π : (ir.layout I).Pads)

/-- **The MAC's honest tag** (`MacTagAt`; `macTagC_honest`) at the honest environment of the
certificate. -/
theorem macTag_honest :
    ir.MacTagAt (ir.reader (ir.honestEnv I (stmtOf y) (val y) (ir.genLateOf I hgen stmtOf val SL y)
      c π)) M.dx M.x M.real (castElt ((ir.honestEnv I (stmtOf y) (val y)
        (ir.genLateOf I hgen stmtOf val SL y) c π).chal M.real.key 0)) :=
  macTagC_honest hgen stmtOf val SL y c π M.hb M.tag M.tagGen M.tagNotSource M.tagLate M.xNoLate

end DigitsMacC

variable (ir primeNodes) in
/-- **A MAC whose tail is a `mod_2` in the one-digit form, at the certificate's generators**
(compiler/mac.h on a single group with compiler/mod.h `kOneDigit`): a MAC (`MacBaseC`) whose tail's quotient is derived from an accumulator
`acc` (`Q = (acc − bits(T)) / 2`, the accumulator committing the left side by a row), and the facts
the honest values need: the accumulator generated as the tail's (`digitsAcc`, whose formula
`digitsAccNat` is the left side's integer reading), a late value of its domain's field and no source
value; the left side reads no late value; the convolutions fit the characteristic; the lookups on
the quotient have room (`quotRoom`). Data and properties of the program, decided per program. -/
structure OneDigitMacC (G : Gens) extends ir.MacBaseC primeNodes G where
  /-- The accumulator. -/
  acc : ℕ
  hT : realT.isOneDigitTail = true
  hacc : ir.oneDigitAcc realT = acc
  derived : ir.quotDerivedAccB dy 2 L R realT = true
  /-- The accumulator is generated as the tail's. -/
  accGen : G.at acc = .digitsAcc t
  /-- The accumulator is no source value. -/
  accNotSource : ¬ ir.IsSourceValue acc
  accLt : acc < ir.values.length
  accLate : ir.IsLate acc
  accField : ir.valueField acc = ir.domainField dy
  accSize : (ir.value acc).size = u.width
  quotLen : ir.exprLen realT.quotExpr = u.width
  lNoLate : ∀ v ∈ ir.exprNodes L, ir.NoLateRead v
  hw : 0 < u.width
  convFit : 2 * u.width < ir.charOf (ir.domainField dy)
  accMax : 1 + u.chunks * Conv.convMax u.width u.taps.toFinset < ir.charOf (ir.domainField dy)
  quotRoom : ∀ p ∈ ir.predicates, ∀ d D N r, p.body = .mem d [D] (.range N) (.lookup r) →
    D.beq realT.quotExpr = true →
      d = dy ∧ (1 + u.chunks * Conv.convMax u.width u.taps.toFinset) / 2 < N

namespace OneDigitMacC

variable {G : Gens} (M : ir.OneDigitMacC primeNodes G) {Inp : Type} (hgen : ir.CGenFacts I G)
  (stmtOf val : Inp → ir.Valuation I) (SL : ir.SrcLate I Inp) (y : Inp) (c : ∀ k, (ir.layout I).Ch k)
  (π : (ir.layout I).Pads) (hwf : ir.WellFormed) (hI : I.Registered ir)
  (hL : I.Lawful ir primeNodes) (hM : I.MacModel ir)

set_option hygiene false in
local notation "HE" =>
  ir.reader (ir.honestEnv I (stmtOf y) (val y) (ir.genLateOf I hgen stmtOf val SL y) c π)

/-- **The left side's honest integer reading as a natural**, at coordinate `i`. -/
noncomputable abbrev lhsNat (i : ℕ) : ℕ := (ir.evalIntWith HE M.dy M.L i).toNat

include hwf hI hL in
/-- **The honest left side's integer reading is its natural.** -/
theorem lhsNat_eq (hB : ir.BlindsArePadCopies) (hS : M.Source HE) {i : ℕ} (hi : i < M.u.width) :
    ((M.lhsNat hgen stmtOf val SL y c π i : ℕ) : ℤ) = ir.evalIntWith HE M.dy M.L i :=
  Int.toNat_of_nonneg (M.lhs_bounds hgen stmtOf val SL y c π hwf hI hL M.hw M.convFit hB hS hi).1

include hwf hI hL in
/-- **The honest left side's natural is at most `1 + nch · convMax`.** -/
theorem lhsNat_le (hB : ir.BlindsArePadCopies) (hS : M.Source HE) {i : ℕ} (hi : i < M.u.width) :
    M.lhsNat hgen stmtOf val SL y c π i ≤ 1 + M.u.chunks * Conv.convMax M.u.width M.u.taps.toFinset := by
  have h := M.lhs_bounds hgen stmtOf val SL y c π hwf hI hL M.hw M.convFit hB hS hi
  have h2 := M.lhsNat_eq hgen stmtOf val SL y c π hwf hI hL hB hS hi
  omega

/-- **The honest accumulator** is the cast of the left side's natural (`reader_digitsAccC_honest`). -/
theorem acc_honest {i : ℕ} (hi : i < M.u.width) :
    (castElt (HE M.acc i) : (I (ir.domainField M.dy)).K) =
      ((M.lhsNat hgen stmtOf val SL y c π i : ℕ) : (I (ir.domainField M.dy)).K) :=
  reader_digitsAccC_honest hgen stmtOf val SL y c π M.hbt M.accGen M.accNotSource M.accLt
    M.accLate M.accField M.lNoLate (by rw [M.accSize]; exact hi)

include hwf hI hL hM in
/-- **The honest target's bit is the left side's parity** (the tail's congruence,
`reader_targetBits`): the right side reads the cast of the left side's natural modulo `2`. -/
theorem rhs_honest (hB : ir.BlindsArePadCopies) (hS : M.Source HE) {i : ℕ} (hi : i < M.u.width) :
    ir.evalWith HE M.dy M.R i =
      ((M.lhsNat hgen stmtOf val SL y c π i % 2 : ℕ) : (I (ir.domainField M.dy)).K) := by
  obtain ⟨bt, hbt2, heint, hecast⟩ := M.target_honest hwf hL hM
    (ir.honestEnv I (stmtOf y) (val y) (ir.genLateOf I hgen stmtOf val SL y) c π) i
  have htail := M.tail_honest hgen stmtOf val SL y c π hwf hI hL hM hB hS
  rw [M.hbt] at htail
  have hLlen : i < ir.exprLen M.L := M.lLen ▸ hi
  have hcong := htail i hLlen
  rw [heint, ← M.lhsNat_eq hgen stmtOf val SL y c π hwf hI hL hB hS hi] at hcong
  rw [hecast]
  congr 1
  omega

include hwf hI hL hM in
/-- **The honest quotient** is the cast of half the left side's natural (`quotDerivedAccB`:
`Q = a · acc + b · R` with `2 a ≡ 1`, `2 b ≡ −1`, the honest accumulator the left side's natural
and `R` its parity). -/
theorem quot_honest (hB : ir.BlindsArePadCopies) (hS : M.Source HE) {i : ℕ} (hi : i < M.u.width) :
    ir.evalWith HE M.dy M.realT.quotExpr i =
      ((M.lhsNat hgen stmtOf val SL y c π i / 2 : ℕ) : (I (ir.domainField M.dy)).K) := by
  have hdy := M.dy_lt hwf
  have hf := domainField_lt hwf hdy
  have hchar := charP_field hI hf
  have hR := M.rhs_honest hgen stmtOf val SL y c π hwf hI hL hM hB hS hi
  have hA := M.acc_honest hgen stmtOf val SL y c π hi
  have hd := M.derived
  have hacc := M.hacc
  unfold quotDerivedAccB at hd
  unfold oneDigitAcc at hacc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hd
  obtain ⟨-, hd⟩ := hd
  simp only [evalWith]
  rw [← evalE_deref hwf.refsOrdered _ _ M.realT.quotExpr]
  split at hd
  · rename_i a acc' b e₂ hx
    rw [hx] at hacc
    simp only at hacc
    subst hacc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hd
    obtain ⟨⟨⟨⟨⟨-, h2'⟩, ha⟩, hb⟩, hqa⟩, hqb⟩ := hd
    simp only [evalWith] at hR
    rw [hx, evalE_add, evalE_scale_const, evalE_scale_const, evalE_leaf, hA, Expr.eq_of_beq h2',
      hR, hL.decode_natCast _ hf a ha, hL.decode_natCast _ hf b hb]
    have hqa' : (2 : (I (ir.domainField M.dy)).K) * a = 1 := by
      rw [show (2 : (I (ir.domainField M.dy)).K) = ((2 : ℕ) : _) by norm_num, ← Nat.cast_mul,
        CharP.cast_eq_mod (I (ir.domainField M.dy)).K (ir.charOf (ir.domainField M.dy)), hqa,
        Nat.cast_one]
    have hqb' : (2 : (I (ir.domainField M.dy)).K) * b + 1 = 0 := by
      rw [show (2 : (I (ir.domainField M.dy)).K) = ((2 : ℕ) : _) by norm_num, ← Nat.cast_mul,
        ← Nat.cast_one, ← Nat.cast_add,
        CharP.cast_eq_mod (I (ir.domainField M.dy)).K (ir.charOf (ir.domainField M.dy)), hqb,
        Nat.cast_zero]
    set A := M.lhsNat hgen stmtOf val SL y c π i
    have he : ((A : ℕ) : (I (ir.domainField M.dy)).K) =
        ((A % 2 : ℕ) : _) + 2 * ((A / 2 : ℕ) : _) := by
      have h := congrArg (Nat.cast : ℕ → (I (ir.domainField M.dy)).K) (Nat.mod_add_div A 2).symm
      push_cast at h
      exact h
    have h2ne : (2 : (I (ir.domainField M.dy)).K) ≠ 0 := by
      rw [show (2 : (I (ir.domainField M.dy)).K) = ((2 : ℕ) : _) by norm_num, Ne,
        CharP.cast_eq_zero_iff _ (ir.charOf (ir.domainField M.dy))]
      intro hd2
      have := Nat.le_of_dvd (by norm_num) hd2
      have := M.char
      omega
    have h2 : (2 : (I (ir.domainField M.dy)).K) * ((a : _) * ((A : ℕ) : _) +
        (b : _) * ((A % 2 : ℕ) : _) - ((A / 2 : ℕ) : _)) = 0 := by
      linear_combination (2 * (a : (I (ir.domainField M.dy)).K)) * he +
        (2 * ((A / 2 : ℕ) : (I (ir.domainField M.dy)).K) + ((A % 2 : ℕ) : _)) * hqa' +
        ((A % 2 : ℕ) : (I (ir.domainField M.dy)).K) * hqb'
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h h2ne
    · exact sub_eq_zero.1 h
  · cases hd

end OneDigitMacC

namespace OneDigitMacC

variable {G : Gens} (M : ir.OneDigitMacC primeNodes G)

/-- **The predicates the MAC's honest values satisfy**: its tail, the accumulator row, a lookup on
its quotient, its H predicate. -/
def Role (b : PredBody) : Prop :=
  b = (ir.predicate M.t).body ∨
    (∃ Lr z tg, b = .equal M.dy Lr (.leaf z) tg ∧
      ir.constAll z 0 (ir.exprLen M.L) (ir.domainField M.dy) = true ∧
      accTerms (ir.charOf (ir.domainField M.dy)) M.acc Lr M.L = true) ∨
    (∃ d D N r, b = .mem d [D] (.range N) (.lookup r) ∧ D.beq M.realT.quotExpr = true) ∨
    ∃ hp, M.real.hPredicate = some hp ∧ b = (ir.predicate hp).body

variable {Inp : Type} (hgen : ir.CGenFacts I G) (stmtOf val : Inp → ir.Valuation I)
  (SL : ir.SrcLate I Inp) (y : Inp) (c : ∀ k, (ir.layout I).Ch k) (π : (ir.layout I).Pads)
  (hwf : ir.WellFormed) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes) (hM : I.MacModel ir)

set_option hygiene false in
local notation "HE" =>
  ir.reader (ir.honestEnv I (stmtOf y) (val y) (ir.genLateOf I hgen stmtOf val SL y) c π)

include hwf hI hL hM in
/-- **The MAC's predicates hold at the honest values** (`Role`), where the source facts hold. -/
theorem role_holds (hB : ir.BlindsArePadCopies)
    (hpow2 : ∀ j < M.real.width, (I M.real.macField).decode (2 ^ j) = (I M.real.macField).decode 2 ^ j)
    (htag1 : (ir.value M.real.tag).size = 1) (hS : M.Source HE)
    {p : Predicate} (hp : p ∈ ir.predicates) (hr : M.Role p.body) :
    ir.HoldsWith HE p.body := by
  have hdy := M.dy_lt hwf
  have hdF := domainField_lt hwf hdy
  obtain ⟨-, hcharF, -, -⟩ := modData hwf hI hL hdy M.char
  rcases hr with h | ⟨Lr, z, tg, h, hz, hacc⟩ | ⟨d, D, N, r, h, hD⟩ | ⟨q, hq, h⟩
  · rw [h]
    exact M.tail_honest hgen stmtOf val SL y c π hwf hI hL hM hB hS
  · rw [h]
    have hneg : ∀ c, c + 1 = ir.charOf (ir.domainField M.dy) →
        (I (ir.domainField M.dy)).decode c = -1 := by
      intro c hc
      rw [hL.decode_natCast _ hdF c (by simp only [charOf] at hc ⊢; omega), eq_neg_iff_add_eq_zero,
        ← Nat.cast_one, ← Nat.cast_add, hc, CharP.cast_eq_zero]
    have hlen := exprLen_of_accTerms (ir := ir) _ M.L Lr (Nat.lt_succ_self _) hacc
    intro i hi
    rw [hlen, M.accSize] at hi
    simp only [evalWith]
    rw [evalE_of_accTerms _ hneg _ M.L Lr (Nat.lt_succ_self _) hacc i,
      evalE_leaf_constAll_reader hL _ hz hdF (by have := M.char; omega)
        (by rw [M.lLen]; exact hi),
      M.acc_honest hgen stmtOf val SL y c π hi]
    have hf := M.lhs_field hgen stmtOf val SL y c π hwf hI hL M.hw M.convFit hB hS hi
    simp only [evalWith] at hf
    rw [hf, ← M.lhsNat_eq hgen stmtOf val SL y c π hwf hI hL hB hS hi, Int.cast_natCast, sub_self,
      Nat.cast_zero]
  · obtain ⟨rfl, hN⟩ := M.quotRoom p hp d D N r h hD
    rw [h, Expr.eq_of_beq hD]
    intro i hi e he
    simp only [List.mem_singleton] at he
    subst he
    have hi' : i < M.u.width := by
      rw [← M.quotLen]
      simpa using hi
    refine ⟨M.lhsNat hgen stmtOf val SL y c π i / 2,
      lt_of_le_of_lt (Nat.div_le_div_right (M.lhsNat_le hgen stmtOf val SL y c π hwf hI hL hB hS hi'))
        hN,
      M.quot_honest hgen stmtOf val SL y c π hwf hI hL hM hB hS hi'⟩
  · have hok := M.hok_of_hPred hq
    have hhalf := hok.half
    unfold macHalfB at hhalf
    rw [hq] at hhalf
    rw [h]
    exact hPred_holds_of_macHHolds hwf.refsOrdered hI hL _ hhalf hok.hField hok.field hok.tag hpow2 htag1
      ((macTagC_honest hgen stmtOf val SL y c π M.hb hok.tag M.tagGen M.tagNotSource M.tagLate
        M.xNoLate).hosted hok.noBlindX)

/-- **The MAC's honest tag** (`MacTagAt`; `macTagC_honest`) at the honest environment of the
certificate. -/
theorem macTag_honest :
    ir.MacTagAt HE M.dx M.x M.real (castElt ((ir.honestEnv I (stmtOf y) (val y)
        (ir.genLateOf I hgen stmtOf val SL y) c π).chal M.real.key 0)) :=
  macTagC_honest hgen stmtOf val SL y c π M.hb M.tag M.tagGen M.tagNotSource M.tagLate M.xNoLate

end OneDigitMacC

variable (ir primeNodes) in
/-- **A MAC whose tail is a grouped `mod_2`, at the certificate's generators** (compiler/mac.h with
compiler/mod.h `kGrouped`; `GroupedMac` with the generators read off `G`): a MAC (`MacBaseC`) whose
tail is in the grouped form (`GroupedFormOk`) with accumulators `acc` and quotient digits `gq`, and
the facts the honest values need: the accumulators and the digits generated as the tail's (`acc`,
`quotDigit`), late values of their domain's field and no source values; the digits fit (`fit`: a
group's sum, at most `count · convMax`, halved, is below `T^k`); the lookups on the digits and on
the final quotient have room (`digitsRoom`, `finalRoom`). Data and properties of the program,
decided per program. -/
structure GroupedMacC (G : Gens) extends ir.MacBaseC primeNodes G where
  hgf : ir.GroupedFormOk (ir.honestIvl primeNodes) dy 2 L R realT
  /-- The grouping. -/
  Gm : GroupedMod
  hG : realT.grouped = some Gm
  /-- The accumulators. -/
  acc : ℕ
  hA : Gm.accumulators = some (.leaf acc)
  /-- The quotient digits. -/
  gq : ℕ
  hD : Gm.groupDigits = .leaf gq
  /-- The accumulators are generated as the tail's. -/
  accGen : G.at acc = .acc t
  /-- The accumulators are no source value. -/
  accNotSource : ¬ ir.IsSourceValue acc
  accLt : acc < ir.values.length
  accLate : ir.IsLate acc
  accField : ir.valueField acc = ir.domainField dy
  /-- The quotient digits are generated as the tail's. -/
  gqGen : G.at gq = .quotDigit t
  /-- The quotient digits are no source value. -/
  gqNotSource : ¬ ir.IsSourceValue gq
  gqLt : gq < ir.values.length
  gqLate : ir.IsLate gq
  gqField : ir.valueField gq = ir.domainField dy
  fit : ∀ fc ∈ Gm.groups, fc.2 * Conv.convMax u.width u.taps.toFinset / 2 < Gm.base ^ Gm.digitCount
  digitsRoom : ∀ p ∈ ir.predicates, ∀ d N r, p.body = .mem d [.leaf gq] (.range N) (.lookup r) →
    d = dy ∧ 0 < Gm.base ∧ Gm.base ≤ N
  finalRoom : ∀ p ∈ ir.predicates, ∀ d D N r, p.body = .mem d [D] (.range N) (.lookup r) →
    D.beq realT.quotExpr = true → d = dy ∧ Gm.groups.length + 1 < 2 * N

namespace GroupedMacC

variable {G : Gens} (M : ir.GroupedMacC primeNodes G)

/-- **The parts of the tail's grouped shape** (`groupedShapeB`): well-formed
units, a row for every group, the residues and the derived final quotient. -/
theorem shape : ir.macUnitsOkB M.dy M.u M.Gm = true ∧
    (∀ g < M.Gm.groups.length, ∃ p ∈ ir.predicates,
      ir.groupRowB (ir.honestIvl primeNodes) M.dy M.u M.Gm M.acc g (M.Gm.groups.getD g default)
        p.body = true) ∧
    ir.residuesB M.dy 2 M.u M.Gm M.acc = true ∧ ir.finalQuotB M.dy 2 M.R M.u M.Gm M.realT = true := by
  have h := M.hgf.shape
  unfold groupedShapeB at h
  rw [M.hG, M.hu] at h
  dsimp only at h
  rw [M.hA] at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.mem_range] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- **The accumulators have one coordinate per group and output coordinate.** -/
theorem acc_size : (ir.value M.acc).size = M.Gm.groups.length * M.u.width := by
  have h := M.shape.2.2.1
  unfold residuesB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.2

/-- **The digits have `k` coordinates per accumulator.** -/
theorem gq_size : (ir.value M.gq).size = M.Gm.groups.length * M.u.width * M.Gm.digitCount := by
  have h := M.shape.2.2.1
  unfold residuesB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨-, h⟩ := h
  rw [M.hD] at h
  split at h
  · rename_i acc' c bb k T gq' gq hR hgd
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    cases hgd
    exact h.2
  · cases h

/-- **Group `g` is one of the groups.** -/
theorem group_mem {g : ℕ} (hg : g < M.Gm.groups.length) :
    M.Gm.groups.getD g default ∈ M.Gm.groups := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hg, Option.getD_some]
  exact List.getElem_mem _

/-- **A group's chunks are chunks of the units** (`macUnitsOkB`: the groups tile the chunks). -/
theorem group_fit {fc : ℕ × ℕ} (hfc : fc ∈ M.Gm.groups) : fc.1 - 1 + fc.2 ≤ M.u.chunks := by
  have hunits := M.shape.1
  unfold macUnitsOkB at hunits
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hunits
  exact (tiles_bound hunits.2 _ (List.mem_map_of_mem hfc)).2

/-- **The final quotient has the tail's output length** (`groupedBoundsB`: a direct `in` on it of
the left side's length). -/
theorem quot_len : ir.exprLen M.realT.quotExpr = M.u.width := by
  have hb := M.hgf.bounds
  unfold groupedBoundsB at hb
  rw [M.hG, M.hu] at hb
  dsimp only at hb
  split at hb
  · simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] at hb
    obtain ⟨-, rid, -, hQr⟩ := hb
    split at hQr
    · rename_i N hN
      unfold digitRangeOf at hN
      split_ifs at hN with hr
      split at hN
      · rename_i d' D' N' r' hbody
        split_ifs at hN with hc
        obtain ⟨-, -, hbq, hlen, -⟩ := hc
        rw [← Expr.eq_of_beq hbq, hlen, eq_of_macUnits? M.hu]
        change (ir.value M.u.blind).size = _
        have hbl := M.blindAt
        unfold macBlindCoreB at hbl
        rw [← M.units.1] at hbl
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hbl
        rw [hbl.2, M.units.2.2.1]
      · cases hN
    · cases hQr
  · cases hb

end GroupedMacC

namespace GroupedMacC

variable {G : Gens} (M : ir.GroupedMacC primeNodes G) {Inp : Type} (hgen : ir.CGenFacts I G)
  (stmtOf val : Inp → ir.Valuation I) (SL : ir.SrcLate I Inp) (y : Inp) (c : ∀ k, (ir.layout I).Ch k)
  (π : (ir.layout I).Pads)

set_option hygiene false in
local notation "HE" =>
  ir.reader (ir.honestEnv I (stmtOf y) (val y) (ir.genLateOf I hgen stmtOf val SL y) c π)

/-- **A group's honest accumulator is its integer sum, at most `count · convMax`** (`groupAcc_eq`):
the operand's integer readings are bits (`Source.yint01`). -/
theorem groupAcc_honest (hS : M.Source HE) (hw : 0 < M.u.width) {fc : ℕ × ℕ}
    (hfc : fc ∈ M.Gm.groups) (i : ℕ) :
    ((ir.groupAcc HE M.dy M.u fc i : ℕ) : ℤ) = ∑ c' ∈ Finset.range fc.2,
        ir.chunkTerm HE M.dy M.u.powers M.u.width M.u.taps M.u.operand i (fc.1 - 1 + c') hw ∧
      ir.groupAcc HE M.dy M.u fc i ≤ fc.2 * Conv.convMax M.u.width M.u.taps.toFinset :=
  groupAcc_eq _ hw fc i fun c' hc' j => by
    have hlen : (fc.1 - 1 + c') * M.u.width + j < ir.exprLen M.y := by
      rw [M.lenY, ← M.units.2.2.1, ← M.units.2.2.2.1]
      have := j.2
      have := M.group_fit hfc
      have h3 : fc.1 - 1 + c' + 1 ≤ M.u.chunks := by omega
      nlinarith
    rw [M.units.2.1]
    exact hS.yint01 M.toMacBaseC hlen

/-- **The honest accumulators are the groups' integer sums**: coordinate `g w + i` of the
accumulators is the cast of the sum of the integer convolutions of group `g`'s chunks
(`reader_accC_honest`). -/
theorem acc_honest (hS : M.Source HE) {g i : ℕ} (hg : g < M.Gm.groups.length) (hi : i < M.u.width)
    (hw : 0 < M.u.width) :
    (castElt (HE M.acc (g * M.u.width + i)) : (I (ir.domainField M.dy)).K) =
      ((∑ c' ∈ Finset.range (M.Gm.groups.getD g default).2,
        ir.chunkTerm HE M.dy M.u.powers M.u.width M.u.taps
          M.u.operand i ((M.Gm.groups.getD g default).1 - 1 + c') hw : ℤ) :
          (I (ir.domainField M.dy)).K) := by
  have hn : g * M.u.width + i < (ir.value M.acc).size := by
    rw [M.acc_size]
    nlinarith
  rw [reader_accC_honest hgen stmtOf val SL y c π M.hbt M.hG M.hu M.accGen M.accNotSource M.accLt
    M.accLate M.accField M.powNoLate M.yNoLate hn]
  have hdiv : (g * M.u.width + i) / M.u.width = g := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt hi, zero_add]
  have hmod : (g * M.u.width + i) % M.u.width = i := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
  simp only [accNat, hdiv, hmod]
  rw [← (M.groupAcc_honest hgen stmtOf val SL y c π hS hw (M.group_mem hg) i).1]
  push_cast
  rfl

variable (hwf : ir.WellFormed) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)

include hwf hI hL in
/-- **Every accumulator row of the tail holds at the honest values** (`groupRow_holds`). -/
theorem rows_honest (hS : M.Source HE) {p : Predicate} {g : ℕ} (hg : g < M.Gm.groups.length)
    (hrow : ir.groupRowB (ir.honestIvl primeNodes) M.dy M.u M.Gm M.acc g
      (M.Gm.groups.getD g default) p.body = true) :
    ir.HoldsWith HE p.body := by
  have hdy := M.dy_lt hwf
  have hunits := M.shape.1
  unfold macUnitsOkB at hunits
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hunits
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hpw, -⟩, -⟩, -⟩, hw0⟩, -⟩, -⟩, -⟩, -⟩ := hunits
  refine groupRow_holds hwf hI hL _ hdy M.char hw0 hpw (M.group_fit (M.group_mem hg)) hrow
    (fun i hi => M.acc_honest hgen stmtOf val SL y c π hS hg hi hw0) fun j hj => ?_
  have hj' : j < ir.exprLen M.y := by
    rw [M.lenY, ← M.units.2.2.1, ← M.units.2.2.2.1]
    exact hj
  rw [M.units.2.1]
  exact hS.ycast M.toMacBaseC hj'

/-- **The honest accumulators' quotients fit their digits** (`GroupedMacC.fit`): a group's sum is
at most `count · convMax` (`groupAcc_eq`). -/
theorem accNat_fit (hS : M.Source HE) {n : ℕ} (hn : n < M.Gm.groups.length * M.u.width)
    (hw : 0 < M.u.width) :
    ir.accNat HE M.dy M.u M.Gm n / 2 < M.Gm.base ^ M.Gm.digitCount := by
  have hg : n / M.u.width < M.Gm.groups.length := by
    rw [Nat.div_lt_iff_lt_mul hw]
    exact hn
  have hmem := M.group_mem hg
  have hle := (M.groupAcc_honest hgen stmtOf val SL y c π hS hw hmem (n % M.u.width)).2
  have := M.fit _ hmem
  unfold accNat
  calc _ ≤ (M.Gm.groups.getD (n / M.u.width) default).2 *
        Conv.convMax M.u.width M.u.taps.toFinset / 2 := Nat.div_le_div_right hle
    _ < _ := this

include hwf hI hL in
/-- **The honest residues are the accumulators modulo `2`** (`residue_honest`). -/
theorem residues_honest (hS : M.Source HE) {j : ℕ} (hj : j < M.Gm.groups.length * M.u.width) :
    ir.evalWith HE M.dy M.Gm.residues j =
      ((ir.accNat HE M.dy M.u M.Gm j % 2 : ℕ) : (I (ir.domainField M.dy)).K) := by
  have hdy := M.dy_lt hwf
  have hw0 : 0 < M.u.width := M.units.2.2.1 ▸ M.pos
  refine residue_honest hwf hI hL _ hdy M.char (by norm_num) M.shape.2.2.1
    (ir.accNat HE M.dy M.u M.Gm) hj ?_ ?_ (M.accNat_fit hgen stmtOf val SL y c π hS hj hw0)
  · exact reader_accC_honest hgen stmtOf val SL y c π M.hbt M.hG M.hu M.accGen M.accNotSource
      M.accLt M.accLate M.accField M.powNoLate M.yNoLate (by rw [M.acc_size]; exact hj)
  · intro gq' hgq' l hl
    rw [M.hD] at hgq'
    cases hgq'
    have hk : 0 < M.Gm.digitCount := by omega
    have hn : j * M.Gm.digitCount + l < (ir.value M.gq).size := by
      rw [M.gq_size]
      have : j * M.Gm.digitCount + l < (j + 1) * M.Gm.digitCount := by nlinarith
      calc _ < (j + 1) * M.Gm.digitCount := this
        _ ≤ _ := Nat.mul_le_mul_right _ hj
    rw [reader_quotDigitC_honest hgen stmtOf val SL y c π M.hbt M.hG M.hu M.gqGen M.gqNotSource
      M.gqLt M.gqLate M.gqField M.powNoLate M.yNoLate hn]
    have hdiv : (j * M.Gm.digitCount + l) / M.Gm.digitCount = j := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hk, Nat.div_eq_of_lt hl, zero_add]
    have hmod : (j * M.Gm.digitCount + l) % M.Gm.digitCount = l := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hl]
    simp only [digitNat, hdiv, hmod]

include hwf hI hL in
/-- **The residues' Boolean check holds at the honest values**: a field `equal` `R · R = R` of the
tail's domain on the residues `R`, which are the accumulators modulo `2` (`residues_honest`). -/
theorem residueCheck_honest (hS : M.Source HE) {d : ℕ} {R₁ R₂ R₃ : Expr} {tgt : Target}
    (hd : d = M.dy) (h1 : R₁.beq M.Gm.residues = true) (h2 : R₂.beq M.Gm.residues = true)
    (h3 : R₃.beq M.Gm.residues = true) :
    ir.HoldsWith HE (.equal d (.mul R₁ R₂) R₃ tgt) := by
  subst hd
  rw [Expr.eq_of_beq h1, Expr.eq_of_beq h2, Expr.eq_of_beq h3]
  intro i hi
  have hres := M.shape.2.2.1
  unfold residuesB at hres
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hres
  have hlen := hres.1.1.2
  have hi' : i < M.Gm.groups.length * M.u.width := by
    rw [← hlen]
    exact hi
  simp only [evalWith, evalE_mul]
  have hr := M.residues_honest hgen stmtOf val SL y c π hwf hI hL hS hi'
  simp only [evalWith] at hr
  rw [hr]
  rcases Nat.mod_two_eq_zero_or_one (ir.accNat HE M.dy M.u M.Gm i) with h | h <;> rw [h] <;> simp

/-- **The digits' lookups hold at the honest values**: every honest digit is below the base, at
most the lookup's bound (`GroupedMacC.digitsRoom`). -/
theorem digitsLookup_honest {p : Predicate} (hp : p ∈ ir.predicates) {d N : ℕ}
    {r : LookupRealization} (hb : p.body = .mem d [.leaf M.gq] (.range N) (.lookup r)) :
    ir.HoldsWith HE p.body := by
  obtain ⟨rfl, hT, hN⟩ := M.digitsRoom p hp d N r hb
  rw [hb]
  intro i hi e he
  simp only [List.mem_singleton] at he
  subst he
  have hi' : i < (ir.value M.gq).size := by simpa [exprLen, Expr.len] using hi
  refine ⟨ir.digitNat HE M.dy 2 M.u M.Gm i, ?_, ?_⟩
  · exact (Nat.mod_lt _ hT).trans_le hN
  · simp only [evalWith, evalE_leaf]
    exact reader_quotDigitC_honest hgen stmtOf val SL y c π M.hbt M.hG M.hu M.gqGen M.gqNotSource
      M.gqLt M.gqLate M.gqField M.powNoLate M.yNoLate hi'

variable (hM : I.MacModel ir)

include hwf hI hL in
/-- **The tail's left side on the integers, by groups**: at an output coordinate `i < w`, the
blind's integer reading plus the honest accumulators of the groups (`evalIntWith_macUnits`, the
groups tile the chunks, `groupAcc_eq`). -/
theorem lhs_honest (hS : M.Source HE) {i : ℕ} (hi : i < M.u.width) :
    ir.evalIntWith HE M.dy M.L i = ir.intOf HE M.u.blind i +
      ∑ g ∈ Finset.range M.Gm.groups.length, (ir.accNat HE M.dy M.u M.Gm (g * M.u.width + i) : ℤ) := by
  have hdy := M.dy_lt hwf
  have hunits := M.shape.1
  unfold macUnitsOkB at hunits
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hunits
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, hw0⟩, -⟩, hcmB⟩, -⟩, htile⟩ := hunits
  split at hcmB
  · simp only [decide_eq_true_eq] at hcmB
    rw [eq_of_macUnits? M.hu, evalIntWith_macUnits hwf hI hL _ hdy M.char M.u hw0 hcmB hi,
      Finset.range_eq_Ico, sum_tiles _ htile, GroupedMod.chunkRuns, List.map_map,
      list_sum_map_eq_sum_range]
    congr 1
    refine Finset.sum_congr rfl fun g hg => ?_
    obtain ⟨hU, -⟩ := M.groupAcc_honest hgen stmtOf val SL y c π hS hw0
      (M.group_mem (Finset.mem_range.1 hg)) i
    have hdiv : (g * M.u.width + i) / M.u.width = g := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hw0, Nat.div_eq_of_lt hi, zero_add]
    have hmod : (g * M.u.width + i) % M.u.width = i := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
    simp only [Function.comp_apply, accNat, hdiv, hmod]
    exact hU.symm
  · simp at hcmB

include hwf hI hL hM in
/-- **The final quotient's lookups hold at the honest values**: the final sum `b + Σ_g r_g` (the
blind's bit and the residues, the accumulators modulo `2`) is congruent to the target's bit modulo
`2`, as the tail's left side is (`tail_honest`, `lhs_honest`), so the final quotient
`(b + Σ_g r_g − t) / 2` is a natural, at most `(1 + groups) / 2`, below the lookup's bound
(`GroupedMacC.finalRoom`). -/
theorem finalLookup_honest (hB : ir.BlindsArePadCopies) (hS : M.Source HE) {p : Predicate}
    (hp : p ∈ ir.predicates) {d N : ℕ} {D : Expr} {r : LookupRealization}
    (hb : p.body = .mem d [D] (.range N) (.lookup r)) (hD : D.beq M.realT.quotExpr = true) :
    ir.HoldsWith HE p.body := by
  obtain ⟨rfl, hroom⟩ := M.finalRoom p hp d D N r hb hD
  set E := ir.honestEnv I (stmtOf y) (val y) (ir.genLateOf I hgen stmtOf val SL y) c π with hE
  set rd := ir.reader E with hrd
  have hdy := M.dy_lt hwf
  have h2 := M.char
  rw [hb, Expr.eq_of_beq hD]
  intro i hi e he
  simp only [List.mem_singleton] at he
  subst he
  have hiw : i < M.u.width := by
    rw [← M.quot_len]
    simpa using hi
  obtain ⟨bI, hbI1, hbint, hbcast⟩ := M.blind_honest hgen stmtOf val SL y c π hwf hL hB hiw
  obtain ⟨bt, hbt2, heint, hecast⟩ := M.target_honest hwf hL hM E i
  rw [← hE, ← hrd] at hbint hbcast
  rw [← hrd] at heint hecast
  replace hecast : ir.evalWith rd M.dy M.R i = ((bt : ℤ) : (I (ir.domainField M.dy)).K) := by
    rw [hecast]
    simp
  have htail := M.tail_honest hgen stmtOf val SL y c π hwf hI hL hM hB hS
  rw [M.hbt] at htail
  have hLlen : i < ir.exprLen M.L := M.lLen ▸ hiw
  have hcongL := htail i hLlen
  rw [M.lhs_honest hgen stmtOf val SL y c π hwf hI hL hS hiw, hbint, heint] at hcongL
  set A := fun g => ir.accNat rd M.dy M.u M.Gm (g * M.u.width + i)
  set ng := M.Gm.groups.length
  have hρ : ∀ g < ng, ir.evalWith rd M.dy M.Gm.residues (g * M.u.width + i) =
      ((A g % 2 : ℕ) : (I (ir.domainField M.dy)).K) := fun g hg =>
    M.residues_honest hgen stmtOf val SL y c π hwf hI hL hS (by nlinarith)
  have hcong : (2 : ℤ) ∣ (bI : ℤ) + ∑ g ∈ Finset.range ng, ((A g % 2 : ℕ) : ℤ) - bt := by
    have hmod : ∀ g, ((A g : ℕ) : ℤ) = ((A g % 2 : ℕ) : ℤ) + 2 * ((A g / 2 : ℕ) : ℤ) := fun g => by
      push_cast
      omega
    obtain ⟨z, hz⟩ := hcongL
    refine ⟨z - ∑ g ∈ Finset.range ng, ((A g / 2 : ℕ) : ℤ), ?_⟩
    have hs : ∑ g ∈ Finset.range ng, ((A g : ℕ) : ℤ) = ∑ g ∈ Finset.range ng, ((A g % 2 : ℕ) : ℤ) +
        2 * ∑ g ∈ Finset.range ng, ((A g / 2 : ℕ) : ℤ) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun g _ => hmod g
    rw [hs] at hz
    push_cast at hz ⊢
    linarith
  have hQ := finalQuot_honest hwf hI hL rd hdy h2 M.shape.2.2.2 hiw (fun g => A g % 2) hρ bI bt
    hbcast hecast hcong
  have hF0 : 0 ≤ ∑ g ∈ Finset.range ng, ((A g % 2 : ℕ) : ℤ) :=
    Finset.sum_nonneg fun g _ => Int.natCast_nonneg _
  have hF1 : ∑ g ∈ Finset.range ng, ((A g % 2 : ℕ) : ℤ) ≤ ng := by
    have : ∑ g ∈ Finset.range ng, ((A g % 2 : ℕ) : ℤ) ≤ ∑ _g ∈ Finset.range ng, (1 : ℤ) :=
      Finset.sum_le_sum fun g _ => by
        have := Nat.mod_lt (A g) (by norm_num : 0 < 2)
        omega
    simpa using this
  obtain ⟨z, hz⟩ := hcong
  have hz0 : 0 ≤ z := by
    by_contra hneg
    push Not at hneg
    omega
  refine ⟨z.toNat, ?_, ?_⟩
  · have : z ≤ (ng + 1) / 2 := by omega
    omega
  · rw [hQ, hz]
    have h2z : (2 * z) / ((2 : ℕ) : ℤ) = z := by
      rw [Nat.cast_ofNat]
      exact Int.mul_ediv_cancel_left _ (by norm_num)
    rw [h2z]
    have h := congrArg (Int.cast (R := (I (ir.domainField M.dy)).K)) (Int.toNat_of_nonneg hz0)
    rw [Int.cast_natCast] at h
    exact h.symm

end GroupedMacC

namespace GroupedMacC

variable {G : Gens} (M : ir.GroupedMacC primeNodes G)

/-- **The predicates the MAC's honest values satisfy**: its tail, an accumulator row, the residues'
Boolean check, a lookup on its quotient digits or on its final quotient, its H predicate. -/
def Role (b : PredBody) : Prop :=
  b = (ir.predicate M.t).body ∨
    (∃ g < M.Gm.groups.length,
      ir.groupRowB (ir.honestIvl primeNodes) M.dy M.u M.Gm M.acc g (M.Gm.groups.getD g default) b =
        true) ∨
    (∃ R₁ R₂ R₃ tgt, b = .equal M.dy (.mul R₁ R₂) R₃ tgt ∧ R₁.beq M.Gm.residues = true ∧
      R₂.beq M.Gm.residues = true ∧ R₃.beq M.Gm.residues = true) ∨
    (∃ d N r, b = .mem d [.leaf M.gq] (.range N) (.lookup r)) ∨
    (∃ d D N r, b = .mem d [D] (.range N) (.lookup r) ∧ D.beq M.realT.quotExpr = true) ∨
    ∃ hp, M.real.hPredicate = some hp ∧ b = (ir.predicate hp).body

variable {Inp : Type} (hgen : ir.CGenFacts I G) (stmtOf val : Inp → ir.Valuation I)
  (SL : ir.SrcLate I Inp) (y : Inp) (c : ∀ k, (ir.layout I).Ch k) (π : (ir.layout I).Pads)
  (hwf : ir.WellFormed) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes) (hM : I.MacModel ir)

set_option hygiene false in
local notation "HE" =>
  ir.reader (ir.honestEnv I (stmtOf y) (val y) (ir.genLateOf I hgen stmtOf val SL y) c π)

include hwf hI hL hM in
/-- **The MAC's predicates hold at the honest values** (`Role`), where the
source facts hold. -/
theorem role_holds (hB : ir.BlindsArePadCopies)
    (hpow2 : ∀ j < M.real.width, (I M.real.macField).decode (2 ^ j) = (I M.real.macField).decode 2 ^ j)
    (htag1 : (ir.value M.real.tag).size = 1) (hS : M.Source HE)
    {p : Predicate} (hp : p ∈ ir.predicates) (hr : M.Role p.body) :
    ir.HoldsWith HE p.body := by
  rcases hr with h | ⟨g, hg, h⟩ | ⟨R₁, R₂, R₃, tgt, h, h1, h2, h3⟩ | ⟨d, N, r, h⟩ |
    ⟨d, D, N, r, h, hD⟩ | ⟨q, hq, h⟩
  · rw [h]
    exact M.tail_honest hgen stmtOf val SL y c π hwf hI hL hM hB hS
  · exact M.rows_honest hgen stmtOf val SL y c π hwf hI hL hS hg h
  · rw [h]
    exact M.residueCheck_honest hgen stmtOf val SL y c π hwf hI hL hS rfl h1 h2 h3
  · exact M.digitsLookup_honest hgen stmtOf val SL y c π hp h
  · exact M.finalLookup_honest hgen stmtOf val SL y c π hwf hI hL hM hB hS hp h hD
  · have hok := M.hok_of_hPred hq
    have hhalf := hok.half
    unfold macHalfB at hhalf
    rw [hq] at hhalf
    rw [h]
    exact hPred_holds_of_macHHolds hwf.refsOrdered hI hL _ hhalf hok.hField hok.field hok.tag hpow2 htag1
      ((macTagC_honest hgen stmtOf val SL y c π M.hb hok.tag M.tagGen M.tagNotSource M.tagLate
        M.xNoLate).hosted hok.noBlindX)

/-- **The MAC's honest tag** (`MacTagAt`; `macTagC_honest`) at the honest environment of the
certificate. -/
theorem macTag_honest :
    ir.MacTagAt HE M.dx M.x M.real (castElt ((ir.honestEnv I (stmtOf y) (val y)
        (ir.genLateOf I hgen stmtOf val SL y) c π).chal M.real.key 0)) :=
  macTagC_honest hgen stmtOf val SL y c π M.hb M.tag M.tagGen M.tagNotSource M.tagLate M.xNoLate

end GroupedMacC

end

end GordieHowe.RealizedProgram
