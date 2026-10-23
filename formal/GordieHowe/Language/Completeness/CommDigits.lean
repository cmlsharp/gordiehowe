-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Completeness.Digits

@[expose] public section

/-!
# GordieHowe: completeness certificates, the committed digits of a quotient

A source `mod_q` in the committed-digits form commits its quotient's radix-`R` digits `D_j`, each
the record of a digit lookup `lk` whose digits are generated as committed digits
(`Gen.commDigit m j lk k`): the honest committed value at digit `k` of `lk` is digit `k` in the
lookup's base `T` of digit `j` of the honest quotient read in the environment of the execution
(`genCommitted_commDigit`). The facts of such a lookup (`CommLookupFactsC`, decided by
`commLookupCB`) and of the `mod_q` (`CommModFactsC`, decided by `commModCB`);
the lookups of the quotient digits are named by the field equation's derivation (`commRowCB`).

At the source environment of the honest committed values, the honest quotient lies below `R^K`
and the sides satisfy `e − e' = q·qlo + q·Q` (`commQuot_specC`), each record reads its honest
quotient digit (`commRec_srcEnvC`), so the lookup holds (`holds_commInC`), the field equation holds
(`holds_commRowC`) and the digits of every two-sided and digit lookup are below their bases
(`digitsBelow_srcEnvCC`).
-/

namespace GordieHowe.RealizedProgram

open Export ProofSystem.PhaseLayout IOP Range

section

variable {ir : RealizedProgram} {I : Interp} {primeNodes : ℕ → List String}
  {L : ℕ → ℕ → Option Ivl}

variable (ir) in
/-- **The facts of a digit lookup whose record is a committed-digits `mod_q`'s quotient digit** at
the certificate's generators `G`, at the `in`
predicate `lk` with body `mem d [rec] (range N) (lookup r)` whose record is digit `j` of the
`mod_q` `m` with body `mod d q e e' real`: a digit lookup of a domain with `k` digit values and no
second digits, each generated as the committed digit `⟨m, j, lk, k⟩` at its position, a committed
cell of the record's length in the domain's field that is no source value; the base above `1`; the
record the number of its digits (`digitsExprOk`) and digit `j` of the `mod_q`, of the sides'
length; the radix `R` with `R ≤ N` (the honest quotient digit lies in the range) and `R ≤ T^k`
(the digits hold it); the range within the characteristic. -/
structure CommLookupFactsC (G : Gens) (lk d : ℕ) (rec : Expr) (N : ℕ) (r : LookupRealization)
    (m j : ℕ) (q : ℕ) (e e' : Expr) (real : ModRealization) : Prop where
  /-- A digit lookup. -/
  kind : r.kind = .digits
  /-- A domain of the program. -/
  domain : d < ir.domains.length
  /-- `k` digit values. -/
  len : r.digitValues.length = r.digits
  /-- No second digits. -/
  second : r.second = []
  /-- The digit values are generated as the committed digits at their positions. -/
  own : ∀ k (hk : k < r.digitValues.length), G.at r.digitValues[k] = .commDigit m j lk k
  /-- The digits are committed cells of the record's length in the domain's field, no source
  values. -/
  cells : ∀ u ∈ r.digitValues, ir.privCellB u = true ∧ (ir.value u).size = ir.exprLen rec ∧
    ir.valueField u = ir.domainField d ∧ ¬ ir.IsSourceValue u
  /-- The base exceeds `1`. -/
  baseGt : 1 < r.base
  /-- The record, through a shared expression (`unref`), is the number of its digits. -/
  expr : digitsExprOk (ir.charOf (ir.domainField d)) r.base (ir.unref rec) r.digitValues = true
  /-- The record is digit `j` of the `mod_q`. -/
  isDigit : (real.digits[j]?.map fun D => D.beq rec) = some true
  /-- The record has the sides' length. -/
  recLen : ir.exprLen rec = ir.exprLen e
  /-- The honest quotient digit lies in the range. -/
  radixLe : real.radix ≤ N
  /-- The digits hold the honest quotient digit. -/
  radixDigits : real.radix ≤ r.base ^ r.digits
  /-- The range lies within the characteristic. -/
  rangeLe : N ≤ ir.charOf (ir.domainField d)

instance (G : Gens) (lk d : ℕ) (rec : Expr) (N : ℕ) (r : LookupRealization) (m j q : ℕ)
    (e e' : Expr) (real : ModRealization) :
    Decidable (ir.CommLookupFactsC G lk d rec N r m j q e e' real) :=
  decidable_of_iff (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
    ⟨fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ =>
      ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩,
     fun h => ⟨h.kind, h.domain, h.len, h.second, h.own, h.cells, h.baseGt, h.expr, h.isDigit,
      h.recLen, h.radixLe, h.radixDigits, h.rangeLe⟩⟩

variable (ir) in
/-- **The facts of the committed-digits lookup `lk` at digit `j` of the `mod_q` `m`, as a check**
(`CommLookupFactsC`): `lk` has one record and a range,
`m` is a `mod_q` of the same domain. -/
def commLookupCB (G : Gens) (lk m j : ℕ) : Bool :=
  match (ir.predicate lk).body, (ir.predicate m).body with
  | .mem d [rec] (.range N) (.lookup r), .mod d' q e e' real =>
    decide (d' = d) && decide (ir.CommLookupFactsC G lk d rec N r m j q e e' real)
  | _, _ => false

variable (ir L) in
/-- **The honest-quotient facts of a source committed-digits `mod_q`** `m` with body
`mod d q e e' real`: `q > 0`, `p > 2`; the sides' intervals from the source values
(`srcIvl`) within the exported `[lhsLo, lhsHi]` and `[rhsLo, rhsHi]`; the honest quotient
`(e − e')/q` at least `qlo` and below `qlo + R^K`; the sides read no challenge. -/
structure CommModFactsC (m d q : ℕ) (e e' : Expr) (real : ModRealization) : Prop where
  /-- A source predicate. -/
  source : ir.inSource (ir.predicate m) = true
  /-- The committed-digits form. -/
  form : real.form = .committedDigits
  /-- The modulus is positive. -/
  qpos : 0 < q
  /-- The characteristic exceeds `2`. -/
  char : 2 < ir.charOf (ir.domainField d)
  /-- The left side's interval lies within the exported one. -/
  lhs : IvlWithin (ir.srcIvl L (ir.domainField d) e) real.lhsLo real.lhsHi
  /-- The right side's interval lies within the exported one. -/
  rhs : IvlWithin (ir.srcIvl L (ir.domainField d) e') real.rhsLo real.rhsHi
  /-- The honest quotient is at least `qlo`. -/
  lo : (q : ℤ) * (real.quotientLo - 1) < real.lhsLo - real.rhsHi
  /-- The honest quotient lies below `qlo + R^K`. -/
  hi : real.lhsHi - real.rhsLo <
    (q : ℤ) * (real.quotientLo + ((real.radix ^ real.digits.length : ℕ) : ℤ))
  /-- The radix is positive. -/
  radixPos : 0 < real.radix
  /-- The sides read no challenge and no late value. -/
  noChal : ∀ w ∈ ir.exprNodes e ++ ir.exprNodes e', (ir.readsT.getD w []).isEmpty = true

instance (m d q : ℕ) (e e' : Expr) (real : ModRealization) :
    Decidable (ir.CommModFactsC L m d q e e' real) :=
  decidable_of_iff (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
    ⟨fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ =>
      ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩,
     fun h => ⟨h.source, h.form, h.qpos, h.char, h.lhs, h.rhs, h.lo, h.hi, h.radixPos,
      h.noChal⟩⟩

variable (ir primeNodes) in
/-- **Predicate `m` is a source committed-digits `mod_q` with its honest-quotient facts**
(`CommModFactsC` at the values' intervals `srcLeafIvl`), as a check. -/
def commModCB (m : ℕ) : Bool :=
  match (ir.predicate m).body with
  | .mod d q e e' real => decide (ir.CommModFactsC (ir.srcLeafIvl primeNodes) m d q e e' real)
  | _ => false

variable (ir primeNodes) in
/-- **Predicate `pr` is the field equation of the committed-digits `mod_q` `m`** whose quotient
digit `j` is the record of the lookup `lks[j]`, as a check: `m` has its honest-quotient facts
(`commModCB`), `pr` is its field equation (`commRowB`), and `lks` names one lookup per quotient
digit with its facts (`commLookupCB`). -/
def commRowCB (G : Gens) (m : ℕ) (lks : List ℕ) (pr : Predicate) : Bool :=
  match (ir.predicate m).body with
  | .mod d q e e' real =>
    ir.commModCB primeNodes m && ir.commRowB d q e e' real pr.body &&
      lks.length == real.digits.length &&
      (List.range lks.length).all fun j => ir.commLookupCB G (lks.getD j 0) m j
  | _ => false

/-- **A committed-digits lookup passing its check** has one record and a range, its `mod_q` of the
same domain, and its facts. -/
theorem commLookupFactsC_of_B {G : Gens} {lk m j : ℕ} (h : ir.commLookupCB G lk m j = true) :
    ∃ d rec N r q e e' real, (ir.predicate lk).body = .mem d [rec] (.range N) (.lookup r) ∧
      (ir.predicate m).body = .mod d q e e' real ∧
        ir.CommLookupFactsC G lk d rec N r m j q e e' real := by
  unfold commLookupCB at h
  split at h
  · rename_i d rec N r d' q e e' real hb hbm
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨rfl, hF⟩ := h
    exact ⟨d', rec, N, r, q, e, e', real, hb, hbm, hF⟩
  · cases h

/-- **A `mod_q` passing `commModCB`** has its body and its honest-quotient facts. -/
theorem commModFactsC_of_B {m : ℕ} (h : ir.commModCB primeNodes m = true) :
    ∃ d q e e' real, (ir.predicate m).body = .mod d q e e' real ∧
      ir.CommModFactsC (ir.srcLeafIvl primeNodes) m d q e e' real := by
  unfold commModCB at h
  split at h
  · rename_i d q e e' real hb
    exact ⟨d, q, e, e', real, hb, of_decide_eq_true h⟩
  · cases h

/-- **A `mod_q` with its honest-quotient facts is a predicate of the program**: past the
predicates the default predicate is no source predicate. -/
theorem lt_of_commModFactsC {m d q : ℕ} {e e' : Expr}
    {real : ModRealization} (hb : (ir.predicate m).body = .mod d q e e' real)
    (_hM : ir.CommModFactsC L m d q e e' real) : m < ir.predicates.length := by
  by_contra h
  simp only [predicate, List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt h),
    Option.getD_none] at hb
  cases hb

/-- **The honest committed value at a committed digit**: digit `k` in the lookup's base `T` of
digit `j` in the radix `R` of the honest quotient read in the environment of the execution. -/
theorem genCommitted_commDigit {G : Gens} {lk d N m j q : ℕ} {rec e e' : Expr}
    {r : LookupRealization} {real : ModRealization} (x s : ir.Valuation I)
    (hb : (ir.predicate lk).body = .mem d [rec] (.range N) (.lookup r))
    (hbm : (ir.predicate m).body = .mod d q e e' real)
    (hF : ir.CommLookupFactsC G lk d rec N r m j q e e' real) {k : ℕ}
    (hk : k < r.digitValues.length) (i : ℕ) :
    ir.genCommitted I G x s r.digitValues[k] i =
      ((ir.commQuot (ir.reader (ir.execEnv I x s 0 (ir.chal0 I))) m i / real.radix ^ j %
        real.radix / r.base ^ k % r.base : ℕ) : (I (ir.valueField r.digitValues[k])).K) := by
  obtain ⟨-, -, -, hns⟩ := hF.cells _ (List.getElem_mem hk)
  simp only [genCommitted, withGens, if_neg hns, hF.own k hk, commDigitNat, hbm, hb, lookupOf?]

variable (hwf : ir.WellFormed) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
  {G : Gens} (R : ir.CommittedFacts I G) {x s l : ir.Valuation I} {c : ∀ k, (ir.layout I).Ch k}
  (hA : ir.SourceAcceptingAt I (ir.execEnv I x s l c)) (π : (ir.layout I).Pads)

set_option hygiene false in
/-- The source environment of the honest committed values of the execution. -/
local notation "SE" => ir.srcEnvL I x (ir.genCommitted I G x s) (ir.padSpaceLate I l) c π

include hwf hI hL R hA in
/-- **The honest quotient reads alike** in the environment of the execution at the default
challenges and at the source environment of the honest committed values: its sides read source
values that read no challenge and no late value. -/
theorem commQuot_exec0C {m d q : ℕ} {e e' : Expr}
    {real : ModRealization} (hb : (ir.predicate m).body = .mod d q e e' real)
    (hM : ir.CommModFactsC L m d q e e' real) (i : ℕ) :
    ir.commQuot (ir.reader (ir.execEnv I x s 0 (ir.chal0 I))) m i =
      ir.commQuot (ir.reader SE) m i := by
  have hm := lt_of_commModFactsC hb hM
  have hS : ∀ z, (d, z) ∈ (ir.predicate m).body.exprs → (∀ w ∈ ir.exprNodes z,
      (ir.readsT.getD w []).isEmpty = true) → ∀ w ∈ ir.exprNodes z,
      ir.reader (ir.execEnv I x s 0 (ir.chal0 I)) w = ir.reader SE w := fun z hz hn w hw =>
    (reader_srcEnvC_eq_exec0 hwf hI hL R hA π (R.sourceValid.preds _ (predicate_mem hm) hM.source w
      (List.mem_append_left _ (List.mem_flatMap.2 ⟨(d, z), hz, hw⟩))) (hn w hw)).symm
  unfold commQuot
  rw [hb]
  simp only
  rw [evalIntWith_congr (hS e (by rw [hb]; simp [PredBody.exprs])
      fun w hw => hM.noChal w (List.mem_append_left _ hw)),
    evalIntWith_congr (hS e' (by rw [hb]; simp [PredBody.exprs])
      fun w hw => hM.noChal w (List.mem_append_right _ hw))]

include hwf hI hL R hA in
/-- **The honest quotient of a committed-digits `mod_q` at the source environment** of the honest
committed values where the execution accepts (`CommQuotSpec`): the source `mod_q`
makes `e − e' = q z` over the integers, the sides' intervals from the source values bound them
(`exprIvl_within_of`), so `qlo ≤ z < qlo + R^K`, and the honest quotient is `z − qlo`. -/
theorem commQuot_specC (hbd : ir.StmtBounded I x) {m d q : ℕ} {e e' : Expr}
    {real : ModRealization} (hb : (ir.predicate m).body = .mod d q e e' real)
    (hM : ir.CommModFactsC (ir.srcLeafIvl primeNodes) m d q e e' real) {i : ℕ}
    (hi : i < ir.exprLen e) :
    ir.CommQuotSpec (ir.reader SE) d q e e' real i (ir.commQuot (ir.reader SE) m i) := by
  have hm := lt_of_commModFactsC hb hM
  have hsat := sourceSatAt_srcEnvC hwf hI hL R hA π
  have hIF := ivlFacts_srcEnvC hwf hI hL R hA π hbd
  have hlok := ir.leafIvl_justified primeNodes ir.declaredRanges
  have hmod := hsat.preds _ (predicate_mem hm) hM.source
  rw [hb] at hmod
  have hpo := hwf.predicates _ (predicate_mem hm)
  rw [hb] at hpo
  have he := hpo.1 (d, e) (by simp [PredBody.exprs])
  have he' := hpo.1 (d, e') (by simp [PredBody.exprs])
  have hlen : ir.exprLen e = ir.exprLen e' := hpo.2
  obtain ⟨⟨h1, h2⟩, hc⟩ := exprIvl_within_of hwf hI hL hIF hlok he.1 hM.char he.2 hM.lhs hi
  obtain ⟨⟨h3, h4⟩, hc'⟩ := exprIvl_within_of hwf hI hL hIF hlok he'.1 hM.char he'.2 hM.rhs
    (by rw [← hlen]; exact hi)
  simp only at h1 h2 h3 h4 hc hc'
  obtain ⟨z, hz⟩ := hmod i hi
  have hq0 : (0 : ℤ) < q := by exact_mod_cast hM.qpos
  have hlo := hM.lo
  have hhi := hM.hi
  have hzlo : real.quotientLo ≤ z := by
    by_contra hc0
    have : (q : ℤ) * z ≤ q * (real.quotientLo - 1) := mul_le_mul_of_nonneg_left (by omega) hq0.le
    linarith
  have hzhi : z < real.quotientLo + ((real.radix ^ real.digits.length : ℕ) : ℤ) := by
    by_contra hc0
    have : (q : ℤ) * (real.quotientLo + ((real.radix ^ real.digits.length : ℕ) : ℤ)) ≤ q * z :=
      mul_le_mul_of_nonneg_left (by omega) hq0.le
    linarith
  have hQ : ir.commQuot (ir.reader SE) m i = (z - real.quotientLo).toNat := by
    unfold commQuot
    rw [hb]
    simp only
    rw [hz, Int.mul_ediv_cancel_left _ (by omega)]
  have hzz : (((z - real.quotientLo).toNat : ℕ) : ℤ) = z - real.quotientLo :=
    Int.toNat_of_nonneg (by omega)
  refine ⟨?_, ?_⟩
  · rw [hQ]
    omega
  · rw [← hc, ← hc', hQ, ← Int.cast_natCast (R := (I (ir.domainField d)).K), ← Int.cast_sub,
      ← Int.cast_add]
    congr 1
    push_cast
    rw [hzz]
    linear_combination hz

include hwf hI hL R hA in
/-- **A committed-digits lookup's record reads its honest quotient digit** at the source
environment of the honest committed values: the record is the number of its
digits (`digitsExprOk`), each digit `k` in base `T` of the quotient digit
(`genCommitted_commDigit`), which lies below `R ≤ T^k`. -/
theorem commRec_srcEnvC {lk d N m j q : ℕ} {rec e e' : Expr}
    {r : LookupRealization} {real : ModRealization}
    (hb : (ir.predicate lk).body = .mem d [rec] (.range N) (.lookup r))
    (hbm : (ir.predicate m).body = .mod d q e e' real)
    (hF : ir.CommLookupFactsC G lk d rec N r m j q e e' real)
    (hM : ir.CommModFactsC L m d q e e' real) {i : ℕ} (hi : i < ir.exprLen rec) :
    ir.evalWith (ir.reader SE) d rec i =
      ((ir.commQuot (ir.reader SE) m i / real.radix ^ j % real.radix : ℕ) :
        (I (ir.domainField d)).K) := by
  have hf := domainField_lt hwf hF.domain
  have hlt : ir.commQuot (ir.reader SE) m i / real.radix ^ j % real.radix <
      r.base ^ r.digitValues.length := by
    rw [hF.len]
    exact lt_of_lt_of_le (Nat.mod_lt _ hM.radixPos) hF.radixDigits
  unfold evalWith
  rw [← evalE_unref hwf, evalE_of_digitsExprOk_digits hL hf hF.expr (n := ir.commQuot
      (ir.reader SE) m i / real.radix ^ j % real.radix) fun k hk => ?_,
    Nat.mod_eq_of_lt hlt]
  obtain ⟨hc, hsz, hfu, -⟩ := hF.cells _ (List.getElem_mem hk)
  rw [reader_srcEnvL_of_privCellB x _ _ c π hc (by rw [hsz]; exact hi),
    genCommitted_commDigit x s hb hbm hF hk, castElt_natCast hfu,
    commQuot_exec0C hwf hI hL R hA π hbm hM]

include hwf hI hL R hA in
/-- **A digit lookup whose record is a quotient digit holds** at the source environment of the
honest committed values: the record reads its honest quotient digit
(`commRec_srcEnvC`), below `R ≤ N`. -/
theorem holds_commInC {lk m j : ℕ} (h : ir.commLookupCB G lk m j = true)
    (hm : ir.commModCB primeNodes m = true) :
    ir.HoldsWith (ir.reader SE) (ir.predicate lk).body := by
  obtain ⟨d, rec, N, r, q, e, e', real, hb, hbm, hF⟩ := commLookupFactsC_of_B h
  obtain ⟨d₁, q₁, e₁, e₁', real₁, hbm₁, hM⟩ := commModFactsC_of_B hm
  rw [hbm] at hbm₁
  simp only [PredBody.mod.injEq] at hbm₁
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hbm₁
  rw [hb]
  intro i hi
  simp only [List.headD_cons] at hi
  exact (inRows_range_iff _ d rec i N).2 ⟨_, lt_of_lt_of_le (Nat.mod_lt _ hM.radixPos) hF.radixLe,
    (commRec_srcEnvC hwf hI hL R hA π hb hbm hF hM hi).symm⟩

include hwf hI hL R hA in
/-- **The field equation of a committed-digits `mod_q` holds** at the source environment of the
honest committed values where the execution accepts: the row reads
`e − e' − q·qlo − q·Σ_j R^j D_j` (`evalE_of_commPeel`, `commShift_spec`, `sum_zipIdx_mul`), each
quotient digit `D_j` is the record of the lookup `lks[j]` and reads digit `j` of the honest
quotient `Q` (`commRec_srcEnvC`), so `Σ_j R^j D_j = Q` below `R^K`, and `e − e' = q·qlo + q·Q`
(`commQuot_specC`). -/
theorem holds_commRowC (hbd : ir.StmtBounded I x) {m : ℕ} {lks : List ℕ} {pr : Predicate}
    (h : ir.commRowCB primeNodes G m lks pr = true) : ir.HoldsWith (ir.reader SE) pr.body := by
  set rd := ir.reader SE with hrd
  unfold commRowCB at h
  split at h
  · rename_i d q e e' real hbm
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
    obtain ⟨⟨⟨hmB, hrow⟩, hlks⟩, hlk⟩ := h
    obtain ⟨d₁, q₁, e₁, e₁', real₁, hbm₁, hM⟩ := commModFactsC_of_B hmB
    rw [hbm] at hbm₁
    simp only [PredBody.mod.injEq] at hbm₁
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hbm₁
    have hm := lt_of_commModFactsC hbm hM
    have hpo := hwf.predicates _ (predicate_mem hm)
    rw [hbm] at hpo
    have hd : d < ir.domains.length := (hpo.1 (d, e) (by simp [PredBody.exprs])).1
    have hf := domainField_lt hwf hd
    obtain ⟨-, hchar, -, hdec0⟩ := modData hwf hI hL hd hM.char
    have hdec : ∀ c' < ir.charOf (ir.domainField d),
        (I (ir.domainField d)).decode c' = (c' : (I (ir.domainField d)).K) := hdec0
    have hp0 : 0 < ir.charOf (ir.domainField d) := by have := hM.char; omega
    have hneg : ∀ c', c' + 1 = ir.charOf (ir.domainField d) →
        (I (ir.domainField d)).decode c' = -1 := by
      intro c' hc'
      rw [hdec c' (by omega), eq_neg_iff_add_eq_zero, ← Nat.cast_one, ← Nat.cast_add, hc',
        CharP.cast_eq_zero]
    obtain ⟨hshl, hshc⟩ := commShift_spec (K := (I (ir.domainField d)).K) hp0 q real
    unfold commRowB at hrow
    split at hrow
    · rename_i d' L z t hbody
      simp only [Bool.and_eq_true, beq_iff_eq] at hrow
      obtain ⟨⟨hd', hz⟩, hmt⟩ := hrow
      subst d'
      split at hmt
      · rename_i hh hpeel
        obtain ⟨hev, hlenL⟩ := evalE_of_commPeel rd hdec _ L hpeel
        unfold commHeadB at hmt
        split at hmt
        · rename_i Xh b sh
          simp only [Bool.and_eq_true, beq_iff_eq] at hmt
          obtain ⟨⟨hX, hb⟩, hsh⟩ := hmt
          obtain ⟨hXe, hXl⟩ := evalE_of_subB rd hdec e e' Xh hX
          rw [hbody]
          intro i hi
          rw [hlenL, exprLen_add, hXl] at hi
          have hQ := commQuot_specC hwf hI hL R hA π hbd hbm hM hi
          have hdig : ∀ j (hj : j < real.digits.length),
              ir.evalE rd (ir.domainField d) real.digits[j] i =
                ((ir.commQuot rd m i / real.radix ^ j % real.radix : ℕ) :
                  (I (ir.domainField d)).K) := by
            intro j hj
            obtain ⟨d₂, rec, N, r, q₂, e₂, e₂', real₂, hb₂, hbm₂, hF⟩ :=
              commLookupFactsC_of_B (hlk j (by rw [hlks]; exact hj))
            rw [hbm] at hbm₂
            simp only [PredBody.mod.injEq] at hbm₂
            obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hbm₂
            have hD : real.digits[j] = rec := by
              have h0 := hF.isDigit
              rw [List.getElem?_eq_getElem hj, Option.map_some, Option.some.injEq] at h0
              exact Expr.eq_of_beq h0
            rw [hD]
            exact commRec_srcEnvC hwf hI hL R hA π hb₂ hbm hF hM (by rw [hF.recLen]; exact hi)
          have hsum : digitsVal (real.radix : (I (ir.domainField d)).K)
              (real.digits.map fun D => ir.evalE rd (ir.domainField d) D i) =
                ((ir.commQuot rd m i : ℕ) : (I (ir.domainField d)).K) := by
            rw [map_eq_map_range real.digits _ _ hdig, digitsVal_range_digits,
              Nat.mod_eq_of_lt hQ.lt]
          have hsides := hQ.sides
          simp only [evalWith] at hsides ⊢
          rw [hev i, evalE_add, evalE_scale_const, hXe i, hneg b hb,
            evalE_leaf_constAll_reader hL _ hsh hf hshl hi,
            evalE_leaf_constAll_reader hL _ hz hf hp0 hi,
            hshc, List.map_reverse, List.sum_reverse,
            sum_zipIdx_mul q real.radix (fun D => ir.evalE rd (ir.domainField d) D i) real.digits 0,
            hsum]
          push_cast at hsides ⊢
          linear_combination hsides
        · cases hmt
      · cases hmt
    · cases hrow
  · cases h

include hwf hI hL R hA in
/-- **The digits of the two-sided and digit lookups are below their bases** at the source
environment of the honest committed values, where every such lookup has its facts, its digits
generated as its digits (`DigitLookupFactsC`) or as the committed digits of a quotient
(`commLookupCB`). -/
theorem digitsBelow_srcEnvCC
    (hD : ∀ pid < ir.predicates.length, ∀ d rec N r,
      (ir.predicate pid).body = .mem d [rec] (.range N) (.lookup r) →
        (r.kind = .twoSided ∨ r.kind = .digits) →
          ir.DigitLookupFactsC G pid d rec N r ∨ ∃ m j, ir.commLookupCB G pid m j = true)
    (hshape : ∀ pid < ir.predicates.length, ∀ r, lookupOf? (ir.predicate pid).body = some r →
      (r.kind = .twoSided ∨ r.kind = .digits) →
        ∃ d rec N, (ir.predicate pid).body = .mem d [rec] (.range N) (.lookup r)) :
    DigitsBelow (ir.reader SE) := by
  intro pid hpid r hr hk u hu i hi
  obtain ⟨d, rec, N, hb⟩ := hshape pid hpid r hr hk
  rcases hD pid hpid d rec N r hb hk with hF | ⟨m, j, hc⟩
  · have hdig := digitsRead_srcEnvC hwf hI hL R hA π hb hF
    obtain ⟨hc, hsz, hf, -⟩ := hF.cells u hu
    rw [reader_srcEnvL_of_privCellB x _ _ c π hc hi]
    rcases List.mem_append.1 hu with hu | hu
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hu
      rw [genCommitted_lookupDigit x s hb hF hj]
      exact ⟨_, Nat.mod_lt _ (by have := hF.baseGt; omega), rfl⟩
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hu
      rw [genCommitted_lookupSecond x s hb hF hj]
      exact ⟨_, Nat.mod_lt _ (by have := hF.baseGt; omega), rfl⟩
  · obtain ⟨d', rec', N', r', q, e, e', real, hb', hbm, hF⟩ := commLookupFactsC_of_B hc
    rw [hb] at hb'
    simp only [PredBody.mem.injEq, List.cons.injEq, and_true, InSet.range.injEq,
      InRealization.lookup.injEq] at hb'
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hb'
    rw [hF.second, List.append_nil] at hu
    have hcell := (hF.cells u hu).1
    rw [reader_srcEnvL_of_privCellB x _ _ c π hcell hi]
    obtain ⟨k, hk', rfl⟩ := List.getElem_of_mem hu
    rw [genCommitted_commDigit x s hb hbm hF hk']
    exact ⟨_, Nat.mod_lt _ (by have := hF.baseGt; omega), rfl⟩

/-- **A committed-digits lookup's digits are committed cells**, from either form of a lookup's
facts. -/
theorem privCellB_of_lookupFactsC {pid d N : ℕ} {rec : Expr} {r : LookupRealization}
    (hb : (ir.predicate pid).body = .mem d [rec] (.range N) (.lookup r))
    (hF : ir.DigitLookupFactsC G pid d rec N r ∨ ∃ m j, ir.commLookupCB G pid m j = true)
    {u : ℕ} (hu : u ∈ r.digitValues ++ r.second) : ir.privCellB u = true := by
  rcases hF with hF | ⟨m, j, hc⟩
  · exact (hF.cells u hu).1
  · obtain ⟨d', rec', N', r', q, e, e', real, hb', -, hF⟩ := commLookupFactsC_of_B hc
    rw [hb] at hb'
    simp only [PredBody.mem.injEq, List.cons.injEq, and_true, InSet.range.injEq,
      InRealization.lookup.injEq] at hb'
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hb'
    rw [hF.second, List.append_nil] at hu
    exact (hF.cells u hu).1

end

end GordieHowe.RealizedProgram
