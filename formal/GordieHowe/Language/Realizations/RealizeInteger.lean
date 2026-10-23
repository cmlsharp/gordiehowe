-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.RealizationValid
public import GordieHowe.Language.RealizedProgram.WithPlan

@[expose] public section

/-!
# GordieHowe: the integer form of `mod_q`, realized

The lemmas that turn a `mod_0`'s field equation into its integer equality and back
(`GordieHowe.RealizedProgram.IntegerOk`):

* **What the realized program establishes about the values** (`GordieHowe.RealizedProgram.LeafFacts` at a reader):
  constants read as constants, node-typed values in their types, every field `equal` (the Boolean
  checks) and every direct `in`. The realized program gives them where every group's needles are in
  their tables; the honest program gives them outright.
* **The values' intervals** (`GordieHowe.RealizedProgram.ivlAt_sound`) and **casts**
  (`GordieHowe.RealizedProgram.ivlAt_cast`), one rule at a time: under the intervals' facts
  (`GordieHowe.RealizedProgram.IvlFacts`) and lawful integer readings (`Interp.Lawful`), every
  coordinate of a value with an interval its source justifies (`GordieHowe.RealizedProgram.ivlAt`)
  lies in it, and its integer reading casts to its value; so for justified intervals
  (`GordieHowe.RealizedProgram.LeafIvlsOk.sound`, `GordieHowe.RealizedProgram.LeafIvlsOk.cast`),
  `leafIvl` among them (`GordieHowe.RealizedProgram.leafIvl_justified`).
* **`mod_0`** (`GordieHowe.RealizedProgram.holdsWith_mod_of_fieldEq`): the field
  equation `e = e'` with the sides' integer readings in the exported intervals, whose span is below
  `p`, gives the integer equality (the difference is a multiple of `p` of absolute value below
  `p`); the integer equality gives the field equation (the readings cast to the values).
-/

namespace GordieHowe.RealizedProgram

open Export

/-! ## Casts between equal field identifiers -/

/-- **An element whose cast to an equal field identifier is idempotent is `0` or `1`.** -/
theorem eq_zero_or_one_of_castElt {I : Interp} {a b : ℕ} (h : a = b) {x : (I a).K}
    (hx : (castElt x : (I b).K) * castElt x = castElt x) : x = 0 ∨ x = 1 := by
  subst h
  simp only [castElt_self] at hx
  exact IsIdempotentElem.iff_eq_zero_or_one.1 hx

/-- **An element whose cast to an equal field identifier is a natural's cast is that cast.** -/
theorem eq_natCast_of_castElt {I : Interp} {a b : ℕ} (h : a = b) {x : (I a).K} {k : ℕ}
    (hx : (castElt x : (I b).K) = k) : x = k := by
  subst h
  simpa using hx

theorem castElt_decode' {I : Interp} {a b : ℕ} (h : a = b) (c : ℕ) :
    (castElt ((I a).decode c) : (I b).K) = (I b).decode c := by
  subst h
  simp

/-- **Twice an integer's absolute value below `p`**, as two bounds. -/
theorem two_abs_lt_iff {x p : ℤ} : 2 * |x| < p ↔ -p < 2 * x ∧ 2 * x < p := by
  rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> constructor <;> intro h' <;> omega

theorem eq_intCast_of_castElt {I : Interp} {a b : ℕ} (h : a = b) {x : (I a).K} {z : ℤ}
    (hx : (castElt x : (I b).K) = z) : x = z := by
  subst h
  simpa using hx

section

variable {ir : RealizedProgram} {I : Interp}

/-- **The fields follow the program's characteristics** under a registered interpretation. -/
theorem charP_field (hI : I.Registered ir) {f : ℕ} (hf : f < ir.fields.length) :
    CharP (I f).K (ir.field f).characteristic := by
  have h := ringChar.charP (I f).K
  rwa [hI.ringChar f hf, hI.characteristic f hf] at h

/-- **A domain's field is a field of the program**, for a well-formed program. -/
theorem domainField_lt (hwf : ir.WellFormed) {d : ℕ} (hd : d < ir.domains.length) :
    ir.domainField d < ir.fields.length := by
  have hm : ir.domain d ∈ ir.domains := by
    rw [domain, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hd]
    exact List.getElem_mem hd
  exact hwf.domains _ hm

/-- **A value's field is a field of the program**, for a well-formed program: its domain's, or the
field it names (`FieldOk`). -/
theorem valueField_lt (hwf : ir.WellFormed) {v : ℕ} (hv : v < ir.values.length) :
    ir.valueField v < ir.fields.length := by
  have h := hwf.fields v hv
  unfold FieldOk at h
  revert h
  cases hf : (ir.value v).field with
  | none =>
    intro _
    rw [ir.valueField_of_field_none hf]
    exact domainField_lt hwf (hwf.values v hv).1
  | some f =>
    intro h
    rw [ir.valueField_of_field_some h.2.1 hf]
    exact h.1

/-! ## What the realized program establishes about the values -/

/-- **The leaf facts at the reader `rd`** (see the module docstring): constants read as constants,
node-typed values in their types, every field `equal` holds, every direct and every digit `in`
holds. -/
structure LeafFacts (rd : ir.Valuation I) : Prop where
  /-- Constants read as constants. -/
  consts : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
    rd v i = (I (ir.valueField v)).decode (es.getD i 0)
  /-- Node-typed values lie in their types. -/
  types : ∀ v < ir.values.length, (ir.value v).typeSource = .node →
    ∀ i < (ir.value v).size, (I (ir.valueField v)).InType (ir.value v).type (rd v i)
  /-- Every field `equal` holds. -/
  equals : ∀ q < ir.predicates.length, (ir.predicate q).body.isEqual = true →
    ir.HoldsWith rd (ir.predicate q).body
  /-- Every direct `in` holds. -/
  directs : ∀ q < ir.predicates.length, ∀ d recs set r,
    (ir.predicate q).body = .mem d recs set (.lookup r) → r.kind = .direct →
      ir.HoldsWith rd (ir.predicate q).body
  /-- Every digit `in` holds. -/
  digits : ∀ q < ir.predicates.length, ∀ d recs set r,
    (ir.predicate q).body = .mem d recs set (.lookup r) → r.kind = .digits →
      ir.HoldsWith rd (ir.predicate q).body
  /-- Opaque values computed from arguments read their functions. -/
  opaques : ∀ v name args, (ir.value v).kind = .pub (.opaque name args) → args ≠ [] → ∀ i,
    ∃ xs, rd v i = (I (ir.valueField v)).decode (I.opaqueFn name xs i)

/-- **An opaque value computed from arguments reads its function** in an environment. -/
theorem reader_opaque (e : ir.Env I) {v : ℕ} {name : String} {args : List ℕ}
    (hk : (ir.value v).kind = .pub (.opaque name args)) (hne : args ≠ []) (i : ℕ) :
    ∃ xs, ir.reader e v i = (I (ir.valueField v)).decode (I.opaqueFn name xs i) :=
  ⟨args.map fun u j => (I (ir.valueField u)).toNat (ir.read e ir.values.length u j), by
    simp only [reader, fuel, read, hk, if_neg hne]⟩

/-- **A program satisfied in an environment has the leaf facts at its reader.** -/
theorem SatAt.leafFacts {e : ir.Env I} (h : ir.SatAt e) : ir.LeafFacts (ir.reader e) where
  consts v _ hk i := reader_of_constant e hk i
  types := h.types
  equals q hq _ := h.preds _ (predicate_mem hq)
  directs q hq _ _ _ _ _ _ := h.preds _ (predicate_mem hq)
  digits q hq _ _ _ _ _ _ := h.preds _ (predicate_mem hq)
  opaques _ _ _ hk hne i := reader_opaque e hk hne i

/-- **The shift facts at the reader `rd`**: every `in` realized by a direct, digit or two-sided
lookup holds. The intervals of bound values read them (`boundIvl`); they are established after the
leaf facts (a two-sided `in` holds under the leaf facts), so the intervals read nothing the leaf facts
need. -/
structure ShiftFacts (rd : ir.Valuation I) (sr : List (ℕ × ℕ) := []) : Prop where
  /-- Every direct, digit and two-sided `in` holds. -/
  lookups : ∀ q < ir.predicates.length, ∀ d recs set r,
    (ir.predicate q).body = .mem d recs set (.lookup r) →
      (r.kind = .direct ∨ r.kind = .digits ∨ r.kind = .twoSided) →
        ir.HoldsWith rd (ir.predicate q).body
  /-- **The value ranges** `sr`: every listed value's coordinates are casts of naturals below its
  bound (the declared statement bounds, which the verifier checks, and the ranges of opaque
  functions, a property of the interpretation). -/
  stmt : ∀ vN ∈ sr, ∀ i < (ir.value vN.1).size,
    ∃ n < vN.2, rd vN.1 i = ((n : ℕ) : (I (ir.valueField vN.1)).K)

/-- **The facts the values' intervals read at the reader `rd`** (`leafIvl`), for the values `S`:
constants read as constants and opaque values computed from arguments read their functions; every
value of `S` that is node-typed lies in its type, has its type predicate hold, has every direct,
digit and two-sided `in` on it or on it plus a constant hold, and has every root equation on it
hold, reading only values of `S`; the value ranges `sr`. The leaf and shift facts give them for
every value (`LeafFacts.ivlFacts`); an honest assignment gives them for the source values. -/
structure IvlFacts (rd : ir.Valuation I) (sr : List (ℕ × ℕ)) (S : ℕ → Prop) : Prop where
  /-- Constants read as constants. -/
  consts : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
    rd v i = (I (ir.valueField v)).decode (es.getD i 0)
  /-- Opaque values computed from arguments read their functions. -/
  opaques : ∀ v name args, (ir.value v).kind = .pub (.opaque name args) → args ≠ [] → ∀ i,
    ∃ xs, rd v i = (I (ir.valueField v)).decode (I.opaqueFn name xs i)
  /-- The node-typed values of `S` lie in their types. -/
  types : ∀ v < ir.values.length, S v → (ir.value v).typeSource = .node →
    ∀ i < (ir.value v).size, (I (ir.valueField v)).InType (ir.value v).type (rd v i)
  /-- The type predicates of the values of `S` hold. -/
  checks : ∀ v, S v → ∀ q < ir.predicates.length, (ir.value v).typeSource = .pred q →
    (ir.predicate q).body.isEqual = true → ir.HoldsWith rd (ir.predicate q).body
  /-- The direct, digit and two-sided `in`s on the values of `S`, or on them plus a value, hold. -/
  lookups : ∀ v, S v → ∀ q < ir.predicates.length, ∀ d rec set r,
    (ir.predicate q).body = .mem d [rec] set (.lookup r) →
      (r.kind = .direct ∨ r.kind = .digits ∨ r.kind = .twoSided) →
        (rec = .leaf v ∨ ∃ c, rec = .add (.leaf v) (.leaf c)) → ir.HoldsWith rd (ir.predicate q).body
  /-- The root equations on the values of `S` hold and read only values of `S`. -/
  roots : ∀ v, S v → ∀ q < ir.predicates.length, (ir.predicate q).body.isEqual = true →
    ir.rootEqB v (ir.predicate q) = true →
      ir.HoldsWith rd (ir.predicate q).body ∧ ∀ w ∈ ir.predNodes (ir.predicate q).body, S w
  /-- The value ranges `sr`. -/
  stmt : ∀ vN ∈ sr, ∀ i < (ir.value vN.1).size,
    ∃ n < vN.2, rd vN.1 i = ((n : ℕ) : (I (ir.valueField vN.1)).K)

/-- **The leaf and shift facts give the intervals' facts** for every value. -/
theorem LeafFacts.ivlFacts {rd : ir.Valuation I} (hF : ir.LeafFacts rd) {sr : List (ℕ × ℕ)}
    (hK : ir.ShiftFacts rd sr) : ir.IvlFacts rd sr fun _ => True where
  consts := hF.consts
  opaques := hF.opaques
  types v hv _ := hF.types v hv
  checks _ _ q hq _ he := hF.equals q hq he
  lookups _ _ q hq d rec set r hb hk _ := hK.lookups q hq d [rec] set r hb hk
  roots _ _ q hq he _ := ⟨hF.equals q hq he, fun _ _ => trivial⟩
  stmt := hK.stmt

/-- **A prime-subfield read of type `Bit` is `0` or `1`** under the leaf facts: stored at a node, or
by its Boolean check (`boolCheckOk`). -/
theorem bit_of_primeRead_of {primeNodes : ℕ → List String} {rd : ir.Valuation I} {v : ℕ}
    (ht : (ir.value v).typeSource = .node →
      ∀ i < (ir.value v).size, (I (ir.valueField v)).InType (ir.value v).type (rd v i))
    (hc : ∀ q < ir.predicates.length, (ir.value v).typeSource = .pred q →
      (ir.predicate q).body.isEqual = true → ir.HoldsWith rd (ir.predicate q).body)
    (hr : ir.primeRead primeNodes v = true) (hb : (ir.value v).type = .bit) {i : ℕ}
    (hi : i < (ir.value v).size) : rd v i = 0 ∨ rd v i = 1 := by
  unfold primeRead at hr
  rw [hb] at hr
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
  revert hr
  cases hts : (ir.value v).typeSource with
  | node =>
    intro _
    have := ht hts i hi
    rwa [hb] at this
  | pred q =>
    rintro ⟨-, hq⟩
    unfold boolCheckOk at hq
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
    obtain ⟨hql, hq⟩ := hq
    have heq := hc q hql hts
    revert hq heq
    rcases hbody : (ir.predicate q).body with ⟨d, L, R, t⟩ | _ | _ | _ <;> try simp
    rcases L with _ | _ | _ | _ | ⟨⟨a⟩ | _, ⟨b⟩ | _⟩ | _ <;> try simp
    rcases R with ⟨c⟩ | _ <;> try simp
    rintro rfl rfl rfl hd hH
    have := hH rfl i (by simpa [exprLen, Expr.len] using hi)
    simp only [evalWith, evalE, Expr.eval] at this
    exact eq_zero_or_one_of_castElt hd.symm this
  | none => simp

/-- **A prime-subfield read of type `Bit` is `0` or `1`** under the leaf facts
(`bit_of_primeRead_of`). -/
theorem bit_of_primeRead {primeNodes : ℕ → List String} {rd : ir.Valuation I}
    (hF : ir.LeafFacts rd) {v : ℕ} (hv : v < ir.values.length)
    (hr : ir.primeRead primeNodes v = true) (hb : (ir.value v).type = .bit) {i : ℕ}
    (hi : i < (ir.value v).size) : rd v i = 0 ∨ rd v i = 1 :=
  bit_of_primeRead_of (hF.types v hv) (fun q hq _ he => hF.equals q hq he) hr hb hi

/-- **A prime-subfield read casts to its value**: `Bit` values are `0` or `1`, and a value stored
at a prime-subfield node is the cast of its integer reading (`Interp.Lawful.natCast_toNat`). -/
theorem natCast_toNat_of_primeRead {primeNodes : ℕ → List String} (hwf : ir.WellFormed)
    (hL : I.Lawful ir primeNodes) {rd : ir.Valuation I} {sr : List (ℕ × ℕ)} {S : ℕ → Prop}
    (hF : ir.IvlFacts rd sr S) {v : ℕ} (hS : S v) (hv : v < ir.values.length) (hr : ir.primeRead primeNodes v = true)
    (hp1 : 1 < ir.charOf (ir.valueField v)) {i : ℕ} (hi : i < (ir.value v).size) :
    (((I (ir.valueField v)).toNat (rd v i) : ℕ) : (I (ir.valueField v)).K) = rd v i := by
  have hd : (ir.value v).domain < ir.domains.length := by
    unfold primeRead at hr
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
    exact hr.1
  have hf : ir.valueField v < ir.fields.length := valueField_lt hwf hv
  by_cases hb : (ir.value v).type = .bit
  · rcases bit_of_primeRead_of (hF.types v hv hS) (fun q hq ht he => hF.checks v hS q hq ht he)
      hr hb hi with h | h <;> rw [h]
    · rw [show (0 : (I (ir.valueField v)).K) = ((0 : ℕ) : (I (ir.valueField v)).K) by simp,
        hL.toNat_natCast _ hf 0 (lt_trans Nat.zero_lt_one hp1)]
    · rw [show (1 : (I (ir.valueField v)).K) = ((1 : ℕ) : (I (ir.valueField v)).K) by simp,
        hL.toNat_natCast _ hf 1 hp1]
  · unfold primeRead at hr
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
    obtain ⟨-, hr⟩ := hr
    revert hr hb
    cases hty : (ir.value v).type with
    | bit => intros; simp_all
    | field =>
      intro _ hE
      revert hE
      cases (ir.value v).typeSource <;> simp
    | sub E =>
      cases hts : (ir.value v).typeSource with
      | node =>
        intro _ hE
        simp only [decide_eq_true_eq] at hE
        have hmem := hF.types v hv hS hts i hi
        rw [hty] at hmem
        have hlaw := hL.natCast_toNat _ hd E hE
        rw [← ir.valueField_of_field_none (hwf.field_none_of_type hv (by rw [hty]; simp))] at hlaw
        exact hlaw _ hmem
      | pred _ => simp
      | none => simp

/-! ## The values' intervals -/

variable {primeNodes : ℕ → List String}

/-- **The `in` of predicate `q` bounds its value** (`rangeIvl`): under the intervals' facts, every
coordinate below its size is the cast of a natural in the interval, below the characteristic. -/
theorem rangeIvl_spec {rd : ir.Valuation I} {sr : List (ℕ × ℕ)} {S : ℕ → Prop}
    (hF : ir.IvlFacts rd sr S) {v q : ℕ} (hS : S v) {J : Ivl} (h : ir.rangeIvl v q = some J) :
    ∀ i < (ir.value v).size, ∃ n : ℕ, (n : ℤ) ∈ J ∧ n < ir.charOf (ir.valueField v) ∧
      rd v i = ((n : ℕ) : (I (ir.valueField v)).K) := by
  intro i hi
  unfold rangeIvl at h
  split_ifs at h with hpid
  obtain ⟨N, hqm, rfl⟩ := Option.map_eq_some_iff.1 h
  unfold rangeBoundOf at hqm
  split at hqm
  · rename_i d u N' r hbody
    split_ifs at hqm with hc
    cases hqm
    obtain ⟨rfl, hkd, hN0, hNp, hdf⟩ := hc
    have hH : ir.HoldsWith rd (ir.predicate q).body :=
      hF.lookups _ hS q hpid _ _ _ _ hbody (hkd.elim .inl fun h => .inr (.inl h)) (.inl rfl)
    rw [hbody] at hH
    obtain ⟨k, hk, hkv⟩ := hH i (by simpa [exprLen, Expr.len] using hi) _ (List.mem_singleton_self _)
    simp only [evalWith, evalE, Expr.eval] at hkv
    refine ⟨k, ⟨by simp, by simp only; omega⟩, by omega, eq_natCast_of_castElt hdf.symm hkv⟩
  · cases hqm

/-- **The interval of the `in` of predicate `q` is sound** (`shiftIvl`): under the intervals'
facts, every coordinate below its size is the cast of an integer in the interval, of absolute value
below `p/2`: the `in` `v + c ∈ [0, N)` (or `v ∈ [0, N)`) holds, so `v = k − c₀` for a natural
`k < N`. -/
theorem shiftIvl_spec (hI : I.Registered ir) (hL : I.Lawful ir primeNodes) {rd : ir.Valuation I}
    {sr : List (ℕ × ℕ)} {S : ℕ → Prop} (hF : ir.IvlFacts rd sr S) {v q : ℕ} (hS : S v) {J : Ivl}
    (hf : ir.valueField v < ir.fields.length) (h : ir.shiftIvl v q = some J) :
    ∀ i < (ir.value v).size, ∃ z : ℤ, z ∈ J ∧ 2 * |z| < ir.charOf (ir.valueField v) ∧
      rd v i = ((z : ℤ) : (I (ir.valueField v)).K) := by
  intro i hi
  have hchar := charP_field hI hf
  unfold shiftIvl at h
  split_ifs at h with hpid
  split at h
  · rename_i cN hqm
    obtain ⟨c₀, N⟩ := cN
    unfold centredIvl at h
    split_ifs at h with hc
    cases h
    obtain ⟨hlo, hhi⟩ := hc
    simp only at hlo hhi
    unfold shiftRangeOf at hqm
    split at hqm
    · rename_i d rec N' r hbody
      split_ifs at hqm with hcond
      obtain ⟨hN0, hNp, hdf, hk⟩ := hcond
      split at hqm
      · rename_i u
        split_ifs at hqm with hu
        cases hqm
        have hu' : v = u := hu.symm
        subst hu'
        have hH := hF.lookups _ hS q hpid _ _ _ _ hbody hk (.inl rfl)
        rw [hbody] at hH
        obtain ⟨k, hkN, hkv⟩ := hH i (by simpa [exprLen, Expr.len] using hi) _
          (List.mem_singleton_self _)
        simp only [evalWith, evalE, Expr.eval] at hkv
        refine ⟨k, ?_, ?_, ?_⟩
        · rw [Ivl.mem_def]
          constructor <;> simp <;> omega
        · rw [two_abs_lt_iff] at hhi ⊢
          constructor <;> omega
        · rw [eq_natCast_of_castElt hdf.symm hkv, Int.cast_natCast]
      · rename_i u c
        split_ifs at hqm with hu
        obtain ⟨k₀, hk₀, hqm⟩ := Option.map_eq_some_iff.1 hqm
        cases hqm
        have hu' : v = u := hu.symm
        subst hu'
        have hH := hF.lookups _ hS q hpid _ _ _ _ hbody hk (.inr ⟨c, rfl⟩)
        rw [hbody] at hH
        unfold constEntry at hk₀
        split at hk₀
        · rename_i k es hck
          split_ifs at hk₀ with hca
          cases hk₀
          obtain ⟨hall, hkp⟩ := hca
          obtain ⟨k, hkN, hkv⟩ := hH i (by simpa [exprLen, Expr.len] using hi) _
            (List.mem_singleton_self _)
          unfold constAll at hall
          rw [hck] at hall
          simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at hall
          obtain ⟨⟨hn, hes⟩, hcf⟩ := hall
          have hci : rd c i = (I (ir.valueField c)).decode k₀ := by
            rw [hF.consts c _ hck i, List.getD_eq_getElem _ _ (by omega)]
            congr 1
            exact hes _ (List.getElem_mem _)
          simp only [evalWith, evalE, Expr.eval] at hkv
          have hcK : (castElt (rd c i) : (I (ir.domainField d)).K) =
              ((centeredZ (ir.charOf (ir.valueField v)) k₀ : ℤ) : (I (ir.domainField d)).K) := by
            rw [hci, castElt_decode' (hcf.trans hdf.symm), hdf,
              hL.decode_natCast _ hf k₀ (by simpa [charOf, hcf] using hkp), centeredZ_cast]
          set z : ℤ := (k : ℤ) - centeredZ (ir.charOf (ir.valueField v)) k₀
          refine ⟨z, ?_, ?_, ?_⟩
          · rw [Ivl.mem_def]
            constructor <;> simp only [z] <;> omega
          · rw [two_abs_lt_iff] at hlo hhi ⊢
            simp only [z]
            constructor <;> omega
          · have hrd : (castElt (rd v i) : (I (ir.domainField d)).K) =
                ((k : ℤ) : (I (ir.domainField d)).K) -
                  ((centeredZ (ir.charOf (ir.valueField v)) k₀ : ℤ) : (I (ir.domainField d)).K) := by
              rw [Int.cast_natCast, ← hcK, ← hkv]
              ring
            exact eq_intCast_of_castElt hdf.symm (by rw [hrd]; push_cast [z]; ring)
        · cases hk₀
      · cases hqm
    · cases hqm
  · cases h

/-- **A value that is neither a constant nor bound is read by its integer reading.** -/
theorem intOf_of_ne_constant (rd : ir.Valuation I) {v : ℕ}
    (h : ∀ es, (ir.value v).kind = .constant es → False) (i : ℕ)
    (hb : ∀ x, (ir.value v).kind = .bound x → False := by intro x hx; simp_all only [reduceCtorEq]) :
    ir.intOf rd v i = ((I (ir.valueField v)).toNat (rd v i) : ℤ) := by
  unfold intOf
  split
  · exact absurd ‹_› (h _)
  · exact absurd ‹_› (hb _)
  · rfl

/-- **A bound value is read centred.** -/
theorem intOf_of_bound (rd : ir.Valuation I) {v : ℕ} {x : Expr}
    (h : (ir.value v).kind = .bound x) (i : ℕ) :
    ir.intOf rd v i = (I (ir.valueField v)).centered ((I (ir.valueField v)).toNat (rd v i)) := by
  simp only [intOf, h]

/-- **The centred reading of the cast of a small integer is the integer**: `|z| < p/2`. -/
theorem centered_toNat_intCast (hI : I.Registered ir) (hL : I.Lawful ir primeNodes) {f : ℕ}
    (hf : f < ir.fields.length) {z : ℤ} (hz : 2 * |z| < ir.charOf f) :
    (I f).centered ((I f).toNat ((z : ℤ) : (I f).K)) = z := by
  have hchar := charP_field hI hf
  rw [FieldInterp.centered_eq, hI.characteristic _ hf]
  rcases le_or_gt 0 z with h0 | h0
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h0
    rw [abs_of_nonneg h0] at hz
    have hn : n < ir.charOf f := by omega
    rw [Int.cast_natCast, hL.toNat_natCast _ hf n hn]
    unfold centeredZ
    rw [if_pos (by simp only [charOf] at hz ⊢; omega)]
  · rw [abs_of_neg h0] at hz
    set m : ℕ := (((ir.charOf f : ℕ) : ℤ) + z).toNat with hm
    have hm' : ((m : ℕ) : ℤ) = ((ir.charOf f : ℕ) : ℤ) + z := by
      rw [hm, Int.toNat_of_nonneg (by omega)]
    have hcast : ((z : ℤ) : (I f).K) = ((m : ℕ) : (I f).K) := by
      rw [← Int.cast_natCast, hm', Int.cast_add, Int.cast_natCast, CharP.cast_eq_zero, zero_add]
    have hpe : (ir.field f).characteristic = ir.charOf f := rfl
    have hmlt : m < ir.charOf f := by have := hm'; omega
    rw [hcast, hL.toNat_natCast _ hf m hmlt]
    unfold centeredZ
    rw [if_neg (by have := hm'; omega)]
    omega

/-- **A constant is read by its centred entries.** -/
theorem intOf_of_constant (rd : ir.Valuation I) {v : ℕ} {es : List ℕ}
    (h : (ir.value v).kind = .constant es) (i : ℕ) :
    ir.intOf rd v i = (I (ir.valueField v)).centered (es.getD i 0) := by
  simp only [intOf, h]

/-- **An opaque value of type `Bit` computed from arguments is `0` or `1`** under the leaf facts and
lawful readings (`Interp.Lawful.opaqueBit`), read as the cast of a natural below `2`. -/
theorem opaque_bit (hL : I.Lawful ir primeNodes) {rd : ir.Valuation I} {sr : List (ℕ × ℕ)}
    {S : ℕ → Prop} (hF : ir.IvlFacts rd sr S) {v : ℕ} (hv : v < ir.values.length) {name : String} {a : ℕ} {args : List ℕ}
    (hk : (ir.value v).kind = .pub (.opaque name (a :: args))) (hb : (ir.value v).type = .bit)
    (i : ℕ) (hf : ir.valueField v < ir.fields.length) (h2 : 2 < ir.charOf (ir.valueField v)) :
    ∃ k : ℕ, k < 2 ∧ rd v i = (k : (I (ir.valueField v)).K) := by
  obtain ⟨xs, hxs⟩ := hF.opaques v name _ hk (List.cons_ne_nil _ _) i
  have hlt := hL.opaqueBit v hv name _ hk (List.cons_ne_nil _ _) hb xs i
  exact ⟨_, hlt, by rw [hxs, hL.decode_natCast _ hf _ (by simp only [charOf] at h2; omega)]⟩

/-- **The interval of a prime-subfield read is sound** (`primeIvl`): every coordinate below its
size is the cast of a natural in the interval, below the characteristic: a `Bit` value is `0` or
`1`, and any other prime-subfield read is the cast of its integer reading
(`natCast_toNat_of_primeRead`). -/
theorem primeIvl_spec (hwf : ir.WellFormed) (hL : I.Lawful ir primeNodes) {rd : ir.Valuation I}
    {sr : List (ℕ × ℕ)} {S : ℕ → Prop} (hF : ir.IvlFacts rd sr S) {v : ℕ} (hS : S v) {J : Ivl}
    (hv : v < ir.values.length) (hf : ir.valueField v < ir.fields.length)
    (hp2 : 2 < ir.charOf (ir.valueField v))
    (h : ir.primeIvl primeNodes (ir.valueField v) v = some J) :
    ∀ i < (ir.value v).size, ∃ n : ℕ, (n : ℤ) ∈ J ∧ n < ir.charOf (ir.valueField v) ∧
      rd v i = ((n : ℕ) : (I (ir.valueField v)).K) := by
  intro i hi
  have hp2' : 2 < (ir.field (ir.valueField v)).characteristic := hp2
  unfold primeIvl at h
  by_cases hpr : ir.primeRead primeNodes v = true
  swap
  · rw [if_neg hpr] at h
    cases h
  rw [if_pos hpr] at h
  cases h
  by_cases hb : (ir.value v).type = .bit
  · rw [if_pos hb]
    rcases bit_of_primeRead_of (hF.types v hv hS) (fun q hq ht he => hF.checks v hS q hq ht he)
      hpr hb hi with h0 | h0 <;> rw [h0]
    · exact ⟨0, by simp, by omega, by simp⟩
    · exact ⟨1, by simp, by omega, by simp⟩
  · rw [if_neg hb]
    have hlt := hL.toNat_lt _ hf hp2' (rd v i)
    refine ⟨(I (ir.valueField v)).toNat (rd v i), ⟨by simp, ?_⟩, hlt,
      (natCast_toNat_of_primeRead hwf hL hF hS hv hpr (by omega) hi).symm⟩
    simp only [charOf] at hlt ⊢
    omega

/-- **An entry of the value ranges bounds its value** (`declaredIvl`, `IvlFacts.stmt`): every
coordinate below its size is the cast of a natural in the interval, below the characteristic. -/
theorem declaredIvl_spec {rd : ir.Valuation I} {sr : List (ℕ × ℕ)} {S : ℕ → Prop}
    (hF : ir.IvlFacts rd sr S) {v k : ℕ} {J : Ivl}
    (h : ir.declaredIvl sr (ir.valueField v) v k = some J) :
    ∀ i < (ir.value v).size, ∃ n : ℕ, (n : ℤ) ∈ J ∧ n < ir.charOf (ir.valueField v) ∧
      rd v i = ((n : ℕ) : (I (ir.valueField v)).K) := by
  intro i hi
  unfold declaredIvl at h
  split at h
  · rename_i u N hk
    split_ifs at h with hc
    cases h
    obtain ⟨rfl, hN0, hNp⟩ := hc
    obtain ⟨n, hnN, hrd⟩ := hF.stmt (u, N) (List.mem_of_getElem? hk) i hi
    exact ⟨n, ⟨by simp, by simp only; omega⟩, by omega, hrd⟩
  · cases h

/-- **A natural's cast read in an equal field identifier is its cast there.** -/
theorem castElt_natCast {a b : ℕ} (h : a = b) (k : ℕ) :
    (castElt ((k : (I a).K)) : (I b).K) = k := by
  subst h
  simp

/-- **A constant holding `c` at its first `n` coordinates reads `c` below `n`**, cast into its
field, at a reader reading constants as constants (`hk`) and lawful integer readings. -/
theorem evalE_leaf_constAll_of (hL : I.Lawful ir primeNodes) {rd : ir.Valuation I}
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0))
    {u c n f : ℕ} (h : ir.constAll u c n f = true)
    (hf : f < ir.fields.length) (hc : c < ir.charOf f) {i : ℕ} (hi : i < n) :
    ir.evalE rd f (.leaf u) i = (c : (I f).K) := by
  unfold constAll at h
  split at h
  · rename_i es hk
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hn, hall⟩, hvf⟩ := h
    have hes : es.getD i 0 = c := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
      exact hall _ (List.getElem_mem _)
    change castElt (rd u i) = _
    rw [hK u es hk i, hes, hL.decode_natCast _ (hvf ▸ hf) c (hvf ▸ hc),
      castElt_natCast hvf]
  · cases h

/-- **A constant holding `c` at its first `n` coordinates reads `c` below `n`**, cast into its
field, under the leaf facts and lawful integer readings (`evalE_leaf_constAll_of`). -/
theorem evalE_leaf_constAll (hL : I.Lawful ir primeNodes) {rd : ir.Valuation I}
    (hF : ir.LeafFacts rd) {u c n f : ℕ} (h : ir.constAll u c n f = true)
    (hf : f < ir.fields.length) (hc : c < ir.charOf f) {i : ℕ} (hi : i < n) :
    ir.evalE rd f (.leaf u) i = (c : (I f).K) :=
  evalE_leaf_constAll_of hL hF.consts h hf hc hi

/-- **A constant expression reads its constant** (`constOf`) below `n`, at a reader reading
constants as constants. -/
theorem constOf_spec (hL : I.Lawful ir primeNodes) {rd : ir.Valuation I} {sr : List (ℕ × ℕ)}
    {S : ℕ → Prop} (hF : ir.IvlFacts rd sr S) {n f c : ℕ} {C : Expr} (h : ir.constOf n f C = some c) (hf : f < ir.fields.length) :
    c < ir.charOf f ∧ ∀ i < n, ir.evalE rd f C i = (c : (I f).K) := by
  have hentry : ∀ {u m : ℕ}, ir.constEntry u m f = some c →
      c < ir.charOf f ∧ ∀ i < m, ir.evalE rd f (.leaf u) i = (c : (I f).K) := by
    intro u m hu
    unfold constEntry at hu
    split at hu
    · split_ifs at hu with hc
      cases hu
      exact ⟨hc.2, fun i hi => evalE_leaf_constAll_of hL hF.consts hc.1 hf hc.2 hi⟩
    · cases hu
  match C, h with
  | .leaf u, h => exact hentry h
  | .reindex idx (.leaf u), h =>
    simp only [constOf] at h
    split_ifs at h with hall
    obtain ⟨hc, hr⟩ := hentry h
    refine ⟨hc, fun i hi => ?_⟩
    have := List.all_eq_true.1 hall i (List.mem_range.2 hi)
    exact hr _ (of_decide_eq_true this)

/-- **The quadratic root equation of predicate `q` bounds its root** (`quadRootIvl`): under the
intervals' facts, every coordinate of `v` is the cast of a natural in the interval, below the
characteristic. -/
theorem quadRootIvl_spec (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
    {rd : ir.Valuation I} {sr : List (ℕ × ℕ)} {S : ℕ → Prop} (hF : ir.IvlFacts rd sr S)
    {v : ℕ} (hS : S v) {J : Ivl} (hf : ir.valueField v < ir.fields.length) {q r : ℕ}
    (h : ir.quadRootIvl v q r = some J) :
    ∀ i < (ir.value v).size, ∃ n : ℕ, (n : ℤ) ∈ J ∧ n < ir.charOf (ir.valueField v) ∧
      rd v i = ((n : ℕ) : (I (ir.valueField v)).K) := by
  intro i hi
  have hchar := charP_field hI hf
  unfold quadRootIvl at h
  split_ifs at h with hpid
  split at h
  · rename_i mo co hview
    split at h
    · rename_i J' hJ'
      unfold quadIvl at h
      split_ifs at h with hJc
      cases h
      have hsome : ir.rootEqB v (ir.predicate q) = true := by rw [rootEqB, hview]; rfl
      unfold quadRootView at hview
      split at hview
      · rename_i d lhs z kind hbody
        split at hview
        · rename_i m a v₁ m₂ a₂ a₃ v₂ C
          split_ifs at hview with hc
          obtain ⟨c, hC, hmc⟩ := Option.map_eq_some_iff.1 hview
          simp only [Prod.mk.injEq] at hmc
          obtain ⟨rfl, rfl⟩ := hmc
          obtain ⟨rfl, rfl, rfl, ha, rfl, rfl, hdf, hmf, hzf, hlen, hz⟩ := hc
          obtain ⟨hc, hCv⟩ := constOf_spec hL hF hC hf
          -- the equation
          obtain ⟨hH, hnodes⟩ := hF.roots _ hS q hpid (by rw [hbody]; rfl) hsome
          have hSm : S m₂ := hnodes m₂ (by
            rw [hbody]
            simp [predNodes, PredBody.exprs, exprNodes, closure, Expr.directNodes])
          rw [hbody] at hH
          have hE := hH i (lt_of_lt_of_le hi hlen)
          -- m's coordinate
          have him : i < (ir.value m₂).size :=
            lt_of_lt_of_le hi (by simpa [exprLen, Expr.len] using hlen)
          obtain ⟨zm, hzm, -, hrdm⟩ := shiftIvl_spec hI hL hF hSm (hmf ▸ hf) hJ' i him
          obtain ⟨k, rfl⟩ : ∃ k : ℕ, zm = k := ⟨zm.toNat, by
            have := hzm.1; rw [hJc.1] at this; omega⟩
          have hkc : k ≤ c := by have := hzm.2; have := hJc.2; omega
          simp only [evalWith, evalE, Expr.eval] at hE
          have hfd : ir.domainField d < ir.fields.length := hdf ▸ hf
          have hcharD := charP_field hI hfd
          have hpD : ir.charOf (ir.domainField d) = ir.charOf (ir.valueField v₂) := by rw [hdf]
          -- the constant `a = p − 1` reads `−1`
          have ha1 : Coef.eval ir (ir.domainField d) rd (Coef.const a₃) = -1 := by
            change (I (ir.domainField d)).decode a₃ = -1
            rw [hL.decode_natCast _ hfd a₃ (by simp only [charOf] at ha hpD ⊢; omega)]
            have : ((a₃ + 1 : ℕ) : (I (ir.domainField d)).K) = 0 := by
              rw [CharP.cast_eq_zero_iff _ (ir.field (ir.domainField d)).characteristic]
              simp only [charOf] at ha hpD
              rw [ha, ← hpD]
            push_cast at this
            linear_combination this
          -- `C` reads `c`
          rw [← hdf] at hCv
          have hCi := hCv i hi
          simp only [evalE] at hCi
          -- `z` reads `0`
          have hz0 : (castElt (rd z i) : (I (ir.domainField d)).K) = 0 := by
            unfold zeroConstB at hz
            split at hz
            · rename_i es hk
              rw [hF.consts z es hk i]
              have h0 : es.getD i 0 = 0 := by
                rw [List.getD_eq_getElem?_getD]
                cases hes : es[i]? with
                | none => rfl
                | some c' =>
                  have := List.all_eq_true.1 hz c' (List.mem_of_getElem? hes)
                  simpa using this
              rw [h0, hL.decode_natCast _ (hzf ▸ hf) 0 (by
                rw [hzf]; simp only [charOf] at hc; omega), Nat.cast_zero, castElt_zero]
            · cases hz
          have hm : (castElt (rd m₂ i) : (I (ir.domainField d)).K) = k := by
            rw [hrdm, Int.cast_natCast, castElt_natCast (hmf.trans hdf.symm)]
          rw [ha1, hCi, hz0, hm] at hE
          have hroot : (castElt (rd v₂ i) : (I (ir.domainField d)).K) = k ∨
              (castElt (rd v₂ i) : (I (ir.domainField d)).K) =
                ((c - k : ℕ) : (I (ir.domainField d)).K) := by
            rw [Nat.cast_sub hkc]
            rcases mul_eq_zero.1 hE with h1 | h1
            · left; linear_combination -h1
            · right; linear_combination h1
          have hback : ∀ n : ℕ, (castElt (rd v₂ i) : (I (ir.domainField d)).K) = n →
              rd v₂ i = ((n : ℕ) : (I (ir.valueField v₂)).K) := fun n hn => by
            rw [← castElt_castElt_of_eq hdf.symm (rd v₂ i), hn, castElt_natCast hdf]
          rcases hroot with h1 | h1
          · exact ⟨k, ⟨by simp, by simpa using hkc⟩, by omega, hback k h1⟩
          · exact ⟨c - k, ⟨by simp, by push_cast [hkc]; omega⟩, by omega, hback _ h1⟩
        · cases hview
      · cases hview
    · cases h
  · cases h

/-- **A chain of `reindex`es over a leaf reads the leaf** at its index map (`leafViewAt`). -/
theorem leafViewAt_spec {f : ℕ} {rd : ir.Valuation I} :
    ∀ (fuel level : ℕ) (e : Expr) {u : ℕ} {g : ℕ → ℕ}, ir.leafViewAt fuel level e = some (u, g) →
      ∀ (rl : ℕ → ℕ) (i : ℕ), Expr.eval ir f rd (ir.refVal rd level f) rl e i = castElt (rd u (g i)) := by
  intro fuel
  induction fuel with
  | zero =>
    intro level e u g h rl i
    cases e <;> simp only [leafViewAt, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Expr.eval, id]
  | succ fuel ih =>
    intro level e u g h rl i
    cases e with
    | leaf w =>
      simp only [leafViewAt, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Expr.eval, id]
    | reindex idx e =>
      simp only [leafViewAt, Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨⟨u', g'⟩, h', rfl, rfl⟩ := h
      simp only [Expr.eval]
      exact ih level e h' rl (idx.entry i)
    | ref k =>
      cases level with
      | zero => simp [leafViewAt] at h
      | succ level =>
        simp only [leafViewAt] at h
        simp only [Expr.eval, refVal]
        exact ih level _ h _ i
    | _ => simp [leafViewAt] at h

/-- **A constant expression reads its entries** (`constReadAt`), below the characteristic, at a
reader reading constants as constants and lawful integer readings. -/
theorem constReadAt_spec (hL : I.Lawful ir primeNodes) {rd : ir.Valuation I}
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0))
    {f fuel level : ℕ} {C : Expr} {cv : ℕ → ℕ} (hf : f < ir.fields.length)
    (h : ir.constReadAt f fuel level C = some cv) (rl : ℕ → ℕ) {i : ℕ} (hc : cv i < ir.charOf f) :
    Expr.eval ir f rd (ir.refVal rd level f) rl C i = (cv i : (I f).K) := by
  unfold constReadAt at h
  split at h
  · rename_i c gc hv
    split at h
    · rename_i es hk
      split_ifs at h with hcf
      cases h
      rw [leafViewAt_spec fuel level C hv rl i, hK c es hk,
        hL.decode_natCast _ (hcf ▸ hf) _ (by rw [hcf]; exact hc), castElt_natCast hcf]
    · cases h
  · cases h

/-- `(p − c) mod p` is `−c` in a field of characteristic `p`, for `c < p`. -/
theorem natCast_sub_mod_eq_neg {K : Type} [Field K] {p : ℕ} [CharP K p] {c : ℕ} (hc : c < p) :
    (((p - c) % p : ℕ) : K) = -(c : K) := by
  rcases Nat.eq_zero_or_pos c with rfl | hc0
  · simp
  · rw [Nat.mod_eq_of_lt (by omega), Nat.cast_sub hc.le, CharP.cast_eq_zero, zero_sub]

/-- **A factor's constant part reads minus its roots** (`factorRoots`): coordinate `i < L` of `C`
is `−ρ i`, at a reader reading constants as constants and lawful integer readings. -/
theorem factorRoots_spec (hL : I.Lawful ir primeNodes) {rd : ir.Valuation I}
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0))
    {f fuel level L : ℕ} (hf : f < ir.fields.length) (hchar : CharP (I f).K (ir.charOf f))
    {C : Expr} {ρ : ℕ → ℕ} (h : ir.factorRoots f fuel level L C = some ρ) (rl : ℕ → ℕ) {i : ℕ}
    (hi : i < L) : Expr.eval ir f rd (ir.refVal rd level f) rl C i = -(ρ i : (I f).K) := by
  unfold factorRoots at h
  split at h
  · rename_i a C'
    split at h
    · rename_i cv hC
      split_ifs at h with hc
      cases h
      obtain ⟨ha, hcv⟩ := hc
      simp only [Expr.eval]
      rw [constReadAt_spec hL hK hf hC rl (hcv i hi)]
      have ha1 : Coef.eval ir f rd (Coef.const a) = -1 := by
        change (I f).decode a = -1
        rw [hL.decode_natCast _ hf a (by simp only [charOf] at ha; omega)]
        have : ((a + 1 : ℕ) : (I f).K) = 0 := by
          rw [ha]; exact CharP.cast_eq_zero _ _
        push_cast at this
        linear_combination this
      rw [ha1]
      ring
    · cases h
  · split at h
    · rename_i cv hC
      split_ifs at h with hcv
      cases h
      rw [constReadAt_spec hL hK hf hC rl (hcv i hi), natCast_sub_mod_eq_neg (hcv i hi), neg_neg]
    · cases h

/-- **A root product vanishes only at its roots** (`rootsAt`): where coordinate `i < L` of the
product is `0`, the coordinate `g i` of its value is one of the roots `r i`, at a reader reading
constants as constants and lawful integer readings. -/
theorem rootsAt_spec (hL : I.Lawful ir primeNodes) {rd : ir.Valuation I}
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0))
    {f : ℕ} (hf : f < ir.fields.length) (hchar : CharP (I f).K (ir.charOf f)) :
    ∀ (fuel level L : ℕ) (e : Expr) {u : ℕ} {g : ℕ → ℕ} {r : ℕ → List ℕ},
      ir.rootsAt f fuel level L e = some (u, g, r) → ∀ (rl : ℕ → ℕ) (i : ℕ), i < L →
      Expr.eval ir f rd (ir.refVal rd level f) rl e i = 0 →
      ∃ ρ ∈ r i, (castElt (rd u (g i)) : (I f).K) = (ρ : (I f).K) := by
  intro fuel
  induction fuel with
  | zero => intro level L e u g r h; simp [rootsAt] at h
  | succ fuel ih =>
    intro level L e u g r h rl i hi he
    cases e with
    | mul a b =>
      simp only [rootsAt] at h
      cases h₁ : rootsAt ir f fuel level L a with
      | none => rw [h₁] at h; cases h
      | some x₁ =>
        obtain ⟨u₁, g₁, r₁⟩ := x₁
        rw [h₁] at h
        cases h₂ : rootsAt ir f fuel level L b with
        | none => rw [h₂] at h; cases h
        | some x₂ =>
          obtain ⟨u₂, g₂, r₂⟩ := x₂
          rw [h₂] at h
          simp only at h
          split_ifs at h with hc
          obtain ⟨rfl, hg⟩ := hc
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          simp only [Expr.eval] at he
          rcases mul_eq_zero.1 he with h0 | h0
          · obtain ⟨ρ, hρ, hx⟩ := ih level L a h₁ rl i hi h0
            exact ⟨ρ, List.mem_append_left _ hρ, hx⟩
          · obtain ⟨ρ, hρ, hx⟩ := ih level L b h₂ rl i hi h0
            exact ⟨ρ, List.mem_append_right _ hρ, by rw [hg i hi]; exact hx⟩
    | ref k =>
      cases level with
      | zero => simp [rootsAt] at h
      | succ level =>
        simp only [rootsAt] at h
        simp only [Expr.eval, refVal] at he
        exact ih level L _ h _ i hi he
    | scale c a =>
      cases c with
      | node _ _ => cases fuel <;> simp [rootsAt, leafViewAt] at h
      | const s =>
        simp only [rootsAt] at h
        split_ifs at h with hs
        simp only [Expr.eval] at he
        have hs0 : Coef.eval ir f rd (Coef.const s) ≠ 0 := by
          change (I f).decode s ≠ 0
          rw [hL.decode_natCast _ hf s hs.2]
          rw [Ne, CharP.cast_eq_zero_iff (I f).K (ir.charOf f)]
          exact Nat.not_dvd_of_pos_of_lt hs.1 hs.2
        exact ih level L a h rl i hi ((mul_eq_zero.1 he).resolve_left hs0)
    | prod n a =>
      simp only [rootsAt] at h
      cases h₁ : rootsAt ir f fuel level (L * n) a with
      | none => rw [h₁] at h; cases h
      | some x₁ =>
        obtain ⟨u₁, g₁, r₁⟩ := x₁
        rw [h₁] at h
        simp only at h
        split_ifs at h with hg
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        simp only [Expr.eval] at he
        obtain ⟨t, ht, ht0⟩ := List.mem_map.1 (List.prod_eq_zero_iff.1 he)
        have htn := List.mem_range.1 ht
        have hin : i * n + t < L * n :=
          lt_of_lt_of_le (Nat.add_lt_add_left htn _)
            (by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hi)
        obtain ⟨ρ, hρ, hx⟩ := ih level (L * n) a h₁ rl _ hin ht0
        refine ⟨ρ, List.mem_flatMap.2 ⟨t, List.mem_range.2 htn, hρ⟩, ?_⟩
        show castElt (rd u₁ (g₁ (i * n))) = _
        rw [← hg i hi t htn]
        exact hx
    | add ex C =>
      simp only [rootsAt] at h
      cases hX : leafViewAt ir fuel level ex with
      | none => rw [hX] at h; cases h
      | some x₁ =>
        obtain ⟨u₁, g₁⟩ := x₁
        rw [hX] at h
        cases hC : factorRoots ir f fuel level L C with
        | none => rw [hC] at h; cases h
        | some ρ =>
          rw [hC] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          simp only [Expr.eval] at he
          rw [leafViewAt_spec fuel level ex hX rl i, factorRoots_spec hL hK hf hchar hC rl hi] at he
          exact ⟨ρ i, List.mem_singleton_self _, by linear_combination he⟩
    | _ =>
      simp only [rootsAt, Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨⟨u₁, g₁⟩, hX, rfl, rfl, rfl⟩ := h
      rw [leafViewAt_spec fuel level _ hX rl i] at he
      exact ⟨0, List.mem_singleton_self _, by rw [he, Nat.cast_zero]⟩

/-- **A root-set equation bounds the coordinates it reads** (`rootSetView`): under the leaf and
shift facts, every coordinate of `v` the equation reads is the cast of a natural in its interval,
below the characteristic. -/
theorem rootSetView_spec (hI : I.Registered ir) (hL : I.Lawful ir primeNodes) {rd : ir.Valuation I}
    {sr : List (ℕ × ℕ)} {S : ℕ → Prop} (hF : ir.IvlFacts rd sr S)
    {v : ℕ} (hS : S v) (hf : ir.valueField v < ir.fields.length) {pid : ℕ}
    (hpid : pid < ir.predicates.length) (hsome : ir.rootEqB v (ir.predicate pid) = true)
    {j : ℕ → ℕ} {L : ℕ} {J : Ivl} (hqm : ir.rootSetView v (ir.predicate pid) = some (j, L, J)) :
    ∀ i < L, ∃ n : ℕ, (n : ℤ) ∈ J ∧ n < ir.charOf (ir.valueField v) ∧
      rd v (j i) = ((n : ℕ) : (I (ir.valueField v)).K) := by
  intro i hi
  unfold rootSetView at hqm
  split at hqm
  · rename_i d lhs z kind hbody
    split_ifs at hqm with hpre
    simp only at hqm
    split at hqm
    · rename_i u j' r hR
      split_ifs at hqm with hc
      obtain ⟨hu, hdf, hzf, hroots⟩ := hc
      subst u
      simp only [Option.some.injEq, Prod.mk.injEq] at hqm
      obtain ⟨rfl, rfl, rfl⟩ := hqm
      obtain ⟨hH, -⟩ := hF.roots _ hS pid hpid (by rw [hbody]; rfl) hsome
      rw [hbody] at hH
      have hE := hH i hi
      have hfd : ir.domainField d < ir.fields.length := hdf ▸ hf
      have hcharD := charP_field hI hfd
      have hz0 : ir.evalWith rd d (.leaf z) i = 0 := by
        change (castElt (rd z i) : (I (ir.domainField d)).K) = 0
        have hz := hpre.2
        unfold zeroConstB at hz
        split at hz
        · rename_i es' hk'
          rw [hF.consts z es' hk' i]
          have h0 : es'.getD i 0 = 0 := by
            rw [List.getD_eq_getElem?_getD]
            cases hes' : es'[i]? with
            | none => rfl
            | some c' =>
              have := List.all_eq_true.1 hz c' (List.mem_of_getElem? hes')
              simpa using this
          have hpos : 0 < (ir.field (ir.valueField z)).characteristic := by
            rw [hzf]
            haveI := charP_field hI hf
            exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite (I (ir.valueField v)).K _)
          rw [h0, hL.decode_natCast _ (hzf ▸ hf) 0 hpos, Nat.cast_zero, castElt_zero]
        · cases hz
      rw [hz0] at hE
      obtain ⟨ρ, hρ, hx⟩ := rootsAt_spec hL hF.consts hfd hcharD _ _ _ _ hR _ i hi hE
      obtain ⟨hlo, hhi, hlt⟩ := hroots i hi ρ hρ
      refine ⟨ρ, ⟨by dsimp only; exact_mod_cast hlo, by dsimp only; exact_mod_cast hhi⟩, hlt, ?_⟩
      rw [← castElt_castElt_of_eq hdf.symm (rd v (j' i)), hx, castElt_natCast hdf]
    · cases hqm
  · cases hqm

/-- **The root-set equations of the predicates `qs` bound their value** (`rootSetIvlAt`): under the
intervals' facts, every coordinate of `v` is the cast of a natural in the interval, below the
characteristic: some listed equation reads it, in its interval, inside the hull. -/
theorem rootSetIvlAt_spec (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
    {rd : ir.Valuation I} {sr : List (ℕ × ℕ)} {S : ℕ → Prop} (hF : ir.IvlFacts rd sr S)
    {v : ℕ} (hS : S v) {J : Ivl} (hf : ir.valueField v < ir.fields.length) {qs : List ℕ}
    (h : ir.rootSetIvlAt v qs = some J) :
    ∀ i < (ir.value v).size, ∃ n : ℕ, (n : ℤ) ∈ J ∧ n < ir.charOf (ir.valueField v) ∧
      rd v i = ((n : ℕ) : (I (ir.valueField v)).K) := by
  intro i hi
  unfold rootSetIvlAt rootSetHull at h
  simp only at h
  split_ifs at h with hc
  cases h
  obtain ⟨hcov, hwin⟩ := hc
  obtain ⟨⟨j, L, J'⟩, hw, i', hi', hji⟩ := hcov i hi
  have hw' := hw
  unfold rootSetViews at hw'
  obtain ⟨q, -, hqm⟩ := List.mem_filterMap.1 hw'
  split_ifs at hqm with hpid
  have hsome : ir.rootEqB v (ir.predicate q) = true := by rw [rootEqB, hqm]; simp
  obtain ⟨n, hn, hnp, hrd⟩ := rootSetView_spec hI hL hF hS hf hpid hsome hqm i' hi'
  obtain ⟨hlo, hhi⟩ := hwin _ hw
  dsimp only at hji hlo hhi
  subst hji
  exact ⟨n, ⟨le_trans hlo hn.1, le_trans hn.2 hhi⟩, hnp, hrd⟩

/-- **A rule reading the value's integer reading bounds it** (`ruleIvl`, every source but a
constant's entries and an `in` read centred): under the intervals' facts, every coordinate of `v` is
the cast of a natural in the interval, below the characteristic. -/
theorem ruleIvl_nat (hwf : ir.WellFormed) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
    {rd : ir.Valuation I} {sr : List (ℕ × ℕ)} {S : ℕ → Prop} (hF : ir.IvlFacts rd sr S)
    {v : ℕ} (hS : S v) {s : IvlSource} {J : Ivl} (hv : v < ir.values.length)
    (hf : ir.valueField v < ir.fields.length) (hp2 : 2 < ir.charOf (ir.valueField v))
    (ha : s.allows (ir.value v).kind = true) (hc : s ≠ .const) (hb : ∀ q, s ≠ .shiftRange q)
    (h : ir.ruleIvl primeNodes sr (ir.valueField v) v s = some J) :
    ∀ i < (ir.value v).size, ∃ n : ℕ, (n : ℤ) ∈ J ∧ n < ir.charOf (ir.valueField v) ∧
      rd v i = ((n : ℕ) : (I (ir.valueField v)).K) := by
  cases s with
  | const => exact absurd rfl hc
  | opaqueBit =>
    obtain ⟨name, a, args, hk⟩ := IvlSource.allows_opaqueBit ha
    simp only [ruleIvl] at h
    split_ifs at h with hbit
    cases h
    intro i hi
    obtain ⟨k, hk2, hrd⟩ := opaque_bit hL hF hv hk hbit i hf hp2
    exact ⟨k, ⟨by simp, by simp only; omega⟩, by omega, hrd⟩
  | declared k => exact declaredIvl_spec hF h
  | shiftRange q => exact absurd rfl (hb q)
  | range q => exact rangeIvl_spec hF hS h
  | quadRoot q r => exact quadRootIvl_spec hI hL hF hS hf h
  | rootSet qs => exact rootSetIvlAt_spec hI hL hF hS hf h
  | prime => exact primeIvl_spec hwf hL hF hS hv hf hp2 h

/-- **A value with a justified interval is a value of the program and of the field, of
characteristic above `2`** (`ivlAt`). -/
theorem ivlAt_field {sr : List (ℕ × ℕ)} {f v : ℕ} {s : IvlSource} {J : Ivl}
    (h : ir.ivlAt primeNodes sr f v s = some J) :
    v < ir.values.length ∧ ir.valueField v = f ∧ f < ir.fields.length ∧ 2 < ir.charOf f := by
  unfold ivlAt at h
  split_ifs at h with hc
  exact ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1⟩

/-- **The justified intervals are sound** (`ivlAt`), under the intervals' facts: every coordinate
below its size of a value with an interval lies in it. -/
theorem ivlAt_sound (hwf : ir.WellFormed) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
    {rd : ir.Valuation I} {sr : List (ℕ × ℕ)} {S : ℕ → Prop} (hF : ir.IvlFacts rd sr S)
    {f v : ℕ} (hS : S v) {s : IvlSource} {J : Ivl} (h : ir.ivlAt primeNodes sr f v s = some J) :
    ∀ i < (ir.value v).size, ir.intOf rd v i ∈ J := by
  obtain ⟨hv, hvf, hf, hp2⟩ := ivlAt_field h
  subst hvf
  intro i hi
  have hp2' : 2 < (ir.field (ir.valueField v)).characteristic := hp2
  unfold ivlAt at h
  split_ifs at h with hg
  have ha := hg.2.2.2.2
  by_cases hc : s = .const
  · subst hc
    obtain ⟨es, hk⟩ := IvlSource.allows_const ha
    simp only [ruleIvl, hk] at h
    split_ifs at h with hall
    cases h
    rw [intOf_of_constant rd hk, FieldInterp.centered_eq, hI.characteristic _ hf]
    exact mem_constIvlOf (by omega) es hi
  by_cases hb : ∃ q, s = .shiftRange q
  · obtain ⟨q, rfl⟩ := hb
    obtain ⟨x, hkb⟩ := IvlSource.allows_shiftRange ha
    obtain ⟨z, hzJ, hzp, hrd⟩ := shiftIvl_spec hI hL hF hS hf h i hi
    rw [intOf_of_bound rd hkb, hrd, centered_toNat_intCast hI hL hf hzp]
    exact hzJ
  push Not at hb
  obtain ⟨hne, hnb⟩ := IvlSource.allows_other ha hc hb
  obtain ⟨n, hnJ, hnp, hrd⟩ := ruleIvl_nat hwf hI hL hF hS hv hf hp2 ha hc hb h i hi
  rw [intOf_of_ne_constant rd hne i hnb, hrd, hL.toNat_natCast _ hf n (by simpa [charOf] using hnp)]
  exact hnJ

/-- **The justified intervals' integer readings cast to the values** (`ivlAt`), under the
intervals' facts. -/
theorem ivlAt_cast (hwf : ir.WellFormed) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
    {rd : ir.Valuation I} {sr : List (ℕ × ℕ)} {S : ℕ → Prop} (hF : ir.IvlFacts rd sr S)
    {f v : ℕ} (hS : S v) {s : IvlSource} {J : Ivl} (h : ir.ivlAt primeNodes sr f v s = some J) :
    ∀ i < (ir.value v).size, ((ir.intOf rd v i : ℤ) : (I f).K) = castElt (rd v i) := by
  obtain ⟨hv, hvf, hf, hp2⟩ := ivlAt_field h
  subst hvf
  intro i hi
  have hp2' : 2 < (ir.field (ir.valueField v)).characteristic := hp2
  have hchar := charP_field hI hf
  unfold ivlAt at h
  split_ifs at h with hg
  have ha := hg.2.2.2.2
  rw [castElt_self]
  by_cases hc : s = .const
  · subst hc
    obtain ⟨es, hk⟩ := IvlSource.allows_const ha
    simp only [ruleIvl, hk] at h
    split_ifs at h with hall
    rw [intOf_of_constant rd hk, FieldInterp.centered_eq, hI.characteristic _ hf, centeredZ_cast,
      hF.consts v es hk i, hL.decode_natCast _ hf _ ?_]
    rw [List.getD_eq_getElem?_getD]
    cases hes : es[i]? with
    | none => simp only [Option.getD_none]; omega
    | some c =>
      simp only [Option.getD_some]
      exact of_decide_eq_true (List.all_eq_true.1 hall c (List.mem_of_getElem? hes))
  by_cases hb : ∃ q, s = .shiftRange q
  · obtain ⟨q, rfl⟩ := hb
    obtain ⟨x, hkb⟩ := IvlSource.allows_shiftRange ha
    obtain ⟨z, -, hzp, hrd⟩ := shiftIvl_spec hI hL hF hS hf h i hi
    rw [intOf_of_bound rd hkb, hrd, centered_toNat_intCast hI hL hf hzp]
  push Not at hb
  obtain ⟨hne, hnb⟩ := IvlSource.allows_other ha hc hb
  obtain ⟨n, -, hnp, hrd⟩ := ruleIvl_nat hwf hI hL hF hS hv hf hp2 ha hc hb h i hi
  rw [intOf_of_ne_constant rd hne i hnb, hrd, hL.toNat_natCast _ hf n (by simpa [charOf] using hnp),
    Int.cast_natCast]

/-- **A value with a justified interval is a value of the field** (`LeafIvlsOk`). -/
theorem LeafIvlsOk.field {sr : List (ℕ × ℕ)} {L : ℕ → ℕ → Option Ivl}
    (hLok : ir.LeafIvlsOk primeNodes sr L) {f v : ℕ} {J : Ivl} (h : L f v = some J) :
    ir.valueField v = f := by
  obtain ⟨s, hs⟩ := hLok f v J h
  exact (ivlAt_field hs).2.1

/-- **Justified values' intervals are sound** (`LeafIvlsOk`, `ivlAt_sound`). -/
theorem LeafIvlsOk.sound (hwf : ir.WellFormed) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
    {sr : List (ℕ × ℕ)} {L : ℕ → ℕ → Option Ivl} (hLok : ir.LeafIvlsOk primeNodes sr L)
    {rd : ir.Valuation I} {S : ℕ → Prop} (hF : ir.IvlFacts rd sr S) {f v : ℕ} (hS : S v) {J : Ivl}
    (h : L f v = some J) : ∀ i < (ir.value v).size, ir.intOf rd v i ∈ J := by
  obtain ⟨s, hs⟩ := hLok f v J h
  exact ivlAt_sound hwf hI hL hF hS hs

/-- **Justified values' integer readings cast to the values** (`LeafIvlsOk`, `ivlAt_cast`). -/
theorem LeafIvlsOk.cast (hwf : ir.WellFormed) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
    {sr : List (ℕ × ℕ)} {L : ℕ → ℕ → Option Ivl} (hLok : ir.LeafIvlsOk primeNodes sr L)
    {rd : ir.Valuation I} {S : ℕ → Prop} (hF : ir.IvlFacts rd sr S) {f v : ℕ} (hS : S v) {J : Ivl}
    (h : L f v = some J) :
    ∀ i < (ir.value v).size, ((ir.intOf rd v i : ℤ) : (I f).K) = castElt (rd v i) := by
  obtain ⟨s, hs⟩ := hLok f v J h
  exact ivlAt_cast hwf hI hL hF hS hs

/-! ## `mod_0` -/

/-- **The data of a `mod_0`'s domain**: its field is a field of the program, of the program's
characteristic `p > 2`, the integer readings of `0` and `1` are `0` and `1`, and constants below `p`
decode to their casts. -/
theorem modData (hwf : ir.WellFormed) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
    {d : ℕ} (hd : d < ir.domains.length) (h2 : 2 < ir.charOf (ir.domainField d)) :
    (I (ir.domainField d)).spec.characteristic = ir.charOf (ir.domainField d) ∧
      CharP (I (ir.domainField d)).K (ir.charOf (ir.domainField d)) ∧
      ((I (ir.domainField d)).toNat 0 = 0 ∧ (I (ir.domainField d)).toNat 1 = 1) ∧
      ∀ c < ir.charOf (ir.domainField d),
        (I (ir.domainField d)).decode c = (c : (I (ir.domainField d)).K) := by
  have hf := domainField_lt hwf hd
  refine ⟨hI.characteristic _ hf, charP_field hI hf, ⟨?_, ?_⟩, hL.decode_natCast _ hf⟩
  · simpa using hL.toNat_natCast _ hf 0 (by simp only [charOf] at h2; omega)
  · simpa using hL.toNat_natCast _ hf 1 (by simp only [charOf] at h2; omega)

/-- **An expression with an interval within `[lo, hi]` is read within it and casts to its value**
(`exprIvl`, at `p > 2`): under the leaf facts, every coordinate of a well-formed expression of
domain `d`. -/
theorem exprIvl_within (hwf : ir.WellFormed) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
    {rd : ir.Valuation I} (hF : ir.LeafFacts rd) {sr : List (ℕ × ℕ)} (hK : ir.ShiftFacts rd sr)
    {L : ℕ → ℕ → Option Ivl} (hLok : ir.LeafIvlsOk primeNodes sr L) {d : ℕ}
    (hd : d < ir.domains.length) (h2 : 2 < ir.charOf (ir.domainField d)) {e : Expr}
    (he : ir.ExprOk (ir.domainField d) e) {lo hi : ℤ}
    (hw : IvlWithin (ir.exprIvl L (ir.domainField d) e) lo hi) {i : ℕ} (hie : i < ir.exprLen e) :
    (lo ≤ ir.evalIntWith rd d e i ∧ ir.evalIntWith rd d e i ≤ hi) ∧
      ((ir.evalIntWith rd d e i : ℤ) : (I (ir.domainField d)).K) = ir.evalWith rd d e i := by
  obtain ⟨hp, hchar, h01, hdec⟩ := modData hwf hI hL hd h2
  have htn := hL.toNat_natCast _ (domainField_lt hwf hd)
  unfold exprIvl at hw
  cases hJ : ir.ivlOf (ir.charOf (ir.domainField d)) (L (ir.domainField d)) e
  · rw [hJ] at hw
    exact hw.elim
  rename_i J
  rw [hJ] at hw
  exact ⟨Ivl.mem_of_within hw (evalIntWith_mem_ivlOf hwf.exprs hp h01 htn
      (fun v J hJ => hLok.sound hwf hI hL (hF.ivlFacts hK) trivial hJ) hchar
      (fun v J hJ => hLok.cast hwf hI hL (hF.ivlFacts hK) trivial hJ) hdec
      (fun v J hJ => hLok.field hJ) he.shape he.refs hJ i hie),
    evalIntWith_cast hwf.exprs hp hchar h01 htn hdec
      (fun v J hJ => hLok.cast hwf hI hL (hF.ivlFacts hK) trivial hJ)
      (fun v J hJ => hLok.sound hwf hI hL (hF.ivlFacts hK) trivial hJ)
      (fun v J hJ => hLok.field hJ) he.shape he.refs hJ i hie⟩

/-- **An expression with an interval from the values `S` within `[lo, hi]` is read within it and
casts to its value** (at `p > 2`): under the intervals' facts for `S` (`IvlFacts`), every coordinate
of a well-formed expression of domain `d` whose interval, from the justified intervals `L`
(`LeafIvlsOk`) of the values of `S` only, lies within `[lo, hi]`. -/
theorem exprIvl_within_of (hwf : ir.WellFormed) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
    {rd : ir.Valuation I} {sr : List (ℕ × ℕ)} {S : ℕ → Prop} [DecidablePred S]
    (hF : ir.IvlFacts rd sr S) {L : ℕ → ℕ → Option Ivl} (hLok : ir.LeafIvlsOk primeNodes sr L)
    {d : ℕ} (hd : d < ir.domains.length)
    (h2 : 2 < ir.charOf (ir.domainField d)) {e : Expr} (he : ir.ExprOk (ir.domainField d) e)
    {lo hi : ℤ} (hw : IvlWithin (ir.ivlOf (ir.charOf (ir.domainField d))
      (fun v => if S v then L (ir.domainField d) v else none) e) lo hi)
    {i : ℕ} (hie : i < ir.exprLen e) :
    (lo ≤ ir.evalIntWith rd d e i ∧ ir.evalIntWith rd d e i ≤ hi) ∧
      ((ir.evalIntWith rd d e i : ℤ) : (I (ir.domainField d)).K) = ir.evalWith rd d e i := by
  obtain ⟨hp, hchar, h01, hdec⟩ := modData hwf hI hL hd h2
  have htn := hL.toNat_natCast _ (domainField_lt hwf hd)
  have hleaf : ∀ v J, (if S v then L (ir.domainField d) v else none) =
      some J → S v ∧ L (ir.domainField d) v = some J := fun v J h => by
    split_ifs at h with hS
    · exact ⟨hS, h⟩
  cases hJ : ir.ivlOf (ir.charOf (ir.domainField d))
      (fun v => if S v then L (ir.domainField d) v else none) e
  · rw [hJ] at hw
    exact hw.elim
  rename_i J
  rw [hJ] at hw
  exact ⟨Ivl.mem_of_within hw (evalIntWith_mem_ivlOf hwf.exprs hp h01 htn
      (fun v J hJ => hLok.sound hwf hI hL hF (hleaf v J hJ).1 (hleaf v J hJ).2) hchar
      (fun v J hJ => hLok.cast hwf hI hL hF (hleaf v J hJ).1 (hleaf v J hJ).2) hdec
      (fun v J hJ => hLok.field (hleaf v J hJ).2) he.shape he.refs hJ i hie),
    evalIntWith_cast hwf.exprs hp hchar h01 htn hdec
      (fun v J hJ => hLok.cast hwf hI hL hF (hleaf v J hJ).1 (hleaf v J hJ).2)
      (fun v J hJ => hLok.sound hwf hI hL hF (hleaf v J hJ).1 (hleaf v J hJ).2)
      (fun v J hJ => hLok.field (hleaf v J hJ).2) he.shape he.refs hJ i hie⟩

/-- **The sides of a `mod_0` in their intervals, cast to their values** (`IntegerOk`): under the
leaf facts, every coordinate of the left side's integer reading lies within `[lhsLo, lhsHi]` and
casts to its value, and the right side's within `[rhsLo, rhsHi]`. -/
theorem integerOk_sides (hwf : ir.WellFormed) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
    {rd : ir.Valuation I} (hF : ir.LeafFacts rd) {sr : List (ℕ × ℕ)} (hK : ir.ShiftFacts rd sr)
    {L : ℕ → ℕ → Option Ivl} (hLok : ir.LeafIvlsOk primeNodes sr L) {d : ℕ} {e e' : Expr}
    {real : ModRealization} (hpo : ir.PredOk (.mod d 0 e e' real))
    (hok : ir.IntegerOk L d e e' real)
    {i : ℕ}
    (hi : i < ir.exprLen e) :
    (real.lhsLo ≤ ir.evalIntWith rd d e i ∧ ir.evalIntWith rd d e i ≤ real.lhsHi) ∧
      (real.rhsLo ≤ ir.evalIntWith rd d e' i ∧ ir.evalIntWith rd d e' i ≤ real.rhsHi) ∧
      ((ir.evalIntWith rd d e i : ℤ) : (I (ir.domainField d)).K) = ir.evalWith rd d e i ∧
      ((ir.evalIntWith rd d e' i : ℤ) : (I (ir.domainField d)).K) = ir.evalWith rd d e' i := by
  obtain ⟨hex, hlen⟩ := hpo
  have he := hex (d, e) (by simp [PredBody.exprs])
  have he' := hex (d, e') (by simp [PredBody.exprs])
  obtain ⟨ha, hca⟩ := exprIvl_within hwf hI hL hF hK hLok he.1 hok.char he.2 hok.lhs hi
  obtain ⟨hb, hcb⟩ := exprIvl_within hwf hI hL hF hK hLok he.1 hok.char he'.2 hok.rhs (hlen ▸ hi)
  exact ⟨ha, hb, hca, hcb⟩

/-- **A `mod_0` holds where its field equation does** (`IntegerOk`): under the leaf facts, the sides'
integer readings lie in the exported intervals and cast to the sides' values; their difference is
a multiple of `p` (the field equation) of absolute value at most the span, below `p`, so zero. -/
theorem holdsWith_mod_of_fieldEq (hwf : ir.WellFormed) (hI : I.Registered ir)
    (hL : I.Lawful ir primeNodes) {rd : ir.Valuation I} (hF : ir.LeafFacts rd)
    {sr : List (ℕ × ℕ)} (hK : ir.ShiftFacts rd sr) {L : ℕ → ℕ → Option Ivl}
    (hLok : ir.LeafIvlsOk primeNodes sr L) {d : ℕ} {e e' : Expr} {real : ModRealization}
    (hpo : ir.PredOk (.mod d 0 e e' real)) (hok : ir.IntegerOk L d e e' real)
    (h : ∀ i < ir.exprLen e, ir.evalWith rd d e i = ir.evalWith rd d e' i) :
    ir.HoldsWith rd (.mod d 0 e e' real) := by
  have hd := (hpo.1 (d, e) (by simp [PredBody.exprs])).1
  have hchar := (modData hwf hI hL hd hok.char).2.1
  intro i hi
  obtain ⟨ha, hb, hca, hcb⟩ := integerOk_sides hwf hI hL hF hK hLok hpo hok hi
  have hdvd : ((ir.charOf (ir.domainField d) : ℕ) : ℤ) ∣
      ir.evalIntWith rd d e i - ir.evalIntWith rd d e' i := by
    rw [← CharP.intCast_eq_zero_iff (I (ir.domainField d)).K, Int.cast_sub, hca, hcb, h i hi,
      sub_self]
  have hspan := hok.spanLt
  have habs : |ir.evalIntWith rd d e i - ir.evalIntWith rd d e' i| <
      ((ir.charOf (ir.domainField d) : ℕ) : ℤ) := by
    rw [abs_lt]
    constructor <;>
      linarith [le_max_left real.lhsHi real.rhsHi, le_max_right real.lhsHi real.rhsHi,
        min_le_left real.lhsLo real.rhsLo, min_le_right real.lhsLo real.rhsLo]
  rw [Nat.cast_zero, zero_dvd_iff]
  exact Int.eq_zero_of_abs_lt_dvd hdvd habs

end

end GordieHowe.RealizedProgram
