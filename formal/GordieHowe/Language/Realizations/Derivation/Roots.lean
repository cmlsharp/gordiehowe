-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.RealizeInteger

@[expose] public section

/-!
# GordieHowe: the interval sources of root equations and opaque bits, for derivations

The local rules behind the `src` steps `opaqueBit`, `quadRoot q r` and `rootSet qs` of a derivation
(`GordieHowe/Language/Realizations/Derivation.lean`), each stated over the predicates and premises
the step names, with no search and no global bundle of facts:

* **`opaqueBit`** (`opaqueBit_spec`): an opaque value of type `Bit` computed from arguments reads
  `0` or `1` (`Interp.Lawful.opaqueBit`).
* **`quadRoot q r`** (`quadView`, `quadSrcN`, `quadSrcN_spec`): predicate `q` is the field `equal`
  `(m + a v) · (m + a (a v + C)) = z` (`v` a root of the quadratic whose roots are `m` and `c − m`),
  and premise `r` gives `m` the interval `[0, M]` with `M ≤ c`: then `v ∈ [0, c]`. The equation
  holds because the realized program's field `equal`s do (`RealizedAt.equal`).
* **`rootSet qs`** (`rootSetViewsAt`, `rootSetSrc`, `rootSetSrc_spec`): the root-set equations of
  the listed predicates `qs` (`rootSetView`) cover every coordinate of `v`, and `v` lies in the hull
  of their roots. Any list covering the coordinates is valid; none needs to be complete.

The proofs are those of `quadRootOf_spec`, `rootSetView_spec` and `rootSetIvl_spec`
(`GordieHowe/Language/Realizations/RealizeInteger.lean`), with the equation and the bound of `m` as
hypotheses in place of the facts `IvlFacts` collects. Each conclusion is stated as the cast of a
natural (`∃ n, … ∧ rd v i = n`), which `Derivation.lean` turns into the step's `ivl` fact.
-/

namespace GordieHowe.RealizedProgram

open Export

section Defs

variable (ir : RealizedProgram)

/-- **The quadratic root equation on value `v`** in predicate `pr` (`quadRootOf`'s shape): the
value `m` and the constant `c` of the field `equal` `(m + a v) · (m + a (a v + C)) = z`, `a = p − 1`,
`z` a constant holding `0`, `C` a constant expression holding `c` (`constOf`). -/
def quadView (v : ℕ) (pr : Predicate) : Option (ℕ × ℕ) :=
  match pr.body with
  | .equal d lhs (.leaf z) _ =>
    match lhs with
    | .mul (.add (.leaf m) (.scale (.const a) (.leaf v₁)))
        (.add (.leaf m₂) (.scale (.const a₂) (.add (.scale (.const a₃) (.leaf v₂)) C))) =>
      if v₁ = v ∧ v₂ = v ∧ m₂ = m ∧ a + 1 = ir.charOf (ir.valueField v) ∧ a₂ = a ∧ a₃ = a ∧
          ir.domainField d = ir.valueField v ∧ ir.valueField m = ir.valueField v ∧
          ir.valueField z = ir.valueField v ∧ (ir.value v).size ≤ ir.exprLen lhs ∧
          ir.zeroConstB z = true then
        (ir.constOf (ir.value v).size (ir.valueField v) C).map fun c => (m, c)
      else none
    | _ => none
  | _ => none

/-- **The bound `c + 1` of value `v` from the quadratic root equation of predicate `q`**, its `m`
the value `m` with the interval `[lo, hi]`: `lo = 0` and `hi ≤ c`. -/
def quadSrcN (v q m : ℕ) (lo hi : ℤ) : Option ℕ :=
  if q < ir.predicates.length then
    match ir.quadView v (ir.predicate q) with
    | some (m', c) => if m' = m ∧ lo = 0 ∧ hi ≤ c then some (c + 1) else none
    | none => none
  else none

/-- **The root-set equations on value `v` of the listed predicates `qs`** (`rootSetView`). -/
def rootSetViewsAt (v : ℕ) (qs : List ℕ) : List ((ℕ → ℕ) × ℕ × Ivl) :=
  qs.filterMap fun q => if q < ir.predicates.length then ir.rootSetView v (ir.predicate q) else none

/-- **The interval of value `v` from the root-set equations of the listed predicates `qs`**: as
`rootSetIvl`, over the listed equations only (`rootSetViewsAt`). -/
def rootSetSrc (v : ℕ) (qs : List ℕ) : Option Ivl :=
  if (ir.value v).type = .bit then none else
  let ws := ir.rootSetViewsAt v qs
  let lo := (ws.map fun w => w.2.2.lo).foldl min ((ws.map fun w => w.2.2.lo).headD 0)
  let hi := (ws.map fun w => w.2.2.hi).foldl max ((ws.map fun w => w.2.2.hi).headD 0)
  if ws.isEmpty = false ∧ (∀ c < (ir.value v).size, ∃ w ∈ ws, ∃ i < w.2.1, w.1 i = c) ∧
      ∀ w ∈ ws, lo ≤ w.2.2.lo ∧ w.2.2.hi ≤ hi then
    some ⟨lo, hi⟩
  else none

end Defs

section Specs

variable {ir : RealizedProgram} {I : Interp} {primeNodes : ℕ → List String}

/-- **A constant expression reads its constant** (`constOf`) below `n`, at a reader reading
constants as constants (`constOf_spec` without the interval facts). -/
theorem constOf_spec_of (hL : I.Lawful ir primeNodes) {rd : ir.Valuation I}
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0))
    {n f c : ℕ} {C : Expr} (h : ir.constOf n f C = some c) (hf : f < ir.fields.length) :
    c < ir.charOf f ∧ ∀ i < n, ir.evalE rd f C i = (c : (I f).K) := by
  have hentry : ∀ {u m : ℕ}, ir.constEntry u m f = some c →
      c < ir.charOf f ∧ ∀ i < m, ir.evalE rd f (.leaf u) i = (c : (I f).K) := by
    intro u m hu
    unfold constEntry at hu
    split at hu
    · split_ifs at hu with hc
      cases hu
      exact ⟨hc.2, fun i hi => evalE_leaf_constAll_of hL hK hc.1 hf hc.2 hi⟩
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

/-- **A constant holding `0` reads `0`** below its length. -/
theorem zero_of_zeroConstB (hI : I.Registered ir) (hL : I.Lawful ir primeNodes) {rd : ir.Valuation I}
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0))
    {z : ℕ} (hz : ir.zeroConstB z = true) (hf : ir.valueField z < ir.fields.length) (i : ℕ) :
    rd z i = 0 := by
  unfold zeroConstB at hz
  split at hz
  · rename_i es hk
    rw [hK z es hk i]
    have h0 : es.getD i 0 = 0 := by
      rw [List.getD_eq_getElem?_getD]
      cases hes : es[i]? with
      | none => rfl
      | some c' =>
        have := List.all_eq_true.1 hz c' (List.mem_of_getElem? hes)
        simpa using this
    have hpos : 0 < (ir.field (ir.valueField z)).characteristic := by
      have := charP_field hI hf
      exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite (I (ir.valueField z)).K _)
    rw [h0, hL.decode_natCast _ hf 0 hpos, Nat.cast_zero]
  · cases hz

/-- **An opaque value of type `Bit` computed from arguments is `0` or `1`** in an environment
(`opaque_bit` without the interval facts). -/
theorem opaqueBit_spec (hL : I.Lawful ir primeNodes) (e : ir.Env I) {v : ℕ}
    (hv : v < ir.values.length) {name : String} {a : ℕ} {args : List ℕ}
    (hk : (ir.value v).kind = .pub (.opaque name (a :: args))) (hb : (ir.value v).type = .bit)
    (hf : ir.valueField v < ir.fields.length) (h2 : 2 < ir.charOf (ir.valueField v)) (i : ℕ) :
    ∃ k : ℕ, k < 2 ∧ ir.reader e v i = (k : (I (ir.valueField v)).K) := by
  obtain ⟨xs, hxs⟩ := reader_opaque e hk (List.cons_ne_nil _ _) i
  have hlt := hL.opaqueBit v hv name _ hk (List.cons_ne_nil _ _) hb xs i
  exact ⟨_, hlt, by rw [hxs, hL.decode_natCast _ hf _ (by simp only [charOf] at h2; omega)]⟩

/-- **The quadratic root equation bounds its root** (`quadSrcN`): where predicate `q`'s equation
holds and every coordinate of `m` is the cast of an integer in `[lo, hi]`, every coordinate of `v`
is the cast of a natural below `c + 1`, itself at most the characteristic. -/
theorem quadSrcN_spec (hI : I.Registered ir) (hL : I.Lawful ir primeNodes) {rd : ir.Valuation I}
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0))
    {v q m : ℕ} {lo hi : ℤ} {N : ℕ} (hf : ir.valueField v < ir.fields.length)
    (hE : ∀ q < ir.predicates.length, (ir.predicate q).body.isEqual = true →
      ir.HoldsWith rd (ir.predicate q).body)
    (hm : ∀ i < (ir.value m).size, ∃ z : ℤ, lo ≤ z ∧ z ≤ hi ∧
      rd m i = ((z : ℤ) : (I (ir.valueField m)).K))
    (h : ir.quadSrcN v q m lo hi = some N) :
    N ≤ ir.charOf (ir.valueField v) ∧ ∀ i < (ir.value v).size, ∃ n < N,
      rd v i = ((n : ℕ) : (I (ir.valueField v)).K) := by
  unfold quadSrcN at h
  split_ifs at h with hq
  split at h
  · rename_i m' c hview
    split_ifs at h with hmc
    cases h
    obtain ⟨rfl, rfl, hhi⟩ := hmc
    unfold quadView at hview
    split at hview
    · rename_i d lhs z kind hbody
      split at hview
      · rename_i m₁ a v₁ m₂ a₂ a₃ v₂ C
        split_ifs at hview with hc
        obtain ⟨rfl, rfl, rfl, ha, rfl, rfl, hdf, hmf, hzf, hlen, hz⟩ := hc
        obtain ⟨c', hC, hcc⟩ := Option.map_eq_some_iff.1 hview
        simp only [Prod.mk.injEq] at hcc
        obtain ⟨rfl, rfl⟩ := hcc
        obtain ⟨hc, hCv⟩ := constOf_spec_of hL hK hC hf
        refine ⟨by omega, fun i hi => ?_⟩
        have hH := hE q hq (by rw [hbody]; rfl)
        rw [hbody] at hH
        have hE' := hH i (lt_of_lt_of_le hi hlen)
        have him : i < (ir.value m₂).size :=
          lt_of_lt_of_le hi (by simpa [exprLen, Expr.len] using hlen)
        obtain ⟨zm, hzlo, hzhi, hrdm⟩ := hm i him
        obtain ⟨k, rfl⟩ : ∃ k : ℕ, zm = k := ⟨zm.toNat, by omega⟩
        have hkc : k ≤ c' := by omega
        simp only [evalWith, evalE, Expr.eval] at hE'
        have hfd : ir.domainField d < ir.fields.length := hdf ▸ hf
        have hcharD := charP_field hI hfd
        have hpD : ir.charOf (ir.domainField d) = ir.charOf (ir.valueField v₂) := by rw [hdf]
        have ha1 : Coef.eval ir (ir.domainField d) rd (Coef.const a₃) = -1 := by
          change (I (ir.domainField d)).decode a₃ = -1
          rw [hL.decode_natCast _ hfd a₃ (by simp only [charOf] at ha hpD ⊢; omega)]
          have : ((a₃ + 1 : ℕ) : (I (ir.domainField d)).K) = 0 := by
            rw [CharP.cast_eq_zero_iff _ (ir.field (ir.domainField d)).characteristic]
            simp only [charOf] at ha hpD
            rw [ha, ← hpD]
          push_cast at this
          linear_combination this
        rw [← hdf] at hCv
        have hCi := hCv i hi
        simp only [evalE] at hCi
        have hz0 : (castElt (rd z i) : (I (ir.domainField d)).K) = 0 := by
          rw [zero_of_zeroConstB hI hL hK hz (hzf ▸ hf) i, castElt_zero]
        have hmk : (castElt (rd m₂ i) : (I (ir.domainField d)).K) = k := by
          rw [hrdm, Int.cast_natCast, castElt_natCast (hmf.trans hdf.symm)]
        rw [ha1, hCi, hz0, hmk] at hE'
        have hroot : (castElt (rd v₂ i) : (I (ir.domainField d)).K) = k ∨
            (castElt (rd v₂ i) : (I (ir.domainField d)).K) = ((c' - k : ℕ) : (I (ir.domainField d)).K) := by
          rw [Nat.cast_sub hkc]
          rcases mul_eq_zero.1 hE' with h1 | h1
          · left; linear_combination -h1
          · right; linear_combination h1
        have hback : ∀ n : ℕ, (castElt (rd v₂ i) : (I (ir.domainField d)).K) = n →
            rd v₂ i = ((n : ℕ) : (I (ir.valueField v₂)).K) := fun n hn => by
          rw [← castElt_castElt_of_eq hdf.symm (rd v₂ i), hn, castElt_natCast hdf]
        rcases hroot with h1 | h1
        · exact ⟨k, by omega, hback k h1⟩
        · exact ⟨c' - k, by omega, hback _ h1⟩
      · cases hview
    · cases hview
  · cases h

/-- **A root-set equation bounds the coordinates it reads** (`rootSetView`): where its equation
holds, every coordinate of `v` it reads is the cast of a natural in its interval, below the
characteristic (`rootSetView_spec` without the interval facts). -/
theorem rootSetView_spec_of (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
    {rd : ir.Valuation I}
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0))
    {v : ℕ} (hf : ir.valueField v < ir.fields.length) {pr : Predicate}
    (hH : ir.HoldsWith rd pr.body)
    {j : ℕ → ℕ} {L : ℕ} {J : Ivl} (hqm : ir.rootSetView v pr = some (j, L, J)) :
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
      rw [hbody] at hH
      have hE := hH i hi
      have hfd : ir.domainField d < ir.fields.length := hdf ▸ hf
      have hcharD := charP_field hI hfd
      have hz0 : ir.evalWith rd d (.leaf z) i = 0 := by
        change (castElt (rd z i) : (I (ir.domainField d)).K) = 0
        rw [zero_of_zeroConstB hI hL hK hpre.2 (hzf ▸ hf) i, castElt_zero]
      rw [hz0] at hE
      obtain ⟨ρ, hρ, hx⟩ := rootsAt_spec hL hK hfd hcharD _ _ _ _ hR _ i hi hE
      obtain ⟨hlo, hhi, hlt⟩ := hroots i hi ρ hρ
      refine ⟨ρ, ⟨by dsimp only; exact_mod_cast hlo, by dsimp only; exact_mod_cast hhi⟩, hlt, ?_⟩
      rw [← castElt_castElt_of_eq hdf.symm (rd v (j' i)), hx, castElt_natCast hdf]
    · cases hqm
  · cases hqm

/-- **The listed root-set equations bound their value** (`rootSetSrc`): where the realized
program's field `equal`s hold, every coordinate of `v` is the cast of a natural in the interval,
below the characteristic. -/
theorem rootSetSrc_spec (hI : I.Registered ir) (hL : I.Lawful ir primeNodes) {rd : ir.Valuation I}
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0))
    (hE : ∀ q < ir.predicates.length, (ir.predicate q).body.isEqual = true →
      ir.HoldsWith rd (ir.predicate q).body)
    {v : ℕ} {qs : List ℕ} {J : Ivl} (hf : ir.valueField v < ir.fields.length)
    (h : ir.rootSetSrc v qs = some J) :
    ∀ i < (ir.value v).size, ∃ n : ℕ, (n : ℤ) ∈ J ∧ n < ir.charOf (ir.valueField v) ∧
      rd v i = ((n : ℕ) : (I (ir.valueField v)).K) := by
  intro i hi
  unfold rootSetSrc at h
  simp only at h
  split_ifs at h with hb hc
  cases h
  obtain ⟨-, hcov, hwin⟩ := hc
  obtain ⟨⟨j, L, J'⟩, hw, i', hi', hji⟩ := hcov i hi
  obtain ⟨q, -, hqm⟩ := List.mem_filterMap.1 hw
  split_ifs at hqm with hq
  have hEq : (ir.predicate q).body.isEqual = true := by
    unfold rootSetView at hqm
    split at hqm
    · rename_i d lhs z kind hbody
      rw [hbody]
      rfl
    · cases hqm
  obtain ⟨n, hn, hnp, hrd⟩ := rootSetView_spec_of hI hL hK hf (hE q hq hEq) hqm i' hi'
  obtain ⟨hlo, hhi⟩ := hwin _ hw
  dsimp only at hji hlo hhi
  subst hji
  exact ⟨n, ⟨le_trans hlo hn.1, le_trans hn.2 hhi⟩, hnp, hrd⟩

end Specs

end GordieHowe.RealizedProgram
