-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Derivation.Basic
public import GordieHowe.Language.Realizations.Derivation.Roots
public import GordieHoweNative.Language.Realizations.Derivation.Rules

@[expose] public section

/-!
# GordieHowe: derivations, the rules

Each rule's checker (`<rule>Fact`) and its soundness lemma (`<rule>Fact_sound`).

The definitions are in `GordieHoweNative/Language/Realizations/Derivation/Rules.lean`
(the compiled library `GordieHoweNative`); this module has their lemmas.
-/

namespace GordieHowe.RealizedProgram

open Export Range IOP

section Sound

variable {ir : RealizedProgram} {I : Interp} {primeNodes : ℕ → List String}

variable {ir : RealizedProgram} {I : Interp} {primeNodes : ℕ → List String}

/-- **An element of an equal field identifier read as a coordinate is that coordinate.** -/
theorem castElt_evalE_eq {a b : ℕ} (h : a = b) (rd : ir.Valuation I) (x : Expr) (i : ℕ) :
    (castElt (ir.evalE rd a x i) : (I b).K) = ir.evalE rd b x i := by
  subst h
  simp

/-- **A natural's cast equal to a coordinate stays equal in an equal field identifier.** -/
theorem natCast_evalE_of_eq {a b : ℕ} (h : a = b) {rd : ir.Valuation I} {x : Expr} {i n : ℕ}
    (hn : ((n : ℕ) : (I a).K) = ir.evalE rd a x i) : ((n : ℕ) : (I b).K) = ir.evalE rd b x i := by
  subst h
  exact hn

/-- **A plain value's integer reading is its natural.** -/
theorem intOf_of_plain (rd : ir.Valuation I) {v : ℕ} (h : isPlainKind (ir.value v).kind = true)
    (i : ℕ) : ir.intOf rd v i = ((I (ir.valueField v)).toNat (rd v i) : ℤ) := by
  unfold intOf
  split
  · rename_i es hk
    rw [hk] at h
    cases h
  · rename_i x hk
    rw [hk] at h
    cases h
  · rfl

/-- **A list lookup that succeeds names a member.** -/
theorem mem_of_lookup_eq_some {β : Type} :
    ∀ {l : List (ℕ × β)} {v : ℕ} {J : β}, l.lookup v = some J → (v, J) ∈ l
  | [], _, _, h => by cases h
  | (w, K) :: l, v, J, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i hw
      cases h
      rw [beq_iff_eq.1 hw]
      exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (mem_of_lookup_eq_some h)

/-- **A linear form that vanishes modulo `p` is `0`** in a ring of characteristic `p`. -/
theorem linZeroB_sound {K : Type*} [CommRing K] {p : ℕ} [CharP K p] (g : Expr → K)
    {x : ℤ × List (ℤ × Expr)} (h : linZeroB p x = true) :
    (x.1 : K) + (x.2.map fun t => (t.1 : K) * g t.2).sum = 0 := by
  unfold linZeroB at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨hc, ht⟩ := h
  rw [sum_eq_zero_of_groups g _ _ le_rfl fun t htm => ht t htm, add_zero]
  exact (CharP.intCast_eq_zero_iff K p _).2 (Int.dvd_of_emod_eq_zero hc)

/-- **`realizedFact_sound`**: the rule is sound: its fact holds where its premises do. -/
theorem realizedOf_sound {e : ir.Env I} (h : ir.RealizedAt e) {pr : Predicate}
    (hm : pr ∈ ir.predicates) {f : Fact} (hf : realizedOf pr.body = some f) :
    f.HoldsWith ir (ir.reader e) := by
  unfold realizedOf at hf
  split at hf
  · rename_i d a b t hb
    cases hf
    have := h.equal _ hm (by rw [hb]; rfl)
    rw [hb] at this
    exact this
  · rename_i d q a b r hb
    split_ifs at hf with hq
    cases hf
    subst hq
    exact h.integer _ hm d a b r hb
  · cases hf

/-- **`realizedFact_sound`**: the rule is sound. -/
theorem realizedFact_sound {e : ir.Env I} (h : ir.RealizedAt e) {p : ℕ} {f : Fact}
    (hf : ir.realizedFact p = some f) : f.HoldsWith ir (ir.reader e) := by
  unfold realizedFact at hf
  split_ifs at hf with hp
  exact realizedOf_sound h (predicate_mem hp) hf

/-- **`substFact_sound`**: the rule is sound: its fact holds where its premises do. -/
theorem substFact_sound (hwf : ir.WellFormed) {rd : ir.Valuation I} (hB : ir.BoundReads rd)
    {d : ℕ} {e₁ e₂ : Expr} {f : Fact} (hf : ir.substFact d e₁ e₂ = some f) : f.HoldsWith ir rd := by
  unfold substFact at hf
  split at hf
  · rename_i k
    split_ifs at hf with hk
    cases hf
    obtain rfl := Expr.eq_of_beq hk.2
    intro i _
    simp only [evalWith]
    rw [evalE_ref hwf.refsOrdered rd _ hk.1]
  · rename_i v
    split at hf
    · rename_i x hx
      split_ifs at hf with hc
      cases hf
      obtain ⟨hv, hb, hfd⟩ := hc
      obtain rfl := Expr.eq_of_beq hb
      intro i _
      simp only [evalWith, evalE_leaf]
      rw [hB v hv _ hx]
      exact castElt_evalE_eq hfd rd _ i
    · cases hf
  · cases hf

/-- **`linPrem_sum`**: a lemma of the derivation checker. -/
theorem linPrem_sum {rd : ir.Valuation I} {fs : List Fact} (hfs : ∀ f ∈ fs, f.HoldsWith ir rd)
    {d n : ℕ} : ∀ {cs : List (ℕ × ℤ)} {ts : List (ℤ × Expr)}, ir.linPrem fs d n cs = some ts →
      ∀ i < n, (ts.map fun t => (t.1 : (I (ir.domainField d)).K) *
        ir.evalE rd (ir.domainField d) t.2 i).sum = 0
  | [], ts, h, i, _ => by
    simp only [linPrem, Option.some.injEq] at h
    subst h
    simp
  | (k, c) :: cs, ts, h, i, hi => by
    simp only [linPrem] at h
    split at h
    · rename_i d' a b hk
      split_ifs at h with hc
      obtain ⟨ts', h', rfl⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨rfl, hn⟩ := hc
      have hab : ir.evalWith rd d' a i = ir.evalWith rd d' b i :=
        hfs _ (List.mem_of_getElem? hk) i (by omega)
      simp only [evalWith] at hab
      simp only [List.map_cons, List.sum_cons, linPrem_sum hfs h' i hi, hab]
      push_cast
      ring
    · cases h

section LinTerms

variable {rd : ir.Valuation I} (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
  rd v i = (I (ir.valueField v)).decode (es.getD i 0))

include hK in
/-- **`evalE_linTerms`**: a lemma of the derivation checker. -/
theorem evalE_linTerms (hL : I.Lawful ir primeNodes) {f n : ℕ} (hf : f < ir.fields.length) :
    ∀ {ts : List (ℤ × Expr)} {x : ℤ × List (ℤ × Expr)}, ir.linTerms f n ts = some x → ∀ i < n,
      (ts.map fun t => (t.1 : (I f).K) * ir.evalE rd f t.2 i).sum =
        (x.1 : (I f).K) + (x.2.map fun t => (t.1 : (I f).K) * ir.evalE rd f t.2 i).sum
  | [], x, h, i, _ => by
    simp only [linTerms, Option.some.injEq] at h
    subst h
    simp
  | (c, y) :: ts, x, h, i, hi => by
    simp only [linTerms, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    rw [List.map_cons, List.sum_cons, evalE_linForm hK hL hf y a ha i hi,
      evalE_linTerms hL hf hb i hi]
    simp only [List.map_append, List.sum_append]
    rw [linSum_scale (fun t => ir.evalE rd f t i)]
    push_cast
    ring

include hK in
/-- **`linearFact_sound`**: the rule is sound: its fact holds where its premises do. -/
theorem linearFact_sound (hwf : ir.WellFormed) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
    {fs : List Fact} (hfs : ∀ f ∈ fs, f.HoldsWith ir rd) {d : ℕ} {cs : List (ℕ × ℤ)}
    {e₁ e₂ : Expr} {f : Fact} (hf : ir.linearFact fs d cs e₁ e₂ = some f) : f.HoldsWith ir rd := by
  unfold linearFact at hf
  split_ifs at hf with hd
  split at hf
  · rename_i ts hts
    split at hf
    · rename_i x hx
      split_ifs at hf with hz
      cases hf
      have hfl := domainField_lt hwf hd
      have := charP_field hI hfl
      intro i hi
      have h1 := evalE_linTerms hK hL hfl hx i hi
      have h2 := linPrem_sum hfs hts i hi
      have h3 := linZeroB_sound (K := (I (ir.domainField d)).K) (p := ir.charOf (ir.domainField d))
        (fun t => ir.evalE rd (ir.domainField d) t i) hz
      rw [List.map_append, List.sum_append, h2] at h1
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h1
      simp only [evalWith]
      push_cast at h1
      linear_combination -h1 - h3
    · cases hf
  · cases hf

end LinTerms

/-- **Contiguous slices cover every coordinate below their end.** -/
theorem exists_of_sliceEnd : ∀ {ms : List Member} {pos q : ℕ}, sliceEnd ms pos = some q →
    ∀ i, pos ≤ i → i < q → ∃ m ∈ ms, m.first ≤ i ∧ i < m.first + m.count
  | [], pos, q, h, i, h1, h2 => by
    simp only [sliceEnd, Option.some.injEq] at h
    omega
  | m :: ms, pos, q, h, i, h1, h2 => by
    simp only [sliceEnd] at h
    split_ifs at h with hm
    by_cases hi : i < pos + m.count
    · exact ⟨m, List.mem_cons_self .., by omega, by omega⟩
    · obtain ⟨m', hm', h3⟩ := exists_of_sliceEnd h i (by omega) h2
      exact ⟨m', List.mem_cons_of_mem _ hm', h3⟩

/-- **`memberAt_mem`**: a lemma of the derivation checker. -/
theorem memberAt_mem {t g m : ℕ} (hm : m < (ir.members t g).length) :
    ir.memberAt t g m ∈ ir.members t g := by
  unfold memberAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm, Option.getD_some]
  exact List.getElem_mem hm

/-- **`lookupFact_holds`**: the rule's fact holds at any reader where every group's needles are
rows of its table. -/
theorem lookupFact_holds {rd : ir.Valuation I}
    (hin : ∀ t < ir.tables.length, ∀ g < ir.groupCountOf t, ir.NeedlesIn rd t g)
    {ms : List (ℕ × ℕ × ℕ)} {f : Fact} (hf : ir.lookupFact ms = some f) : f.HoldsWith ir rd := by
  unfold lookupFact at hf
  split at hf
  · cases hf
  rename_i t g m ms
  split_ifs at hf with hc
  obtain ⟨ht, hall⟩ := hc
  split at hf
  · rename_i q hq
    split_ifs at hf with hlen
    cases hf
    have hok : ∀ x ∈ (t, g, m) :: ms, x.1 = t ∧ x.2.1 < ir.groupCountOf t ∧
        x.2.2 < (ir.members t x.2.1).length ∧ ir.memberNeedle t x.2.1 x.2.2 = ir.memberNeedle t g m := by
      intro x hx
      have := List.all_eq_true.1 hall x hx
      simp only [memberRefB, Bool.and_eq_true, decide_eq_true_eq] at this
      exact ⟨this.1.1.1, this.1.1.2, this.1.2, Expr.eq_of_beq this.2⟩
    intro i hi
    obtain ⟨mb, hmb, h1, h2⟩ := exists_of_sliceEnd hq i (Nat.zero_le i) (by omega)
    obtain ⟨⟨xt, xg, xm⟩, hx, rfl⟩ := List.mem_map.1 hmb
    obtain ⟨hxt, hxg, hxm, hxn⟩ := hok _ hx
    dsimp only at hxt hxg hxm hxn h1 h2
    subst hxt
    have hn := mem_groupNeedles (rd := rd) (f := ir.chalField (ir.alphaOf xt))
      (memberAt_mem hxm) (c := i - (ir.memberAt xt xg xm).first) (by omega)
    rw [Nat.add_sub_cancel' h1] at hn
    have hne : ir.needleExpr (ir.memberAt xt xg xm).pred (ir.memberAt xt xg xm).needle =
        ir.memberNeedle xt g m := hxn
    rw [hne] at hn
    exact hin xt ht xg hxg _ hn
  · cases hf

/-- **`lookupFact_sound`**: the rule is sound: its fact holds where its premises do. -/
theorem lookupFact_sound (hI : I.Registered ir) (hT : ∀ t < ir.tables.length, ir.TableOk t)
    {e : ir.Env I} (he : Env.Sampled ir e) (h : ir.RealizedAt e) {ms : List (ℕ × ℕ × ℕ)}
    {f : Fact} (hf : ir.lookupFact ms = some f) :
    f.HoldsWith ir (ir.reader e) ∨ ∃ j, ir.RealEvent j e := by
  unfold lookupFact at hf
  split at hf
  · cases hf
  rename_i t g m ms
  split_ifs at hf with hc
  obtain ⟨ht, hall⟩ := hc
  split at hf
  · rename_i q hq
    split_ifs at hf with hlen
    cases hf
    have hok : ∀ x ∈ (t, g, m) :: ms, x.1 = t ∧ x.2.1 < ir.groupCountOf t ∧
        x.2.2 < (ir.members t x.2.1).length ∧ ir.memberNeedle t x.2.1 x.2.2 = ir.memberNeedle t g m := by
      intro x hx
      have := List.all_eq_true.1 hall x hx
      simp only [memberRefB, Bool.and_eq_true, decide_eq_true_eq] at this
      exact ⟨this.1.1.1, this.1.1.2, this.1.2, Expr.eq_of_beq this.2⟩
    by_cases hin : ∀ x ∈ (t, g, m) :: ms, ir.NeedlesIn (ir.reader e) t x.2.1
    · left
      intro i hi
      obtain ⟨mb, hmb, h1, h2⟩ := exists_of_sliceEnd hq i (Nat.zero_le i) (by omega)
      obtain ⟨⟨xt, xg, xm⟩, hx, rfl⟩ := List.mem_map.1 hmb
      obtain ⟨hxt, hxg, hxm, hxn⟩ := hok _ hx
      dsimp only at hxt hxg hxm hxn h1 h2
      subst hxt
      have hn := mem_groupNeedles (rd := ir.reader e) (f := ir.chalField (ir.alphaOf xt))
        (memberAt_mem hxm) (c := i - (ir.memberAt xt xg xm).first) (by omega)
      rw [Nat.add_sub_cancel' h1] at hn
      have hne : ir.needleExpr (ir.memberAt xt xg xm).pred (ir.memberAt xt xg xm).needle =
          ir.memberNeedle xt g m := hxn
      rw [hne] at hn
      exact hin _ hx _ hn
    · push Not at hin
      obtain ⟨x, hx, hn⟩ := hin
      obtain ⟨-, hxg, -, -⟩ := hok x hx
      rcases needlesIn_or_logupBad (hT t ht) hxg hI he (h.logup t ht _ hxg) with hin | hbad
      · exact absurd hin hn
      · exact Or.inr ⟨_, .inl ⟨t, ht, rfl, _, hxg, hbad⟩⟩
  · cases hf

/-- **`ivlMeetFact_sound`**: the rule is sound: its fact holds where its premises do. -/
theorem ivlMeetFact_sound {rd : ir.Valuation I} {fs : List Fact}
    (hfs : ∀ f ∈ fs, f.HoldsWith ir rd) {a b : ℕ} {f : Fact} (hf : ivlMeetFact fs a b = some f) :
    f.HoldsWith ir rd := by
  unfold ivlMeetFact at hf
  split at hf
  · rename_i d x lo hi d' x' lo' hi' ha hb
    split_ifs at hf with hc
    cases hf
    obtain ⟨rfl, hx⟩ := hc
    obtain rfl := Expr.eq_of_beq hx
    have h1 : Fact.HoldsWith ir rd (.ivl d' x' lo hi) := hfs _ (List.mem_of_getElem? ha)
    have h2 : Fact.HoldsWith ir rd (.ivl d' x' lo' hi') := hfs _ (List.mem_of_getElem? hb)
    intro i hi
    obtain ⟨a1, a2, a3⟩ := h1 i hi
    obtain ⟨b1, b2, -⟩ := h2 i hi
    exact ⟨max_le a1 b1, le_min a2 b2, a3⟩
  · cases hf

/-- **`natIvlFact_sound`**: the rule is sound: its fact holds where its premises do. -/
theorem natIvlFact_sound {rd : ir.Valuation I} {fs : List Fact}
    (hfs : ∀ f ∈ fs, f.HoldsWith ir rd) {k : ℕ} {f : Fact} (hf : natIvlFact fs k = some f) :
    f.HoldsWith ir rd := by
  unfold natIvlFact at hf
  split at hf
  · rename_i d x lo hi hk
    split_ifs at hf with h0
    cases hf
    have h1 : Fact.HoldsWith ir rd (.ivl d x lo hi) := hfs _ (List.mem_of_getElem? hk)
    intro i hi'
    obtain ⟨a1, a2, a3⟩ := h1 i hi'
    refine ⟨(ir.evalIntWith rd d x i).toNat, by omega, ?_⟩
    rw [← a3, ← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
  · cases hf

/-- **`rangeNatFact_sound`**: the rule is sound: its fact holds where its premises do. -/
theorem rangeNatFact_sound {rd : ir.Valuation I} {fs : List Fact}
    (hfs : ∀ f ∈ fs, f.HoldsWith ir rd) {d k : ℕ} {f : Fact} (hf : ir.rangeNatFact fs d k = some f) :
    f.HoldsWith ir rd := by
  unfold rangeNatFact at hf
  split at hf
  · rename_i t x hk
    split at hf
    · rename_i T hr
      split_ifs at hf with hfd
      cases hf
      have hx := hfs _ (List.mem_of_getElem? hk)
      intro i hi
      obtain ⟨j, hj⟩ := hx i hi
      rw [tableRow_of_isRange (isRange_of_rows hr)] at hj
      have hT : ir.tableSize t = T := by simp [tableSize, hr]
      exact ⟨j, by rw [← hT]; exact j.2, natCast_evalE_of_eq hfd hj⟩
    · cases hf
  · cases hf

/-- **`holdsInFact_sound`**: the rule is sound: its fact holds where its premises do. -/
theorem holdsInFact_sound {rd : ir.Valuation I} {fs : List Fact}
    (hfs : ∀ f ∈ fs, f.HoldsWith ir rd) {k : ℕ} {f : Fact} (hf : ir.holdsInFact fs k = some f) :
    f.HoldsWith ir rd := by
  unfold holdsInFact at hf
  split at hf
  · rename_i q hk
    split at hf
    · rename_i d x N r hb
      cases hf
      have hq : ir.HoldsWith rd (ir.predicate q).body := hfs _ (List.mem_of_getElem? hk)
      rw [hb] at hq
      intro i hi
      exact (inRows_range_iff rd d x i N).1 (hq i hi)
    · cases hf
  · cases hf

/-- **A plain leaf whose coordinates are casts of naturals below `N ≤ p` has the interval
`[0, N − 1]`.** -/
theorem ivl_of_natLeaf (hwf : ir.WellFormed) (hL : I.Lawful ir primeNodes) {rd : ir.Valuation I}
    {d v N : ℕ} (hd : d < ir.domains.length) (hfd : ir.valueField v = ir.domainField d)
    (hp : isPlainKind (ir.value v).kind = true) (hN : N ≤ ir.charOf (ir.domainField d))
    (h : ∀ i < (ir.value v).size, ∃ n < N, rd v i = ((n : ℕ) : (I (ir.valueField v)).K)) :
    Fact.HoldsWith ir rd (.ivl d (.leaf v) 0 ((N : ℤ) - 1)) := by
  intro i hi
  obtain ⟨n, hn, hv⟩ := h i hi
  have hvf : ir.valueField v < ir.fields.length := hfd ▸ domainField_lt hwf hd
  have hint : ir.evalIntWith rd d (.leaf v) i = n := by
    change ir.intOf rd v i = n
    rw [intOf_of_plain rd hp, hv, hL.toNat_natCast _ hvf n (by
      have : ir.charOf (ir.valueField v) = ir.charOf (ir.domainField d) := by rw [hfd]
      simp only [charOf] at this hN
      omega)]
  rw [hint]
  refine ⟨by omega, by omega, ?_⟩
  change ((n : ℤ) : (I (ir.domainField d)).K) = castElt (rd v i)
  rw [hv, castElt_natCast hfd, Int.cast_natCast]

/-- **A leaf reading naturals as themselves** (`natReadB`: plain, or bound with `2 N ≤ p`) **whose
coordinates are casts of naturals below `N ≤ p` has the interval `[0, N − 1]`.** -/
theorem ivl_of_natRead (hwf : ir.WellFormed) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
    {rd : ir.Valuation I} {d v N : ℕ} (hd : d < ir.domains.length)
    (hfd : ir.valueField v = ir.domainField d)
    (hp : natReadB (ir.value v).kind N (ir.charOf (ir.domainField d)) = true)
    (hN : N ≤ ir.charOf (ir.domainField d))
    (h : ∀ i < (ir.value v).size, ∃ n < N, rd v i = ((n : ℕ) : (I (ir.valueField v)).K)) :
    Fact.HoldsWith ir rd (.ivl d (.leaf v) 0 ((N : ℤ) - 1)) := by
  unfold natReadB at hp
  rcases Bool.or_eq_true_iff.1 hp with hpl | hb
  · exact ivl_of_natLeaf hwf hL hd hfd hpl hN h
  intro i hi
  obtain ⟨n, hn, hv⟩ := h i hi
  have hvf : ir.valueField v < ir.fields.length := hfd ▸ domainField_lt hwf hd
  have hc : ir.charOf (ir.valueField v) = ir.charOf (ir.domainField d) := by rw [hfd]
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨hbk, h2N⟩ := hb
  have hint : ir.evalIntWith rd d (.leaf v) i = n := by
    change ir.intOf rd v i = n
    cases hk : (ir.value v).kind with
    | bound x =>
      rw [intOf_of_bound rd hk, hv, hL.toNat_natCast _ hvf n (by
        simp only [charOf] at hc hN
        omega), FieldInterp.centered_eq, hI.characteristic _ hvf]
      unfold centeredZ
      rw [if_pos (by simp only [charOf] at hc hN h2N ⊢; omega)]
    | _ => rw [hk] at hbk; cases hbk
  rw [hint]
  refine ⟨by omega, by omega, ?_⟩
  change ((n : ℤ) : (I (ir.domainField d)).K) = castElt (rd v i)
  rw [hv, castElt_natCast hfd, Int.cast_natCast]

/-- **A plain leaf whose coordinates are casts of naturals in `[lo, hi]` below the characteristic
has the interval `[lo, hi]`.** -/
theorem ivl_of_natLeafIn (hwf : ir.WellFormed) (hL : I.Lawful ir primeNodes) {rd : ir.Valuation I}
    {d v : ℕ} {lo hi : ℤ} (hd : d < ir.domains.length) (hfd : ir.valueField v = ir.domainField d)
    (hp : isPlainKind (ir.value v).kind = true)
    (h : ∀ i < (ir.value v).size, ∃ n : ℕ, lo ≤ n ∧ (n : ℤ) ≤ hi ∧ n < ir.charOf (ir.domainField d) ∧
      rd v i = ((n : ℕ) : (I (ir.valueField v)).K)) :
    Fact.HoldsWith ir rd (.ivl d (.leaf v) lo hi) := by
  intro i hi'
  obtain ⟨n, hlo, hhi, hn, hv⟩ := h i hi'
  have hvf : ir.valueField v < ir.fields.length := hfd ▸ domainField_lt hwf hd
  have hint : ir.evalIntWith rd d (.leaf v) i = n := by
    change ir.intOf rd v i = n
    rw [intOf_of_plain rd hp, hv, hL.toNat_natCast _ hvf n (by
      have : ir.charOf (ir.valueField v) = ir.charOf (ir.domainField d) := by rw [hfd]
      simp only [charOf] at this hn
      omega)]
  rw [hint]
  refine ⟨hlo, hhi, ?_⟩
  change ((n : ℤ) : (I (ir.domainField d)).K) = castElt (rd v i)
  rw [hv, castElt_natCast hfd, Int.cast_natCast]

/-- **A constant entry reads its constant** below `n`, at a reader reading constants as
constants. -/
theorem constEntry_sound (hL : I.Lawful ir primeNodes) {rd : ir.Valuation I}
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0))
    {u n f c : ℕ} (h : ir.constEntry u n f = some c) (hf : f < ir.fields.length) :
    c < ir.charOf f ∧ ∀ i < n, ir.evalE rd f (.leaf u) i = (c : (I f).K) := by
  unfold constEntry at h
  split at h
  · split_ifs at h with hc
    cases h
    exact ⟨hc.2, fun i hi => evalE_leaf_constAll_of hL hK hc.1 hf hc.2 hi⟩
  · cases h


/-- **`srcFact_sound`**: the rule is sound: its fact holds where its premises do. -/
theorem srcFact_sound (hwf : ir.WellFormed) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
    {sr : List (ℕ × ℕ)} {e : ir.Env I} (h : ir.RealizedAt e)
    (hS : ∀ vN ∈ sr, ∀ i < (ir.value vN.1).size,
      ∃ n < vN.2, ir.reader e vN.1 i = ((n : ℕ) : (I (ir.valueField vN.1)).K))
    {fs : List Fact} (hfs : ∀ f ∈ fs, f.Holds e) {d v : ℕ} {s : IvlSrc} {f : Fact}
    (hg : ir.srcGuard d v = true) (hf : ir.srcFact primeNodes sr fs d v s = some f) :
    f.Holds e := by
  unfold srcGuard at hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨⟨hv, hd⟩, hfd⟩, hp2⟩ := hg
  have hf' := domainField_lt hwf hd
  have hchar := charP_field hI hf'
  cases s with
  | const =>
    simp only [srcFact] at hf
    split at hf
    · rename_i es hk
      split_ifs at hf with hall
      cases hf
      intro i hi
      change i < (ir.value v).size at hi
      have hc : es.getD i 0 < ir.charOf (ir.domainField d) := by
        rw [List.getD_eq_getElem?_getD]
        cases hes : es[i]? with
        | none => simp only [Option.getD_none]; omega
        | some c =>
          exact of_decide_eq_true (List.all_eq_true.1 ((allK_eq _ es).symm.trans hall) c
            (List.mem_of_getElem? hes))
      have hint : ir.evalIntWith (ir.reader e) d (.leaf v) i =
          centeredZ (ir.charOf (ir.domainField d)) (es.getD i 0) := by
        change ir.intOf (ir.reader e) v i = _
        rw [intOf_of_constant _ hk, FieldInterp.centered_eq, hI.characteristic _ (hfd ▸ hf'), hfd]
      have hmem := mem_constIvlOf (p := ir.charOf (ir.domainField d)) (n := (ir.value v).size)
        es hi
      rw [hint]
      refine ⟨hmem.1, hmem.2, ?_⟩
      change _ = castElt (ir.reader e v i)
      rw [reader_of_constant e hk, castElt_decode' hfd, hL.decode_natCast _ hf' _ hc,
        centeredZ_cast]
    · cases hf
  | declared k =>
    simp only [srcFact] at hf
    split at hf
    · rename_i w N hk
      split_ifs at hf with hc
      cases hf
      obtain ⟨rfl, hpl, -, hN⟩ := hc
      exact ivl_of_natRead hwf hI hL hd hfd hpl hN (hS _ (List.mem_of_getElem? hk))
    · cases hf
  | nat k =>
    simp only [srcFact] at hf
    split at hf
    · rename_i d' x N hk
      split_ifs at hf with hc
      cases hf
      obtain ⟨rfl, hx, hpl, -, hN⟩ := hc
      obtain rfl := Expr.eq_of_beq hx
      have hn : Fact.HoldsWith ir (ir.reader e) (.nat d' (.leaf v) N) := hfs _ (List.mem_of_getElem? hk)
      refine ivl_of_natRead hwf hI hL hd hfd hpl hN fun i hi => ?_
      obtain ⟨n, hnN, hn'⟩ := hn i hi
      exact ⟨n, hnN, (eq_natCast_of_castElt hfd hn'.symm)⟩
    · cases hf
  | prime =>
    simp only [srcFact] at hf
    split at hf
    · rename_i E hty hts
      split_ifs at hf with hc
      cases hf
      obtain ⟨hpl, hfn, hdd, hE⟩ := hc
      have hvf : ir.valueField v < ir.fields.length := hfd ▸ hf'
      have key : ∀ x ∈ (I (ir.valueField v)).node E,
          (((I (ir.valueField v)).toNat x : ℕ) : (I (ir.valueField v)).K) = x := by
        rw [ir.valueField_of_field_none hfn]
        exact hL.natCast_toNat _ hdd E hE
      refine ivl_of_natLeaf (N := ir.charOf (ir.domainField d)) hwf hL hd hfd hpl le_rfl
        fun i hi => ?_
      have hin := h.types v hv hts i hi
      rw [hty] at hin
      refine ⟨_, ?_, (key _ hin).symm⟩
      have := hL.toNat_lt _ hvf (by rw [hfd]; exact hp2) (ir.reader e v i)
      have hc : (ir.field (ir.valueField v)).characteristic = ir.charOf (ir.domainField d) := by
        rw [hfd]
      exact hc ▸ this
    · cases hf
  | opaqueBit =>
    simp only [srcFact] at hf
    split at hf
    · rename_i name a args hk
      split_ifs at hf with hb
      cases hf
      have hvf : ir.valueField v < ir.fields.length := hfd ▸ hf'
      have h2 : 2 < ir.charOf (ir.valueField v) := by rw [hfd]; exact hp2
      refine ivl_of_natLeaf hwf hL hd hfd (by rw [hk]; rfl) (by omega) fun i _ => ?_
      exact opaqueBit_spec hL e hv hk hb hvf h2 i
    · cases hf
  | shift k =>
    simp only [srcFact] at hf
    split at hf
    · rename_i d' w c N hk
      split at hf
      rotate_left
      · rename_i hnp
        split at hf
        rotate_left
        · cases hf
        rename_i hc'
        obtain ⟨rfl, rfl, hbd⟩ := hc'
        split at hf
        · rename_i c0 hce
          split_ifs at hf with hc2
          cases hf
          obtain ⟨hN0, hc'0, hcN⟩ := hc2
          rw [← abs_eq_max_neg] at hc'0 hcN
          have hn : Fact.HoldsWith ir (ir.reader e) (.nat d' (.add (.leaf w) (.leaf c)) N) :=
            hfs _ (List.mem_of_getElem? hk)
          have hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
              ir.reader e v i = (I (ir.valueField v)).decode (es.getD i 0) :=
            fun _ _ hk i => reader_of_constant e hk i
          have hvf : ir.valueField w < ir.fields.length := hfd ▸ hf'
          have hcf : ir.charOf (ir.valueField w) = ir.charOf (ir.domainField d') := by rw [hfd]
          intro i hi
          change i < (ir.value w).size at hi
          obtain ⟨kk, hkN, hkv⟩ := hn i hi
          set c' := centeredZ (ir.charOf (ir.domainField d')) c0
          have hcv := (constEntry_sound hL hK hce hf').2 i hi
          simp only [evalWith, evalE_add] at hkv
          rw [hcv] at hkv
          have hz : (((kk : ℤ) - c' : ℤ) : (I (ir.domainField d')).K) =
              castElt (ir.reader e w i) := by
            rw [Int.cast_sub, centeredZ_cast, Int.cast_natCast, hkv, evalE_leaf]
            ring
          have hrd : ir.reader e w i = (((kk : ℤ) - c' : ℤ) : (I (ir.valueField w)).K) :=
            eq_intCast_of_castElt hfd hz.symm
          have hkN' : (kk : ℤ) ≤ (N : ℤ) - 1 := by
            have : (kk : ℤ) < N := by exact_mod_cast hkN
            omega
          have hsmall : 2 * |(kk : ℤ) - c'| < (ir.charOf (ir.valueField w) : ℤ) := by
            rw [hcf]
            have h1 := hc'0
            have h2 := hcN
            rcases abs_cases ((kk : ℤ) - c') with ⟨ha, _⟩ | ⟨ha, _⟩ <;>
            rcases abs_cases c' with ⟨hb, _⟩ | ⟨hb, _⟩ <;>
            rcases abs_cases ((N : ℤ) - 1 - c') with ⟨hc, _⟩ | ⟨hc, _⟩ <;>
            · rw [ha]
              rw [hb] at h1
              rw [hc] at h2
              omega
          have hint : ir.evalIntWith (ir.reader e) d' (.leaf w) i = (kk : ℤ) - c' := by
            change ir.intOf (ir.reader e) w i = _
            obtain ⟨x, hkx⟩ : ∃ x, (ir.value w).kind = .bound x := by
              cases hk' : (ir.value w).kind <;> rw [hk'] at hbd <;>
                first | exact ⟨_, rfl⟩ | cases hbd
            rw [intOf_of_bound _ hkx, hrd, centered_toNat_intCast hI hL hvf hsmall]
          rw [hint]
          refine ⟨by omega, by omega, hz⟩
        · cases hf
      rename_i hc
      obtain ⟨rfl, rfl, hpl⟩ := hc
      split at hf
      · rename_i c0 hce
        split_ifs at hf with hc2
        cases hf
        obtain ⟨hc'0, hcN⟩ := hc2
        have hn : Fact.HoldsWith ir (ir.reader e) (.nat d' (.add (.leaf w) (.leaf c)) N) :=
          hfs _ (List.mem_of_getElem? hk)
        have hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
            ir.reader e v i = (I (ir.valueField v)).decode (es.getD i 0) :=
          fun _ _ hk i => reader_of_constant e hk i
        intro i hi
        change i < (ir.value w).size at hi
        obtain ⟨kk, hkN, hkv⟩ := hn i hi
        set c' := centeredZ (ir.charOf (ir.domainField d')) c0
        have hcv := (constEntry_sound hL hK hce hf').2 i hi
        simp only [evalWith, evalE_add] at hkv
        rw [hcv] at hkv
        set m := ((kk : ℤ) - c').toNat with hm
        have hm' : (m : ℤ) = kk - c' := Int.toNat_of_nonneg (by omega)
        have hval : (castElt (ir.reader e w i) : (I (ir.domainField d')).K) = (m : (I (ir.domainField d')).K) := by
          have : ((m : ℤ) : (I (ir.domainField d')).K) = (kk : (I (ir.domainField d')).K) - (c0 : (I (ir.domainField d')).K) := by
            rw [hm', Int.cast_sub, centeredZ_cast]
            simp
          rw [Int.cast_natCast] at this
          rw [this, hkv, evalE_leaf]
          ring
        have hrd : ir.reader e w i = m := eq_natCast_of_castElt hfd hval
        have hvf : ir.valueField w < ir.fields.length := hfd ▸ hf'
        have hint : ir.evalIntWith (ir.reader e) d' (.leaf w) i = m := by
          change ir.intOf (ir.reader e) w i = m
          have hmlt : (m : ℤ) < (ir.charOf (ir.domainField d') : ℤ) := by
            rw [hm']
            have : (kk : ℤ) < N := by exact_mod_cast hkN
            linarith
          have hmlt' : m < (ir.field (ir.valueField w)).characteristic := by
            rw [hfd]
            exact_mod_cast hmlt
          rw [intOf_of_plain _ hpl, hrd, hL.toNat_natCast _ hvf m hmlt']
        rw [hint]
        refine ⟨by omega, by omega, ?_⟩
        change ((m : ℤ) : (I (ir.domainField d')).K) = castElt (ir.reader e w i)
        rw [hval, Int.cast_natCast]
      · cases hf
    · cases hf
  | quadRoot q r =>
    have hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
        ir.reader e v i = (I (ir.valueField v)).decode (es.getD i 0) :=
      fun _ _ hk i => reader_of_constant e hk i
    have hvf : ir.valueField v < ir.fields.length := hfd ▸ hf'
    simp only [srcFact] at hf
    split at hf
    · rename_i d' m lo hi hk
      split_ifs at hf with hc
      obtain ⟨rfl, hmf, hpl⟩ := hc
      split at hf
      · rename_i N hN
        cases hf
        have hm : Fact.HoldsWith ir (ir.reader e) (.ivl d' (.leaf m) lo hi) :=
          hfs _ (List.mem_of_getElem? hk)
        obtain ⟨hNp, hv'⟩ := quadSrcN_spec hI hL hK hvf
          (fun q hq hEq => h.equal _ (predicate_mem hq) hEq)
          (fun i hi => ⟨_, (hm i hi).1, (hm i hi).2.1,
            eq_intCast_of_castElt hmf (hm i hi).2.2.symm⟩) hN
        have hNd : N ≤ ir.charOf (ir.domainField d') := by
          have : ir.charOf (ir.valueField v) = ir.charOf (ir.domainField d') := by rw [hfd]
          omega
        exact ivl_of_natLeaf hwf hL hd hfd hpl hNd hv'
      · cases hf
    · cases hf
  | rootSet qs =>
    have hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
        ir.reader e v i = (I (ir.valueField v)).decode (es.getD i 0) :=
      fun _ _ hk i => reader_of_constant e hk i
    have hvf : ir.valueField v < ir.fields.length := hfd ▸ hf'
    simp only [srcFact] at hf
    split_ifs at hf with hpl
    split at hf
    · rename_i J hJ
      cases hf
      have hv' := rootSetSrc_spec hI hL hK (fun q hq hEq => h.equal _ (predicate_mem hq) hEq) hvf hJ
      refine ivl_of_natLeafIn hwf hL hd hfd hpl fun i hi => ?_
      obtain ⟨n, hn, hnp, hrd⟩ := hv' i hi
      exact ⟨n, hn.1, hn.2, by rw [← hfd]; exact hnp, hrd⟩
    · cases hf
  | tableHull _ _ _ => simp [srcFact] at hf


/-- **`ivlNatFact_sound`**: the rule is sound: its fact holds where its premises do. -/
theorem ivlNatFact_sound (hwf : ir.WellFormed) (hL : I.Lawful ir primeNodes) {rd : ir.Valuation I}
    {fs : List Fact} (hfs : ∀ f ∈ fs, f.HoldsWith ir rd) {d k : ℕ} {f : Fact}
    (hf : ir.ivlNatFact fs d k = some f) : f.HoldsWith ir rd := by
  unfold ivlNatFact at hf
  split at hf
  · rename_i d' v N hk
    split_ifs at hf with hc
    cases hf
    obtain ⟨rfl, hg, hpl, -, hN⟩ := hc
    unfold srcGuard at hg
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
    obtain ⟨⟨⟨-, hd⟩, hfd⟩, -⟩ := hg
    have hn : Fact.HoldsWith ir rd (.nat d' (.leaf v) N) := hfs _ (List.mem_of_getElem? hk)
    refine ivl_of_natLeaf hwf hL hd hfd hpl hN fun i hi => ?_
    obtain ⟨n, hnN, hn'⟩ := hn i hi
    exact ⟨n, hnN, eq_natCast_of_castElt hfd hn'.symm⟩
  · cases hf

/-- **An interval of an expression's integer readings that cast to its values** below its
length. -/
def IvlOn (ir : RealizedProgram) (rd : ir.Valuation I) (d : ℕ) (x : Expr) (J : Ivl) : Prop :=
  ∀ i < ir.exprLen x, ir.evalIntWith rd d x i ∈ J ∧
    ((ir.evalIntWith rd d x i : ℤ) : (I (ir.domainField d)).K) = ir.evalWith rd d x i

/-- **`ivlPrem_sound`**: the rule is sound: its fact holds where its premises do. -/
theorem ivlPrem_sound {rd : ir.Valuation I} {fs : List Fact} (hfs : ∀ f ∈ fs, f.HoldsWith ir rd)
    {d : ℕ} : ∀ {ks : List ℕ} {ps : List (Expr × Ivl)}, ivlPrem fs d ks = some ps →
      ∀ x ∈ ps, IvlOn ir rd d x.1 x.2
  | [], ps, h, x, hm => by
    simp only [ivlPrem, Option.some.injEq] at h
    subst h
    cases hm
  | k :: ks, ps, h, x, hm => by
    simp only [ivlPrem] at h
    split at h
    · rename_i d' y a b hk
      split_ifs at h with hc
      obtain ⟨ps', h', rfl⟩ := Option.map_eq_some_iff.1 h
      subst hc
      rcases List.mem_cons.1 hm with rfl | he
      · have hw : Fact.HoldsWith ir rd (.ivl d' y a b) := hfs _ (List.mem_of_getElem? hk)
        intro i hi
        obtain ⟨h1, h2, h3⟩ := hw i hi
        exact ⟨⟨h1, h2⟩, h3⟩
      · exact ivlPrem_sound hfs h' x he
    · cases h

/-- **`ivlNode_sound`**: the rule is sound: its fact holds where its premises do. -/
theorem ivlNode_sound (hwf : ir.WellFormed) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
    {rd : ir.Valuation I}
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0))
    {d : ℕ} (hd : d < ir.domains.length)
    {w : Expr → List (Expr × Ivl) → Option (Ivl × List (Expr × Ivl))}
    (hw : ∀ e ps J ps', w e ps = some (J, ps') → (∀ x ∈ ps, IvlOn ir rd d x.1 x.2) →
      IvlOn ir rd d e J ∧ ∀ x ∈ ps', IvlOn ir rd d x.1 x.2)
    {e : Expr} {ps ps' : List (Expr × Ivl)} {J : Ivl}
    (h : ir.ivlNode (ir.charOf (ir.domainField d)) (ir.domainField d) w e ps = some (J, ps'))
    (hps : ∀ x ∈ ps, IvlOn ir rd d x.1 x.2) :
    IvlOn ir rd d e J ∧ ∀ x ∈ ps', IvlOn ir rd d x.1 x.2 := by
  have hf := domainField_lt hwf hd
  have hchar := charP_field hI hf
  unfold ivlNode at h
  split at h
  · rename_i v
    split at h
    · rename_i es hk
      split_ifs at h with hc
      cases h
      obtain ⟨hp0, hall, hfd⟩ := hc
      refine ⟨fun i hi => ?_, hps⟩
      change i < (ir.value v).size at hi
      have hcp : es.getD i 0 < ir.charOf (ir.domainField d) := by
        rw [List.getD_eq_getElem?_getD]
        cases hes : es[i]? with
        | none =>
          simp only [Option.getD_none]
          exact hp0
        | some c =>
          exact of_decide_eq_true (List.all_eq_true.1 ((allK_eq _ es).symm.trans hall) c
            (List.mem_of_getElem? hes))
      have hint : ir.evalIntWith rd d (.leaf v) i =
          centeredZ (ir.charOf (ir.domainField d)) (es.getD i 0) := by
        change ir.intOf rd v i = _
        rw [intOf_of_constant _ hk, FieldInterp.centered_eq, hI.characteristic _ (hfd ▸ hf), hfd]
      rw [hint]
      refine ⟨mem_constIvlOf es hi, ?_⟩
      change _ = castElt (rd v i)
      rw [hK v es hk i, castElt_decode' hfd, hL.decode_natCast _ hf _ hcp, centeredZ_cast]
    · cases h
  · rename_i a b
    split_ifs at h with hl
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨⟨Ja, ps₁⟩, ha, ⟨Jb, ps₂⟩, hb, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨hA, hps₁⟩ := hw _ _ _ _ ha hps
    obtain ⟨hB, hps₂⟩ := hw _ _ _ _ hb hps₁
    refine ⟨fun i hi => ?_, hps₂⟩
    obtain ⟨a1, a2⟩ := hA i hi
    obtain ⟨b1, b2⟩ := hB i (lt_of_lt_of_le hi hl)
    refine ⟨Ivl.add_mem a1 b1, ?_⟩
    simp only [evalIntWith_add, evalWith, evalE_add, Int.cast_add]
    simp only [evalWith] at a2 b2
    rw [a2, b2]
  · rename_i a b
    split_ifs at h with hl
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨⟨Ja, ps₁⟩, ha, ⟨Jb, ps₂⟩, hb, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨hA, hps₁⟩ := hw _ _ _ _ ha hps
    obtain ⟨hB, hps₂⟩ := hw _ _ _ _ hb hps₁
    refine ⟨fun i hi => ?_, hps₂⟩
    obtain ⟨a1, a2⟩ := hA i hi
    obtain ⟨b1, b2⟩ := hB i (lt_of_lt_of_le hi hl)
    refine ⟨Ivl.sub_mem a1 b1, ?_⟩
    simp only [evalIntWith_sub, evalWith, evalE_sub, Int.cast_sub]
    simp only [evalWith] at a2 b2
    rw [a2, b2]
  · rename_i a b
    split_ifs at h with hl
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨⟨Ja, ps₁⟩, ha, ⟨Jb, ps₂⟩, hb, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨hA, hps₁⟩ := hw _ _ _ _ ha hps
    obtain ⟨hB, hps₂⟩ := hw _ _ _ _ hb hps₁
    refine ⟨fun i hi => ?_, hps₂⟩
    obtain ⟨a1, a2⟩ := hA i hi
    obtain ⟨b1, b2⟩ := hB i (lt_of_lt_of_le hi hl)
    refine ⟨Ivl.mul_mem a1 b1, ?_⟩
    simp only [evalIntWith_mul, evalWith, evalE_mul, Int.cast_mul]
    simp only [evalWith] at a2 b2
    rw [a2, b2]
  · rename_i c a
    split_ifs at h with hc
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨Ja, ps₁⟩, ha, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨hA, hps₁⟩ := hw _ _ _ _ ha hps
    refine ⟨fun i hi => ?_, hps₁⟩
    obtain ⟨a1, a2⟩ := hA i hi
    have hcen : (I (ir.domainField d)).centered c = centeredZ (ir.charOf (ir.domainField d)) c := by
      rw [FieldInterp.centered_eq, hI.characteristic _ hf]
    rw [evalIntWith_scale_const, hcen]
    refine ⟨Ivl.smul_mem _ a1, ?_⟩
    simp only [evalWith, evalE_scale_const, Int.cast_mul]
    simp only [evalWith] at a2
    rw [a2, centeredZ_cast, hL.decode_natCast _ hf _ hc]
  · rename_i idx a
    split_ifs at h with hr
    obtain ⟨hA, hps₁⟩ := hw _ _ _ _ h hps
    refine ⟨fun i hi => ?_, hps₁⟩
    exact hA _ (IndexMap.entry_lt_of_inRange hr hi)
  · rename_i a b
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨⟨Ja, ps₁⟩, ha, ⟨Jb, ps₂⟩, hb, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨hA, hps₁⟩ := hw _ _ _ _ ha hps
    obtain ⟨hB, hps₂⟩ := hw _ _ _ _ hb hps₁
    refine ⟨fun i hi => ?_, hps₂⟩
    rw [exprLen_concat] at hi
    simp only [evalIntWith_concat, evalWith, evalE_concat]
    split_ifs with hia
    · obtain ⟨a1, a2⟩ := hA i hia
      exact ⟨Ivl.hull_mem_left a1, a2⟩
    · obtain ⟨b1, b2⟩ := hB (i - ir.exprLen a) (by omega)
      exact ⟨Ivl.hull_mem_right b1, b2⟩
  · rename_i k
    split_ifs at h with hk
    obtain ⟨hA, hps₁⟩ := hw _ _ _ _ h hps
    refine ⟨fun i hi => ?_, hps₁⟩
    rw [exprLen_ref hwf.refsOrdered hk] at hi
    have := hA i hi
    simp only [evalWith] at this ⊢
    rw [evalIntWith_ref hwf.refsOrdered rd d hk, evalE_ref hwf.refsOrdered rd _ hk]
    exact this
  · rename_i op a
    split at h
    · rename_i m hm
      split_ifs at h with hp2
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨Ja, ps₁⟩, ha, he⟩ := h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      obtain ⟨hA, hps₁⟩ := hw _ _ _ _ ha hps
      obtain ⟨hp, -, h01, -⟩ := modData hwf hI hL hd hp2
      obtain ⟨h0', h1'⟩ := coefInt_zero_one h01 (hp ▸ hp2)
      refine ⟨fun i hi => ?_, hps₁⟩
      have hint : ir.evalIntWith rd d (.apply op a) i = ∑ s : Fin m, ir.evalIntWith rd d a (i * m + s) :=
        NamedOp.applyInt_of_sumWidth ir hm h0' h1' _ i
      have hval : ir.evalWith rd d (.apply op a) i = ∑ s : Fin m, ir.evalWith rd d a (i * m + s) :=
        NamedOp.apply_of_sumWidth ir hm _ i
      rw [hint, hval]
      refine ⟨Ivl.sum_mem fun s => (hA _ (NamedOp.lt_of_sumWidth ir hm hi s)).1, ?_⟩
      rw [Int.cast_sum]
      exact Finset.sum_congr rfl fun s _ => (hA _ (NamedOp.lt_of_sumWidth ir hm hi s)).2
    · rename_i hnone
      split_ifs at h with hp2
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨⟨Ja, ps₁⟩, ha, hJ⟩ := h
      obtain ⟨hA, hps₁⟩ := hw _ _ _ _ ha hps
      obtain ⟨hp, hchar', h01, hdec⟩ := modData hwf hI hL hd hp2
      have htn := hL.toNat_natCast _ (domainField_lt hwf hd)
      have hx : ∀ t < ir.exprLen a, ir.evalIntWith rd d a t ∈ Ja := fun t ht => (hA t ht).1
      have hxc : ∀ t < ir.exprLen a, ((ir.evalIntWith rd d a t : ℤ) : (I (ir.domainField d)).K) =
          ir.evalWith rd d a t := fun t ht => (hA t ht).2
      split at hJ
      · rename_i J' hm
        simp only [Option.some.injEq, Prod.mk.injEq] at hJ
        obtain ⟨rfl, rfl⟩ := hJ
        refine ⟨fun i hi => ⟨NamedOp.applyInt_mem_macIvl ir hp htn rd hm hx hi, ?_⟩, hps₁⟩
        change ((NamedOp.applyInt ir (ir.domainField d) rd op (ir.evalIntWith rd d a) i : ℤ) :
          (I (ir.domainField d)).K) = NamedOp.apply ir (ir.domainField d) rd op (ir.evalWith rd d a) i
        match op, hm with
        | .macConv r w' nch taps, hm =>
          simp only [NamedOp.macIvl] at hm
          split_ifs at hm with hW
          split at hm
          · rw [NamedOp.applyInt_macConv ir hp htn rd hW.2.1 hW.2.2,
              NamedOp.apply_macConv ir rd hW.2.1]
            push_cast
            refine Finset.sum_congr rfl fun c' _ => Finset.sum_congr rfl fun j _ => ?_
            have hlt : (c' : ℕ) * w' + j < nch * w' := by
              have := c'.2
              have := j.2
              nlinarith
            have hlt' : i / w' * (nch * w') + ((c' : ℕ) * w' + j) < ir.exprLen a :=
              NamedOp.lt_of_cols ir (op := .macConv r w' nch taps) hW.2.1 hi hlt
            rw [hxc _ hlt']
          · cases hm
      · rename_i hm
        simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hJ
        obtain ⟨J', hJ', rfl, rfl⟩ := hJ
        refine ⟨fun i hi => ?_, hps₁⟩
        have hP := NamedOp.applyInt_polyIvl ir hp hchar' htn rd (il := fun _ _ => 0)
          (fun v A hA => by cases hA) hdec (fun v J es hJ => by cases hJ) hJ' (x := ir.evalIntWith rd d a)
          (Len := ir.exprLen a) hi
        exact ⟨hP.1 hx, hP.2 _ hxc⟩
  · rename_i rows a
    split_ifs at h with hcol
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨⟨A, ps₁⟩, hA, K, hK, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨hon, hps₁⟩ := hw _ _ _ _ hA hps
    have hp : (I (ir.domainField d)).spec.characteristic = ir.charOf (ir.domainField d) :=
      hI.characteristic _ hf
    refine ⟨fun i hi => ?_, hps₁⟩
    change i < rows.length at hi
    obtain ⟨B, hB, hsub⟩ := linIvl_row rows hK i hi
    have hcols : ∀ t ∈ rows.getD i [], t.1 < ir.exprLen a := by
      intro t ht
      have hrow : rows.getD i [] ∈ rows := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
        exact List.getElem_mem hi
      exact of_decide_eq_true (List.all_eq_true.1 (List.all_eq_true.1 hcol _ hrow) t ht)
    have hmem := linRowIvl_mem (I := I) hp (il := ir.intOf rd) (y := ir.evalIntWith rd d a)
      (rows.getD i []) hB fun t ht => (hon t.1 (hcols t ht)).1
    have hcast := linRowIvl_cast (ir := ir) hp hchar (hL.decode_natCast _ hf) (leaf := rd)
      (il := ir.intOf rd) (y := ir.evalIntWith rd d a) (z := ir.evalWith rd d a)
      (rows.getD i []) hB fun t ht => (hon t.1 (hcols t ht)).2
    exact ⟨hsub _ hmem, hcast⟩
  · cases h

/-- **`ivlWalk_sound`**: the rule is sound: its fact holds where its premises do. -/
theorem ivlWalk_sound (hwf : ir.WellFormed) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
    {rd : ir.Valuation I}
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0))
    {d : ℕ} (hd : d < ir.domains.length) :
    ∀ (n : ℕ) (e : Expr) (ps : List (Expr × Ivl)) (J : Ivl) (ps' : List (Expr × Ivl)),
      ir.ivlWalk (ir.charOf (ir.domainField d)) (ir.domainField d) n e ps = some (J, ps') →
      (∀ x ∈ ps, IvlOn ir rd d x.1 x.2) → IvlOn ir rd d e J ∧ ∀ x ∈ ps', IvlOn ir rd d x.1 x.2
  | 0, _, _, _, _, h, _ => by cases h
  | n + 1, e, ps, J, ps', h, hps => by
    have hw := ivlWalk_sound (rd := rd) hwf hI hL hK hd n
    unfold ivlWalk at h
    split at h
    · rename_i x K ps₀
      split_ifs at h with hx
      · cases h
        obtain rfl := Expr.eq_of_beq hx
        exact ⟨hps _ List.mem_cons_self, fun y hy => hps y (List.mem_cons_of_mem _ hy)⟩
      · exact ivlNode_sound hwf hI hL hK hd hw h hps
    · exact ivlNode_sound hwf hI hL hK hd hw h hps

/-- **`ivlExprFact_sound`**: the rule is sound: its fact holds where its premises do. -/
theorem ivlExprFact_sound (hwf : ir.WellFormed) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
    {rd : ir.Valuation I}
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0))
    {fs : List Fact} (hfs : ∀ f ∈ fs, f.HoldsWith ir rd) {d : ℕ}
    {ks : List ℕ} {x : Expr} {lo hi : ℤ} {f : Fact} (hf : ir.ivlExprFact fs d ks x lo hi = some f) :
    f.HoldsWith ir rd := by
  unfold ivlExprFact at hf
  split_ifs at hf with hc
  obtain ⟨hd, -⟩ := hc
  split at hf
  · rename_i ps hps
    split at hf
    · rename_i J hJ
      split_ifs at hf with hw
      cases hf
      obtain ⟨hon, -⟩ := ivlWalk_sound hwf hI hL hK hd _ _ _ _ _ hJ (ivlPrem_sound hfs hps)
      intro i hi
      obtain ⟨hm, hc⟩ := hon i hi
      exact ⟨(Ivl.mem_of_within hw hm).1, (Ivl.mem_of_within hw hm).2, hc⟩
    · cases hf
  · cases hf

/-- **`transportFact_sound`**: the rule is sound: its fact holds where its premises do. -/
theorem transportFact_sound {rd : ir.Valuation I} {fs : List Fact}
    (hfs : ∀ f ∈ fs, f.HoldsWith ir rd) {k j : ℕ} {f : Fact}
    (hf : ir.transportFact fs k j = some f) : f.HoldsWith ir rd := by
  unfold transportFact at hf
  split at hf
  · rename_i d x y hk
    split_ifs at hf with hl
    have hxy : Fact.HoldsWith ir rd (.eq d x y) := hfs _ (List.mem_of_getElem? hk)
    split at hf
    · rename_i d' x' N hj
      split_ifs at hf with hc
      cases hf
      obtain ⟨rfl, hx⟩ := hc
      obtain rfl := Expr.eq_of_beq hx
      have hn : Fact.HoldsWith ir rd (.nat d' x' N) := hfs _ (List.mem_of_getElem? hj)
      intro i hi
      rw [← hxy i (lt_of_lt_of_le hi hl)]
      exact hn i (lt_of_lt_of_le hi hl)
    · rename_i t x' hj
      split_ifs at hf with hc
      cases hf
      obtain ⟨hfd, hx⟩ := hc
      obtain rfl := Expr.eq_of_beq hx
      have hn : Fact.HoldsWith ir rd (.inRows t x') := hfs _ (List.mem_of_getElem? hj)
      intro i hi
      obtain ⟨r, hr⟩ := hn i (lt_of_lt_of_le hi hl)
      have h1 := hxy i (lt_of_lt_of_le hi hl)
      simp only [evalWith] at h1
      refine ⟨r, ?_⟩
      rw [hr]
      clear hr
      revert h1
      generalize ir.chalField (ir.alphaOf t) = a at hfd ⊢
      subst hfd
      exact id
    · cases hf
  · cases hf

/-- **The value of a quotient shape** `q · Q + C` below `n`. -/
theorem evalE_quotShape (hL : I.Lawful ir primeNodes) {rd : ir.Valuation I}
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0))
    {f n q c : ℕ} {y Q : Expr} (h : ir.quotShape f n y = some (q, Q, c))
    (hf : f < ir.fields.length) (hq : q < ir.charOf f) {i : ℕ} (hi : i < n) :
    ir.evalE rd f y i = (q : (I f).K) * ir.evalE rd f Q i + (c : (I f).K) := by
  unfold quotShape at h
  split at h
  · rename_i q' Q' u
    obtain ⟨c', hc', he⟩ := Option.map_eq_some_iff.1 h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    rw [evalE_add, evalE_scale_const, hL.decode_natCast _ hf _ hq,
      (constEntry_sound hL hK hc' hf).2 i hi]
  · rename_i q' Q'
    cases h
    rw [evalE_scale_const, hL.decode_natCast _ hf _ hq]
    simp
  · cases h

/-- **`liftFact_sound`**: the rule is sound: its fact holds where its premises do. -/
theorem liftFact_sound (hwf : ir.WellFormed) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
    {rd : ir.Valuation I}
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0))
    {fs : List Fact} (hfs : ∀ f ∈ fs, f.HoldsWith ir rd) {k a b : ℕ} {f : Fact}
    (hf : ir.liftFact fs k a b = some f) : f.HoldsWith ir rd := by
  unfold liftFact at hf
  split at hf
  · rename_i d x y hk
    split at hf
    · rename_i d₂ x' lo hi ha
      split_ifs at hf with hc
      obtain ⟨hd, rfl, hx⟩ := hc
      obtain rfl := Expr.eq_of_beq hx
      have hfl := domainField_lt hwf hd
      have hchar := charP_field hI hfl
      have hxy : Fact.HoldsWith ir rd (.eq d₂ x' y) := hfs _ (List.mem_of_getElem? hk)
      have hxi : Fact.HoldsWith ir rd (.ivl d₂ x' lo hi) := hfs _ (List.mem_of_getElem? ha)
      split at hf
      · rename_i d₃ y' lo' hi' hb
        split_ifs at hf with hc
        cases hf
        obtain ⟨rfl, hy, hlen, h1, h2⟩ := hc
        obtain rfl := Expr.eq_of_beq hy
        have hyi : Fact.HoldsWith ir rd (.ivl d₃ y' lo' hi') := hfs _ (List.mem_of_getElem? hb)
        intro i hix
        obtain ⟨ha1, ha2, ha3⟩ := hxi i hix
        obtain ⟨hb1, hb2, hb3⟩ := hyi i (lt_of_lt_of_le hix hlen)
        have hdvd : ((ir.charOf (ir.domainField d₃) : ℕ) : ℤ) ∣
            ir.evalIntWith rd d₃ x' i - ir.evalIntWith rd d₃ y' i := by
          rw [← CharP.intCast_eq_zero_iff (I (ir.domainField d₃)).K, Int.cast_sub, ha3, hb3,
            hxy i hix, sub_self]
        have := Int.eq_zero_of_abs_lt_dvd hdvd (abs_lt.2 ⟨by linarith, by linarith⟩)
        linarith
      · rename_i d₃ Q N hb
        unfold quotLift at hf
        split at hf
        · rename_i q Q' c hq
          split_ifs at hf with hc
          cases hf
          obtain ⟨rfl, hQ, hlen, hq0, hqp, hN, hcq, hhi, hlo⟩ := hc
          obtain rfl := Expr.eq_of_beq hQ
          have hQn : Fact.HoldsWith ir rd (.nat d₃ Q' N) := hfs _ (List.mem_of_getElem? hb)
          intro i hix
          obtain ⟨ha1, ha2, ha3⟩ := hxi i hix
          obtain ⟨n, hn, hnv⟩ := hQn i (lt_of_lt_of_le hix hlen)
          simp only [evalWith] at hnv
          have hy := evalE_quotShape hL hK hq hfl hqp hix
          have hz : IntIn lo hi (ir.evalIntWith rd d₃ x' i) (ir.evalWith rd d₃ x' i) :=
            ⟨ha1, ha2, ha3⟩
          have hM : (((q * (N - 1) + 1 : ℕ) : ℤ)) - 1 +
              (centeredZ (ir.charOf (ir.domainField d₃)) c - lo) < ir.charOf (ir.domainField d₃) := by
            push_cast
            push_cast at hlo
            linarith
          have hlift := IntIn.sub_eq_natCast (p := ir.charOf (ir.domainField d₃)) hz hhi hM
            (n := q * n) (Nat.lt_succ_of_le (Nat.mul_le_mul_left q (by omega))) (by
              rw [hxy i hix]
              simp only [evalWith]
              rw [hy, ← hnv, centeredZ_cast]
              push_cast
              ring)
          have hdq : (q : ℤ) ∣ centeredZ (ir.charOf (ir.domainField d₃)) c :=
            Int.dvd_of_emod_eq_zero hcq
          have : ir.evalIntWith rd d₃ x' i =
              (q : ℤ) * n + centeredZ (ir.charOf (ir.domainField d₃)) c := by
            push_cast at hlift
            linarith
          rw [this]
          exact dvd_add (dvd_mul_right _ _) hdq
        · cases hf
      · cases hf
    · cases hf
  · cases hf

/-- **The digits' sum of digits below `T < p`** is the cast of a natural below `T^n`. -/
theorem isNatBelow_digitExpr (hL : I.Lawful ir primeNodes) {rd : ir.Valuation I} {f T : ℕ}
    (hf : f < ir.fields.length) (hT : T < ir.charOf f) (i : ℕ) :
    ∀ (Ds : List Expr) (D : Expr), (∀ D' ∈ D :: Ds, IsNatBelow T (ir.evalE rd f D' i)) →
      IsNatBelow (T ^ (Ds.length + 1)) (ir.evalE rd f (digitExpr T D Ds) i)
  | [], D, h => by simpa [digitExpr] using h D List.mem_cons_self
  | D' :: Ds, D, h => by
    obtain ⟨n₀, hn₀, h0⟩ := h D List.mem_cons_self
    obtain ⟨m, hm, h1⟩ := isNatBelow_digitExpr hL hf hT i Ds D' fun D'' hD'' =>
      h D'' (List.mem_cons_of_mem _ hD'')
    refine ⟨n₀ + T * m, ?_, ?_⟩
    · have : T * (m + 1) ≤ T * T ^ (Ds.length + 1) := Nat.mul_le_mul_left T hm
      simp only [List.length_cons]
      rw [pow_succ']
      nlinarith
    · simp only [digitExpr]
      rw [evalE_add, evalE_scale_const, hL.decode_natCast _ hf _ hT, ← h0, ← h1]
      push_cast
      ring

/-- **`natPrem_sound`**: the rule is sound: its fact holds where its premises do. -/
theorem natPrem_sound {rd : ir.Valuation I} {fs : List Fact} (hfs : ∀ f ∈ fs, f.HoldsWith ir rd)
    {d T : ℕ} : ∀ {ks : List ℕ} {Ds : List Expr}, natPrem fs d T ks = some Ds →
      ∀ D ∈ Ds, ∀ i < ir.exprLen D, IsNatBelow T (ir.evalWith rd d D i)
  | [], Ds, h, D, hD => by
    simp only [natPrem, Option.some.injEq] at h
    subst h
    cases hD
  | k :: ks, Ds, h, D, hD => by
    simp only [natPrem] at h
    split at h
    · rename_i d' D₀ N hk
      split_ifs at h with hc
      obtain ⟨Ds', h', rfl⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨rfl, hNT⟩ := hc
      rcases List.mem_cons.1 hD with rfl | hD
      · intro i hi
        obtain ⟨n, hn, hv⟩ := (hfs _ (List.mem_of_getElem? hk) : Fact.HoldsWith ir rd _) i hi
        exact ⟨n, by omega, hv⟩
      · exact natPrem_sound hfs h' D hD
    · cases h

/-- **Equal linear forms have equal values** below `n`. -/
theorem linSameB_sound {rd : ir.Valuation I}
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0))
    (hwf : ir.WellFormed) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes) {d n : ℕ}
    (hd : d < ir.domains.length) {y z : Expr}
    (h : ir.linSameB (ir.domainField d) n y z = true) :
    ∀ i < n, ir.evalWith rd d y i = ir.evalWith rd d z i := by
  intro i hi
  unfold linSameB at h
  split at h
  · rename_i x hx
    have hfl := domainField_lt hwf hd
    have := charP_field hI hfl
    have h1 := evalE_linTerms hK hL hfl hx i hi
    have h3 := linZeroB_sound (K := (I (ir.domainField d)).K) (p := ir.charOf (ir.domainField d))
      (fun t => ir.evalE rd (ir.domainField d) t i) h
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h1
    simp only [evalWith]
    push_cast at h1
    linear_combination h1 + h3
  · cases h

/-- **`digitsFact_sound`**: the rule is sound: its fact holds where its premises do. -/
theorem digitsFact_sound (hwf : ir.WellFormed) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
    {rd : ir.Valuation I}
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0))
    {fs : List Fact} (hfs : ∀ f ∈ fs, f.HoldsWith ir rd) {d k T : ℕ} {ds : List ℕ} {f : Fact}
    (hf : ir.digitsFact fs d k ds T = some f) : f.HoldsWith ir rd := by
  unfold digitsFact at hf
  split at hf
  · rename_i d' x y hk
    split at hf
    · rename_i D Ds hDs
      split_ifs at hf with hc
      cases hf
      obtain ⟨rfl, hd, hy, hlen, hT⟩ := hc
      have hxy : Fact.HoldsWith ir rd (.eq d' x y) := hfs _ (List.mem_of_getElem? hk)
      intro i hi
      have hyz : ir.evalWith rd d' y i = ir.evalWith rd d' (digitExpr T D Ds) i := by
        rcases Bool.or_eq_true_iff.1 hy with hb | hl
        · rw [Expr.eq_of_beq hb]
        · exact linSameB_sound hK hwf hI hL hd hl i hi
      rw [show ir.evalWith rd d' x i = _ from hxy i hi, hyz]
      exact isNatBelow_digitExpr hL (domainField_lt hwf hd) hT i Ds D fun D' hD' =>
        natPrem_sound hfs hDs D' hD' i
          (lt_of_lt_of_le hi (of_decide_eq_true (List.all_eq_true.1 hlen D' hD')))
    · cases hf
  · cases hf

/-- **`congrFact_sound`**: the rule is sound: its fact holds where its premises do. -/
theorem congrFact_sound {rd : ir.Valuation I} {fs : List Fact}
    (hfs : ∀ f ∈ fs, f.HoldsWith ir rd) {pid k : ℕ} {body : PredBody}
    (hpb : (ir.predicate pid).body = body) {f : Fact} (hf : congrFact fs pid body k = some f) :
    f.HoldsWith ir rd := by
  subst hpb
  unfold congrFact at hf
  split at hf
  · rename_i d' x q' hk
    split at hf
    · rename_i d q e e' r hb
      split_ifs at hf with hc
      cases hf
      obtain ⟨rfl, rfl, hx⟩ := hc
      obtain rfl := Expr.eq_of_beq hx
      have hd : Fact.HoldsWith ir rd (.dvd d' (.sub e e') q') := hfs _ (List.mem_of_getElem? hk)
      show ir.HoldsWith rd (ir.predicate pid).body
      rw [hb]
      exact holdsWith_mod_iff.2 hd
    · cases hf
  · cases hf

/-- **A row of a table, read in the domain's field, makes a one-record `in` into the table
hold** at that coordinate. -/
theorem inRows_table_of_row {rd : ir.Valuation I} {d t : ℕ} {x : Expr} {i : ℕ}
    (hfd : ir.chalField (ir.alphaOf t) = ir.domainField d)
    (h : ∃ j, ir.tableRow rd (ir.chalField (ir.alphaOf t)) t j =
      ir.evalE rd (ir.chalField (ir.alphaOf t)) x i) :
    ir.InSetWith rd d [x] i (.table t) := by
  obtain ⟨j, hj⟩ := h
  revert hj
  generalize ir.chalField (ir.alphaOf t) = a at hfd
  subst hfd
  intro hj
  change ir.InRows rd d [x] i (ir.table t).rows
  rcases hr : (ir.table t).rows with T | cols | e'
  · rw [tableRow_of_isRange (isRange_of_rows hr)] at hj
    have hT : ir.tableSize t = T := by simp [tableSize, hr]
    intro y hy
    rw [List.mem_singleton.1 hy]
    exact ⟨j, by rw [← hT]; exact j.2, hj.symm⟩
  · rw [tableRow_of_columns hr] at hj
    refine ⟨j, by rw [← tableSize_of_columns hr]; exact j.2, fun ec hec => ?_⟩
    cases cols with
    | nil => simp at hec
    | cons c rest =>
      simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_singleton] at hec
      subst hec
      exact hj.symm
  · rw [tableRow_of_expr hr] at hj
    intro y hy
    rw [List.mem_singleton.1 hy]
    exact ⟨j, by rw [← tableSize_of_expr hr]; exact j.2, hj.symm⟩

/-- **`natLinPrem_sound`**: the ranges of a `natLin` step hold. -/
theorem natLinPrem_sound {rd : ir.Valuation I} {fs : List Fact} (hfs : ∀ f ∈ fs, f.HoldsWith ir rd)
    {d n : ℕ} : ∀ {ks : List ℕ} {xs : List (Expr × ℕ)}, ir.natLinPrem fs d n ks = some xs →
      ∀ xN ∈ xs, ∀ i < n, IsNatBelow xN.2 (ir.evalWith rd d xN.1 i)
  | [], xs, h, xN, hm => by
    simp only [natLinPrem, Option.some.injEq] at h
    subst h
    cases hm
  | k :: ks, xs, h, xN, hm => by
    simp only [natLinPrem] at h
    split at h
    · rename_i d' x N hk
      split_ifs at h with hc
      obtain ⟨xs', h', rfl⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨rfl, hn⟩ := hc
      rcases List.mem_cons.1 hm with rfl | hm
      · intro i hi
        exact (hfs _ (List.mem_of_getElem? hk) : Fact.HoldsWith ir rd (.nat d' x N)) i (by omega)
      · exact natLinPrem_sound hfs h' xN hm
    · cases h

/-- **A sum of constant multiples of bounded naturals** is the cast of a natural at most the sum of
the multiples of the bounds less one, below `p`. -/
theorem foldr_scale_isNat (hL : I.Lawful ir primeNodes) {rd : ir.Valuation I} {f : ℕ}
    (hf : f < ir.fields.length) (e : Expr) (i : ℕ) :
    ∀ cs : List (ℕ × Expr × ℕ), (∀ c ∈ cs, c.1 < ir.charOf f ∧ 0 < c.2.2 ∧
        IsNatBelow c.2.2 (ir.evalE rd f c.2.1 i)) → 0 < ir.charOf f →
      ∃ m ≤ (cs.map fun c => c.1 * (c.2.2 - 1)).sum, ((m : ℕ) : (I f).K) =
        ir.evalE rd f (cs.foldr (fun c acc => .add (.scale (.const c.1) c.2.1) acc)
          (.scale (.const 0) e)) i
  | [], _, hp => ⟨0, le_rfl, by
      simp only [List.foldr_nil, evalE_scale_const, hL.decode_natCast _ hf 0 hp]; simp⟩
  | c :: cs, h, hp => by
    obtain ⟨hc, hN, n, hn, hv⟩ := h c List.mem_cons_self
    obtain ⟨m, hm, hmv⟩ := foldr_scale_isNat hL hf e i cs (fun c' hc' => h c' (List.mem_cons_of_mem _ hc')) hp
    refine ⟨c.1 * n + m, ?_, ?_⟩
    · simp only [List.map_cons, List.sum_cons]
      have : c.1 * n ≤ c.1 * (c.2.2 - 1) := Nat.mul_le_mul_left _ (by omega)
      omega
    · simp only [List.foldr_cons, evalE_add, evalE_scale_const, hL.decode_natCast _ hf _ hc, ← hv, ← hmv]
      push_cast
      ring

/-- **`natLinFact_sound`**: a bounded nonnegative combination of ranges is a range. -/
theorem natLinFact_sound (hwf : ir.WellFormed) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
    {rd : ir.Valuation I}
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0))
    {fs : List Fact} (hfs : ∀ f ∈ fs, f.HoldsWith ir rd) {d k : ℕ} {ks : List ℕ} {f : Fact}
    (hf : ir.natLinFact fs d k ks = some f) : f.HoldsWith ir rd := by
  unfold natLinFact at hf
  split at hf
  · rename_i d' e y hk
    split_ifs at hf with hc
    obtain ⟨h1, hd⟩ := hc
    rw [h1] at hk
    dsimp only at hf
    split at hf
    · rename_i xs ly hxs hly
      split_ifs at hf with hc2
      cases hf
      obtain ⟨hall, hS, hsame⟩ := hc2
      have hfl := domainField_lt hwf hd
      have hey : Fact.HoldsWith ir rd (.eq d e y) := hfs _ (List.mem_of_getElem? hk)
      intro i hi
      have hp0 : 0 < ir.charOf (ir.domainField d) := by omega
      obtain ⟨m, hm, hmv⟩ := foldr_scale_isNat hL hfl e i
        (xs.map fun xN => (coefIn (ir.charOf (ir.domainField d)) ly.2 xN.1, xN.1, xN.2))
        (fun c hc => by
          obtain ⟨xN, hxN, rfl⟩ := List.mem_map.1 hc
          have h0 := of_decide_eq_true (List.all_eq_true.1 hall _ hc)
          refine ⟨?_, h0.2, natLinPrem_sound hfs hxs xN hxN i hi⟩
          simp only [coefIn]
          have := Int.emod_lt_of_pos (((ly.2.filter fun t => t.2.beq xN.1).map (·.1)).sum)
            (show (0 : ℤ) < (ir.charOf (ir.domainField d) : ℤ) by exact_mod_cast hp0)
          have := Int.emod_nonneg (((ly.2.filter fun t => t.2.beq xN.1).map (·.1)).sum)
            (show (ir.charOf (ir.domainField d) : ℤ) ≠ 0 by exact_mod_cast hp0.ne')
          omega) hp0
      refine ⟨m, by omega, ?_⟩
      rw [hey i hi, linSameB_sound hK hwf hI hL hd hsame i hi]
      exact hmv
    · cases hf
  · cases hf

/-- **`natBoolFact_holds`**: a Boolean check bounds its value by `2`, at any reader where the
field `equal`s hold. -/
theorem natBoolFact_holds {rd : ir.Valuation I}
    (heq : ∀ p ∈ ir.predicates, p.body.isEqual = true → ir.HoldsWith rd p.body) {p : ℕ} {f : Fact}
    (hf : ir.natBoolFact p = some f) : f.HoldsWith ir rd := by
  unfold natBoolFact at hf
  split_ifs at hf with hp
  obtain ⟨⟨d, v⟩, hb, rfl⟩ := Option.map_eq_some_iff.1 hf
  unfold boolOf? at hb
  split at hb
  · rename_i d' a b c t hbody
    have hc : a = v ∧ b = v ∧ d' = d := by
      split at hb <;> (try split_ifs at hb with hc') <;> (try cases hb) <;>
        exact ⟨Expr.eq_of_beq hc'.1, Expr.eq_of_beq hc'.2, rfl⟩
    have hcv : c = v := by
      split at hb <;> (try split_ifs at hb) <;> (try cases hb) <;> rfl
    obtain ⟨rfl, rfl, rfl⟩ := hc
    subst hcv
    have hq := heq _ (predicate_mem hp) (by rw [hbody]; rfl)
    change ir.HoldsWith _ _ at hq
    rw [hbody] at hq
    intro i hi
    have hx := hq i hi
    simp only [evalWith, evalE_mul] at hx
    rcases IsIdempotentElem.iff_eq_zero_or_one.1 hx with h0 | h1
    · exact ⟨0, by omega, by simp [evalWith, h0]⟩
    · exact ⟨1, by omega, by simp [evalWith, h1]⟩
  · cases hb


/-- **`natBoolFact_sound`**: a Boolean check bounds its value by `2` (`natBoolFact_holds`). -/
theorem natBoolFact_sound {e : ir.Env I} (h : ir.RealizedAt e) {p : ℕ} {f : Fact}
    (hf : ir.natBoolFact p = some f) : f.HoldsWith ir (ir.reader e) :=
  natBoolFact_holds h.equal hf

/-- **`liftConstFact_sound`**: the constant-quotient lift is sound. -/
theorem liftConstFact_sound (hwf : ir.WellFormed) (hI : I.Registered ir)
    (hL : I.Lawful ir primeNodes) {rd : ir.Valuation I}
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0))
    {fs : List Fact} (hfs : ∀ f ∈ fs, f.HoldsWith ir rd) {body : PredBody} {k a : ℕ} {f : Fact}
    (hf : ir.liftConstFact fs body k a = some f) : f.HoldsWith ir rd := by
  unfold liftConstFact at hf
  split at hf
  · rename_i q
    split at hf
    · rename_i d x C d' x' lo hi hk ha
      split_ifs at hf with hc
      obtain ⟨rfl, hx, hd, hq⟩ := hc
      obtain rfl := Expr.eq_of_beq hx
      split at hf
      · rename_i c hce
        split_ifs at hf with hc2
        cases hf
        obtain ⟨hcq, hhi, hlo⟩ := hc2
        have hfl := domainField_lt hwf hd
        have hchar := charP_field hI hfl
        have hxC : Fact.HoldsWith ir rd (.eq d' x' (.leaf C)) := hfs _ (List.mem_of_getElem? hk)
        have hxi : Fact.HoldsWith ir rd (.ivl d' x' lo hi) := hfs _ (List.mem_of_getElem? ha)
        intro i hix
        obtain ⟨a1, a2, a3⟩ := hxi i hix
        have hz : IntIn lo hi (ir.evalIntWith rd d' x' i) (ir.evalWith rd d' x' i) := ⟨a1, a2, a3⟩
        have hlift := IntIn.sub_eq_natCast (p := ir.charOf (ir.domainField d')) (M := 1) (n := 0)
          hz hhi (by push_cast; linarith) Nat.one_pos (by
            rw [hxC i hix]
            simp only [evalWith]
            rw [(constEntry_sound hL hK hce hfl).2 i hix, centeredZ_cast]
            simp)
        have : ir.evalIntWith rd d' x' i = centeredZ (ir.charOf (ir.domainField d')) c := by
          push_cast at hlift
          linarith
        rw [this]
        exact Int.dvd_of_emod_eq_zero hcq
      · cases hf
    · cases hf
  · cases hf

/-- **`natCompFact_sound`**: a complement within the characteristic bounds its expression. -/
theorem natCompFact_sound (hwf : ir.WellFormed) (hI : I.Registered ir)
    (hL : I.Lawful ir primeNodes) {rd : ir.Valuation I}
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0))
    {fs : List Fact} (hfs : ∀ f ∈ fs, f.HoldsWith ir rd) {d k j : ℕ} {f : Fact}
    (hf : ir.natCompFact fs d k j = some f) : f.HoldsWith ir rd := by
  unfold natCompFact at hf
  split at hf
  · rename_i d₁ e A d₂ Xc B hk hj
    split_ifs at hf with hc
    obtain ⟨h1, h2, hd, hlen, hAB, hA, hB⟩ := hc
    rw [h1] at hk
    rw [h2] at hj
    split at hf
    · rename_i x hx
      split_ifs at hf with hc2
      cases hf
      obtain ⟨hcp, hz⟩ := hc2
      have hfl := domainField_lt hwf hd
      have hchar := charP_field hI hfl
      have he : Fact.HoldsWith ir rd (.nat d e A) := hfs _ (List.mem_of_getElem? hk)
      have hX : Fact.HoldsWith ir rd (.nat d Xc B) := hfs _ (List.mem_of_getElem? hj)
      intro i hi
      obtain ⟨a, haA, hav⟩ := he i hi
      obtain ⟨b, hbB, hbv⟩ := hX i (lt_of_lt_of_le hi hlen)
      set c := (x.1 % (ir.charOf (ir.domainField d) : ℤ)).toNat
      have h1 := evalE_linTerms hK hL hfl hx i hi
      have h3 := linZeroB_sound (K := (I (ir.domainField d)).K)
        (p := ir.charOf (ir.domainField d)) (fun t => ir.evalE rd (ir.domainField d) t i) hz
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h1
      simp only [evalWith] at hav hbv
      have hsum : (((a + b : ℕ)) : (I (ir.domainField d)).K) = ((c : ℕ) : (I (ir.domainField d)).K) := by
        push_cast at h1 h3 ⊢
        rw [hav, hbv]
        linear_combination h1 + h3
      have hmod := (CharP.natCast_eq_natCast _ (ir.charOf (ir.domainField d))).1 hsum
      have hab : a + b = c := by
        unfold Nat.ModEq at hmod
        rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hcp] at hmod
      exact ⟨a, by omega, hav⟩
    · cases hf
  · cases hf

/-- **`concludeFact_sound`**: the rule is sound: its fact holds where its premises do. -/
theorem concludeFact_sound {rd : ir.Valuation I} {fs : List Fact}
    (hfs : ∀ f ∈ fs, f.HoldsWith ir rd) {pid k : ℕ} {body : PredBody}
    (hpb : (ir.predicate pid).body = body) {f : Fact}
    (hf : ir.concludeFact fs pid body k = some f) : f.HoldsWith ir rd := by
  subst hpb
  unfold concludeFact at hf
  split at hf
  · rename_i d' a' b' hk
    split at hf
    · rename_i d a b t hb
      split_ifs at hf with hc
      cases hf
      obtain ⟨rfl, ha, hb'⟩ := hc
      obtain rfl := Expr.eq_of_beq ha
      obtain rfl := Expr.eq_of_beq hb'
      show ir.HoldsWith rd (ir.predicate pid).body
      rw [hb]
      exact hfs _ (List.mem_of_getElem? hk)
    · cases hf
  · rename_i d' x' N' hk
    split at hf
    · rename_i d x N r hb
      split_ifs at hf with hc
      cases hf
      obtain ⟨rfl, hx, hN⟩ := hc
      obtain rfl := Expr.eq_of_beq hx
      have hn : Fact.HoldsWith ir rd (.nat d' x' N') := hfs _ (List.mem_of_getElem? hk)
      show ir.HoldsWith rd (ir.predicate pid).body
      rw [hb]
      intro i hi
      obtain ⟨n, hn', hv⟩ := hn i hi
      exact (inRows_range_iff rd d' x' i N).2 ⟨n, by omega, hv⟩
    · cases hf
  · rename_i t' x' hk
    split at hf
    · rename_i d x t r hb
      split_ifs at hf with hc
      cases hf
      obtain ⟨rfl, hx, hfd⟩ := hc
      obtain rfl := Expr.eq_of_beq hx
      have hn : Fact.HoldsWith ir rd (.inRows t' x') := hfs _ (List.mem_of_getElem? hk)
      show ir.HoldsWith rd (ir.predicate pid).body
      rw [hb]
      intro i hi
      exact inRows_table_of_row hfd (hn i hi)
    · rename_i d x e' r hb
      split at hf
      · rename_i e₀ hr
        split_ifs at hf with hc
        cases hf
        obtain ⟨he, hx, hfd⟩ := hc
        obtain rfl := Expr.eq_of_beq he
        obtain rfl := Expr.eq_of_beq hx
        have hn : Fact.HoldsWith ir rd (.inRows t' x') := hfs _ (List.mem_of_getElem? hk)
        show ir.HoldsWith rd (ir.predicate pid).body
        rw [hb]
        intro i hi
        have := inRows_table_of_row hfd (hn i hi)
        change ir.InRows rd d [x'] i (ir.table t').rows at this
        rw [hr] at this
        exact this
      · cases hf
    · cases hf
  · rename_i d' a' b' hk
    split at hf
    · rename_i d q a b r hb
      split_ifs at hf with hc
      cases hf
      obtain ⟨rfl, rfl, ha, hb'⟩ := hc
      obtain rfl := Expr.eq_of_beq ha
      obtain rfl := Expr.eq_of_beq hb'
      have hn : Fact.HoldsWith ir rd (.intEq d' a' b') := hfs _ (List.mem_of_getElem? hk)
      show ir.HoldsWith rd (ir.predicate pid).body
      rw [hb]
      refine holdsWith_mod_iff.2 fun i hi => ?_
      rw [hn i hi, sub_self]
      exact dvd_zero _
    · cases hf
  · cases hf

end Sound

end GordieHowe.RealizedProgram
