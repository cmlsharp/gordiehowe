-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Derivation.Pure
public import GordieHowe.Language.Realizations.RealizeHonest

@[expose] public section

/-!
# GordieHowe: the honest prover over derivations

Completeness of the realized program from valid derivations
(`GordieHowe.RealizedProgram.realizedAt_of_honest_derivs`): where the program holds and the honest
prover's obligations hold, the realized program holds.

* **The honest steps** (`GordieHowe.RealizedProgram.honestStepB`) hold at any reader where every
  predicate holds and every group's needles are rows of its table
  (`GordieHowe.RealizedProgram.stepFact_honest`): the reader-generic rules, lookups, cited
  predicates and the facts read from them.
* **A `mod_0` has its field equation** where its integer equality holds: its derivation cites
  intervals of both sides by shared entries of honest steps (`DerivationsValid.mods`), which hold
  at the honest prover's reader; an interval fact casts its side's integer reading back to its
  field value.
-/

namespace GordieHowe.RealizedProgram

open Export Range IOP

section

variable {ir : RealizedProgram} {I : Interp} {primeNodes : ℕ → List String}

/-- **An honest interval source is reader-generic** (`pureSrcFact`). -/
theorem pureSrcFact_of_honest {sr : List (ℕ × ℕ)} {fs : List Fact} {d v : ℕ} {s : IvlSrc}
    (hs : honestSrcB s = true) :
    ir.pureSrcFact primeNodes sr fs d v s = ir.srcFact primeNodes sr fs d v s := by
  cases s <;> simp_all [honestSrcB, pureSrcFact]

/-- **A typed interval source is sound at a typed environment's reader** (`typedSrcB`) where every
equality predicate holds: a value of a prime node reads below the characteristic by its type, an
opaque bit reads `0` or `1` by the opaque call's evaluation, a root of cited equalities lies in
their roots' hull, and a leaf whose sum with a constant is a range lies in the shifted range. -/
theorem srcFact_typed_sound (hwf : ir.WellFormed) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
    {sr : List (ℕ × ℕ)} {e : ir.Env I} (ht : ir.TypesHold e) {fs : List Fact} {d v : ℕ}
    {s : IvlSrc} {f : Fact} (hs : typedSrcB s = true)
    (hE : ∀ p ∈ ir.predicates, p.body.isEqual = true → ir.HoldsWith (ir.reader e) p.body)
    (hfs : ∀ f ∈ fs, f.Holds e) (hg : ir.srcGuard d v = true) (hf : ir.srcFact primeNodes sr fs d v s = some f) :
    f.Holds e := by
  unfold srcGuard at hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨⟨hv, hd⟩, hfd⟩, hp2⟩ := hg
  have hf' := domainField_lt hwf hd
  have hchar := charP_field hI hf'
  cases s with
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
      have hin := ht v hv hts i hi
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
          (fun q hq hEq => hE _ (predicate_mem hq) hEq)
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
      have hv' := rootSetSrc_spec hI hL hK (fun q hq hEq => hE _ (predicate_mem hq) hEq) hvf hJ
      refine ivl_of_natLeafIn hwf hL hd hfd hpl fun i hi => ?_
      obtain ⟨n, hn, hnp, hrd⟩ := hv' i hi
      exact ⟨n, hn.1, hn.2, by rw [← hfd]; exact hnp, hrd⟩
    · cases hf
  | _ => simp [typedSrcB] at hs

/-- **`stepFact_honest`**: an honest step's fact holds at any reader `rd` whose constants read
their entries (`hK`), whose ranged values lie in their ranges (`hS`), whose bound values read their
expressions (`hB`), where every predicate holds (`hpreds`) and every group's needles are rows of
its table (`hin`), from its premises' facts at `rd`. -/
theorem stepFact_honest (hwf : ir.WellFormed) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
    {rd : ir.Valuation I}
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0))
    {sr : List (ℕ × ℕ)}
    (hS : ∀ vN ∈ sr, ∀ i < (ir.value vN.1).size,
      ∃ n < vN.2, rd vN.1 i = ((n : ℕ) : (I (ir.valueField vN.1)).K))
    (hB : ir.BoundReads rd)
    (hpreds : ∀ q < ir.predicates.length, ir.HoldsWith rd (ir.predicate q).body)
    (hin : ∀ t < ir.tables.length, ∀ g < ir.groupCountOf t, ir.NeedlesIn rd t g)
    (hT : ∀ {fs : List Fact} {d v : ℕ} {s : IvlSrc} {f : Fact}, typedSrcB s = true →
      (∀ f ∈ fs, f.HoldsWith ir rd) → ir.srcGuard d v = true → ir.srcFact primeNodes sr fs d v s = some f → f.HoldsWith ir rd)
    {ctx : DerivCtx} {self pid : ℕ} {body : PredBody} {fs : List Fact}
    (hfs : ∀ f ∈ fs, f.HoldsWith ir rd) {s : Step} (hs : honestStepB s = true) {f : Fact}
    (hf : ir.stepFact primeNodes sr ctx self pid body fs s = some f) : f.HoldsWith ir rd := by
  have heq : ∀ p ∈ ir.predicates, p.body.isEqual = true → ir.HoldsWith rd p.body := by
    intro p hp _
    obtain ⟨q, hq, rfl⟩ := exists_index_of_mem hp
    exact hpreds q hq
  induction s generalizing body f with
  | subst e₁ e₂ => exact substFact_sound hwf hB hf
  | linear cs e₁ e₂ => exact linearFact_sound hK hwf hI hL hfs hf
  | lookup ms => exact lookupFact_holds hin hf
  | rangeNat k => exact rangeNatFact_sound hfs hf
  | holdsIn k => exact holdsInFact_sound hfs hf
  | src v s =>
    simp only [stepFact] at hf
    split_ifs at hf with hg
    simp only [honestStepB, Bool.or_eq_true] at hs
    rcases hs with hs | hs
    · rw [← pureSrcFact_of_honest hs] at hf
      exact pureSrcFact_sound hwf hI hL hK hS hfs hg hf
    · exact hT hs hfs hg hf
  | ivlNat k => exact ivlNatFact_sound hwf hL hfs hf
  | ivlExpr ks x lo hi => exact ivlExprFact_sound hwf hI hL hK hfs hf
  | ivlSolve k ks a j lo hi => exact ivlSolveFact_sound hI hwf hfs hf
  | ivlApply k a e lo hi => exact ivlApplyFact_sound hwf hI hL hfs hf
  | ivlLogic ks e => exact ivlLogicFact_sound hfs hf
  | ivlMeet a b => exact ivlMeetFact_sound hfs hf
  | ivlDisjoint a b => exact ivlDisjointFact_sound hfs hf
  | fieldDvd k a b => exact fieldDvdFact_sound hwf hI hfs hf
  | natIvl k => exact natIvlFact_sound hfs hf
  | transport k j => exact transportFact_sound hfs hf
  | natComp k j => exact natCompFact_sound hwf hI hL hK hfs hf
  | natBool p => exact natBoolFact_holds heq hf
  | natLin k ks => exact natLinFact_sound hwf hI hL hK hfs hf
  | liftConst k a => exact liftConstFact_sound hwf hI hL hK hfs hf
  | lift k a b => exact liftFact_sound hwf hI hL hK hfs hf
  | digits k ds T => exact digitsFact_sound hwf hI hL hK hfs hf
  | linop s => exact linopFact_sound hwf hI hL hK hfs hf
  | hyp q =>
    simp only [stepFact] at hf
    split_ifs at hf with hq
    cases hf
    exact hpreds q hq.1
  | inDom d s ih =>
    simp only [stepFact] at hf
    exact ih (by simpa [honestStepB] using hs) hf
  | _ => simp [honestStepB] at hs

/-- **The facts of honest steps hold** at the reader of `stepFact_honest`. -/
theorem runSteps_honest (hwf : ir.WellFormed) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
    {rd : ir.Valuation I}
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0))
    {sr : List (ℕ × ℕ)}
    (hS : ∀ vN ∈ sr, ∀ i < (ir.value vN.1).size,
      ∃ n < vN.2, rd vN.1 i = ((n : ℕ) : (I (ir.valueField vN.1)).K))
    (hB : ir.BoundReads rd)
    (hpreds : ∀ q < ir.predicates.length, ir.HoldsWith rd (ir.predicate q).body)
    (hin : ∀ t < ir.tables.length, ∀ g < ir.groupCountOf t, ir.NeedlesIn rd t g)
    (hT : ∀ {fs : List Fact} {d v : ℕ} {s : IvlSrc} {f : Fact}, typedSrcB s = true →
      (∀ f ∈ fs, f.HoldsWith ir rd) → ir.srcGuard d v = true → ir.srcFact primeNodes sr fs d v s = some f → f.HoldsWith ir rd)
    {ctx : DerivCtx} {self pid : ℕ} {body : PredBody} :
    ∀ {fs : List Fact} {ss : List Step} {fs' : List Fact},
      (∀ f ∈ fs, f.HoldsWith ir rd) → ss.all honestStepB = true →
      ir.runSteps primeNodes sr ctx self pid body fs ss = some fs' → ∀ f ∈ fs', f.HoldsWith ir rd
  | fs, [], fs', h0, _, hr => by
    simp only [runSteps, Option.some.injEq] at hr
    subst hr
    exact h0
  | fs, s :: ss, fs', h0, hall, hr => by
    simp only [runSteps, Option.bind_eq_some_iff] at hr
    obtain ⟨f, hf, hr⟩ := hr
    simp only [List.all_cons, Bool.and_eq_true] at hall
    refine runSteps_honest hwf hI hL hK hS hB hpreds hin hT (fun g hg => ?_) hall.2 hr
    rcases List.mem_append.1 hg with hg | hg
    · exact h0 g hg
    · rw [List.mem_singleton.1 hg]
      exact stepFact_honest hwf hI hL hK hS hB hpreds hin hT h0 hall.1 hf

/-- **A shared entry of honest steps that checks has its fact** at the reader of
`stepFact_honest`. -/
theorem entryB_honest (hwf : ir.WellFormed) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
    {rd : ir.Valuation I}
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0))
    {sr : List (ℕ × ℕ)}
    (hS : ∀ vN ∈ sr, ∀ i < (ir.value vN.1).size,
      ∃ n < vN.2, rd vN.1 i = ((n : ℕ) : (I (ir.valueField vN.1)).K))
    (hB : ir.BoundReads rd)
    (hpreds : ∀ q < ir.predicates.length, ir.HoldsWith rd (ir.predicate q).body)
    (hin : ∀ t < ir.tables.length, ∀ g < ir.groupCountOf t, ir.NeedlesIn rd t g)
    (hT : ∀ {fs : List Fact} {d v : ℕ} {s : IvlSrc} {f : Fact}, typedSrcB s = true →
      (∀ f ∈ fs, f.HoldsWith ir rd) → ir.srcGuard d v = true → ir.srcFact primeNodes sr fs d v s = some f → f.HoldsWith ir rd)
    {ctx : DerivCtx} {k : ℕ} {en : SharedEntry} (hall : en.steps.all honestStepB = true)
    (hd : ir.entryB primeNodes sr ctx k en = true) : en.fact.HoldsWith ir rd := by
  unfold entryB at hd
  split at hd
  · rename_i fs hfs
    have h1 := runSteps_honest hwf hI hL hK hS hB hpreds hin hT
      (fun _ h => absurd h List.not_mem_nil) hall hfs
    cases hl : fs.getLast? with
    | none => rw [hl] at hd; cases hd
    | some g =>
      rw [hl] at hd
      simp only [Option.map_some, Option.getD_some] at hd
      rw [← Fact.eq_of_beq hd]
      exact h1 _ (List.mem_of_getLast? hl)
  · cases hd

/-- **A cited interval is a checked shared entry of honest steps** (`citesIvlB`). -/
theorem exists_of_citesIvlB {sh : List SharedEntry} {d : ℕ} {x : Expr} :
    ∀ {ss : List Step}, citesIvlB sh d x ss = true →
      ∃ (k : ℕ) (en : SharedEntry) (lo hi : ℤ), sh[k]? = some en ∧ en.fact = .ivl d x lo hi ∧ en.steps.all honestStepB = true
  | [], h => by simp [citesIvlB] at h
  | s :: ss, h => by
    cases s with
    | fact k =>
      simp only [citesIvlB, Bool.or_eq_true] at h
      rcases h with h | h
      · split at h
        · rename_i en hen
          simp only [Bool.and_eq_true] at h
          obtain ⟨h1, h2⟩ := h
          split at h1
          · rename_i d' x' lo hi hf
            simp only [Bool.and_eq_true, beq_iff_eq] at h1
            obtain ⟨rfl, hx⟩ := h1
            obtain rfl := Expr.eq_of_beq hx
            exact ⟨k, en, lo, hi, hen, hf, h2⟩
          · cases h1
        · cases h
      · exact exists_of_citesIvlB (ss := ss) h
    | _ => exact exists_of_citesIvlB (ss := ss) (by simpa [citesIvlB] using h)

/-- **Completeness of the realized program, from valid derivations**: in a sampled environment
whose bound values read their expressions (`hB`) and where the value ranges `sr` hold (`hS`), where
the program holds, every group's histograms count its needles, the two-sided lookups' digits are
below their bases and the MACs' tags are honest, the realized program holds. -/
theorem realizedAt_of_honest_derivs (hwf : ir.WellFormed) {sr : List (ℕ × ℕ)} {D : Derivations}
    (hv : ir.DerivationsValid primeNodes sr D) (hI : I.Registered ir)
    (hL : I.Lawful ir primeNodes) {e : ir.Env I} (he : Env.Sampled ir e)
    (hsat : ir.SatAt e) (hh : ir.HistogramsCount e) (hd : ir.DigitsBelow (ir.reader e))
    (hm : ir.MacsHonest e)
    (hS : ∀ vN ∈ sr, ∀ i < (ir.value vN.1).size,
      ∃ n < vN.2, ir.reader e vN.1 i = ((n : ℕ) : (I (ir.valueField vN.1)).K))
    (hB : ir.BoundReads (ir.reader e)) :
    ir.RealizedAt e := by
  have hpreds : ∀ q < ir.predicates.length, ir.HoldsWith (ir.reader e) (ir.predicate q).body :=
    fun q hq => hsat.preds _ (predicate_mem hq)
  have hin : ∀ t < ir.tables.length, ∀ g < ir.groupCountOf t, ir.NeedlesIn (ir.reader e) t g :=
    fun t ht g hg => groupNeedles_inRows_core hwf hI hL hv.tables hv.lookups ht hg hsat.leafFacts
      hpreds hd
  have hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      ir.reader e v i = (I (ir.valueField v)).decode (es.getD i 0) :=
    fun _ _ hk i => reader_of_constant e hk i
  have hcite : ∀ {d : ℕ} {x : Expr} {ss : List Step}, citesIvlB D.shared d x ss = true →
      ∃ lo hi, Fact.HoldsWith ir (ir.reader e) (.ivl d x lo hi) := by
    intro d x ss h
    obtain ⟨k, en, lo, hi, hen, hf, hall⟩ := exists_of_citesIvlB h
    have hk : k < D.shared.length := (List.getElem?_eq_some_iff.1 hen).1
    have hc := hv.shared k hk
    rw [List.getD_eq_getElem?_getD, hen, Option.getD_some] at hc
    have := entryB_honest hwf hI hL hK hS hB hpreds hin
      (fun hs hfs hg hf => srcFact_typed_sound hwf hI hL hsat.types hs
        (fun p hp _ => hsat.preds p hp) hfs hg hf) hall hc
    rw [hf] at this
    exact ⟨lo, hi, this⟩
  refine ⟨fun p hp _ => hsat.preds p hp, fun p hp d lhs rhs real hb => ?_, fun t ht g hg => ?_,
    hsat.types, fun p hp _ _ _ _ _ _ hb hn hx => (hm.tag p hp _ _ _ _ _ _ hb hn).hosted hx⟩
  · obtain ⟨pid, hpid, rfl⟩ := exists_index_of_mem hp
    have hmc := hv.mods pid hpid
    have hb' : (ir.predicate pid).body = .mod d 0 lhs rhs real := hb
    rw [hb'] at hmc
    simp only [modCiteB, bne_self_eq_false, Bool.false_or, Bool.and_eq_true] at hmc
    obtain ⟨⟨lo, hi, ha⟩, ⟨lo', hi', hb2⟩⟩ := And.intro (hcite hmc.1) (hcite hmc.2)
    have hpo := hwf.predicates _ hp
    rw [hb] at hpo
    have hlen : ir.exprLen lhs = ir.exprLen rhs := hpo.2
    have hs := hsat.preds _ hp
    rw [hb] at hs
    intro i hi'
    have h1 := hs i hi'
    rw [Nat.cast_zero, zero_dvd_iff, sub_eq_zero] at h1
    rw [← (ha i hi').2.2, ← (hb2 i (hlen ▸ hi')).2.2, h1]
  · have := charP_field hI (hv.tables t ht).field
    have hin' := hin t ht g hg
    have hc := hh t ht g hg
    unfold LogupHolds logupAt
    unfold honestCounts at hc
    rcases hrows : (ir.table t).rows with T | cols | e'
    · have hr := isRange_of_rows hrows
      simp only [hrows] at hc ⊢
      exact rangeArgument_complete le_rfl
        (IntLift.finCast_injective (((hv.tables t ht).tmax hr).trans (hv.tables t ht).char.le))
        (alpha_notMem_tableValues (hv.tables t ht) hr hI he)
        ((needlesIn_iff_inTable hr _ g).1 hin') fun j => congrFun hc j
    · simp only [hrows] at hc ⊢
      exact committedArgument_complete _ hin' fun j => congrFun hc j
    · simp only [hrows] at hc ⊢
      exact committedArgument_complete _ hin' fun j => congrFun hc j

end

end GordieHowe.RealizedProgram
