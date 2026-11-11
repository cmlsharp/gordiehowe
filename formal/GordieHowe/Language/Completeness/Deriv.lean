-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Completeness.MacCheck
public import GordieHowe.Language.Completeness.CommDigits
public import GordieHowe.Language.Completeness.Reader
public import GordieHowe.Language.Completeness.Spectral
public import GordieHowe.Language.Realizations.Derivation
public import GordieHowe.Language.Realizations.Derivation.Pure
public import GordieHowe.Language.Honest.Check
public import GordieHowe.Language.RealizedProgram.StructureCheck
public import GordieHoweNative.Language.Completeness.Deriv

@[expose] public section

/-!
# GordieHowe: completeness derivations

A **completeness derivation** is the compiler's proof that a predicate holds at the honest values,
as a list of steps of a fixed rule set (`GordieHowe.RealizedProgram.CStep`), in the format of the
soundness derivations (`GordieHowe/Language/Realizations/Derivation.lean`): facts
(`GordieHowe.RealizedProgram.Fact`), steps naming their premises by index and program items by id,
one derivation per predicate aligned with the predicates, and ranks (`DerivCtx`) so a derivation
cites only predicates of smaller rank.

* **The rules** (`GordieHowe.RealizedProgram.CStep`): the soundness derivations' rules that read
  only their premises and the program (`pure`, `pureStepFact`) and their conclusion of the
  derivation's predicate (`conclude`); a source predicate holds (`source`); the
  quotient of a one-digit `mod_q` lies in its range (`quotIn`); a row of a two-sided or digit lookup
  whose digits are generated as its digits holds (`digitRow`); a predicate of the MAC of a MAC site
  read at a `macSite` structure record (`macSiteAt`) holds in the role its step names (`macRow`),
  and so does the tail of a MAC check over a field of characteristic `2`
  (`twoTail`); the Boolean check of a pad copy holds (`padBool`); a digit or direct lookup
  whose record is a committed quotient digit holds (`commIn`); the field equation of a
  committed-digits `mod_q` holds (`commRow`); the products predicate of a spectrally realized
  convolution holds (`specProd`), and so does a realization of a source predicate's field equation
  through the convolutions (`specRow`); the field equation of a source field-form `mod_q` holds
  (`fieldRow`); a predicate of smaller rank holds (`hyp`). The rules that read the honest values at
  the source environment (`quotIn`, `digitRow`, `padBool`, `commIn`, `commRow`, `specProd`,
  `specRow`, `fieldRow`) conclude only predicates reading no generated late value.
* **What the rules read** (`GordieHowe.RealizedProgram.CEnvFacts`): the facts of a reader the rules
  are sound at, in the vocabulary of the honest values; the honest environment has them
  (`GordieHowe/Language/Completeness/Honest.lean`).
* **Soundness**: each rule is sound at a reader with those facts (`cstepFact_sound`), a derivation
  that checks gives its predicate (`cderivStepsB_sound`), and derivations for every predicate give
  every predicate (`holds_of_cderivs`), by induction on the rank.

The definitions are in `GordieHoweNative/Language/Completeness/Deriv.lean`
(the compiled library `GordieHoweNative`); this module has their lemmas.
-/

namespace GordieHowe.RealizedProgram

open Export Range IOP

deriving instance Repr for MacSite

section

variable (ir : RealizedProgram) {I : Interp}

variable (I) in
/-- **The facts of a reader the completeness rules read**: the model facts (`DerivModel`), the
constants and the values bound to their digits read as the program states, every source predicate
holds, and the predicates the rules `quotIn`, `digitRow`, `macRow`, `padBool`, `commIn`, `commRow`,
`specProd`, `specRow`, `fieldRow` and `twoTail` conclude hold. -/
structure CEnvFacts (primeNodes : ℕ → List String) (S : Structure) (G : Gens)
    (rd : ir.Valuation I) : Prop where
  /-- The model facts the soundness rules read. -/
  model : ir.DerivModel I primeNodes
  /-- The constants read their entries. -/
  const : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
    rd v i = (I (ir.valueField v)).decode (es.getD i 0)
  /-- The values bound to their digits read their expressions. -/
  bound : ir.BoundReads rd
  /-- Every source predicate holds. -/
  source : ∀ q < ir.predicates.length, ir.inSource (ir.predicate q) = true →
    ir.HoldsWith rd (ir.predicate q).body
  /-- The quotient's `in` of a one-digit `mod_q` holds. -/
  quotIn : ∀ m, ∀ rid < ir.predicates.length,
    ir.oneDigitQuotAtB (ir.srcLeafIvl primeNodes S) m rid = true →
      ir.noGenPredB (ir.predicate rid).body = true → ir.HoldsWith rd (ir.predicate rid).body
  /-- The rows of the two-sided and digit lookups hold. -/
  digitRow : ∀ p, ∀ pid < ir.predicates.length, ir.digitRowB G p (ir.predicate pid) = true →
    ir.noGenPredB (ir.predicate pid).body = true → ir.HoldsWith rd (ir.predicate pid).body
  /-- The predicates of the MACs hold, in every role. -/
  macRow : ∀ st role, ∀ pid < ir.predicates.length, ir.macBaseCB primeNodes S G st = true →
    ir.macTailCB G st = true → ir.macIvlB primeNodes S st = true →
      ir.macRoleAtB primeNodes S st role pid = true →
      ir.HoldsWith rd (ir.predicate pid).body
  /-- The Boolean checks of the pad copies hold. -/
  padBool : ∀ pid < ir.predicates.length, ir.padCopyBoolB pid = true →
    ir.noGenPredB (ir.predicate pid).body = true → ir.HoldsWith rd (ir.predicate pid).body
  /-- The digit and direct lookups whose records are quotient digits of committed-digits
  `mod_q`s hold. -/
  commIn : ∀ m j, ∀ pid < ir.predicates.length, ir.commRecCB G pid m j = true →
    ir.commModCB primeNodes S m = true → ir.noGenPredB (ir.predicate pid).body = true →
      ir.HoldsWith rd (ir.predicate pid).body
  /-- The field equations of the committed-digits `mod_q`s hold. -/
  commRow : ∀ m lks, ∀ pid < ir.predicates.length,
    ir.commRowCB primeNodes S G m lks (ir.predicate pid) = true →
      ir.noGenPredB (ir.predicate pid).body = true → ir.HoldsWith rd (ir.predicate pid).body
  /-- The products predicates of the spectrally realized convolutions with their honest facts
  hold. -/
  specProd : ∀ k cv, ir.convs[k]? = some cv → ir.specHonestCB primeNodes S G k = true →
    ir.noGenPredB (ir.predicate cv.products).body = true →
      ir.HoldsWith rd (ir.predicate cv.products).body
  /-- The realizations of the predicates' field equations through the spectrally realized
  convolutions hold, of a source predicate's, or of a predicate reading no generated late value
  that holds. -/
  specRow : ∀ m, ∀ pid < ir.predicates.length, ir.specRowCB primeNodes S G m pid = true →
    (ir.inSource (ir.predicate m) = true ∨
      (m < ir.predicates.length ∧ ir.noGenPredB (ir.predicate m).body = true ∧
        ir.HoldsWith rd (ir.predicate m).body)) →
    ir.noGenPredB (ir.predicate pid).body = true → ir.HoldsWith rd (ir.predicate pid).body
  /-- The field equations of the source field-form `mod_q`s hold. -/
  fieldRow : ∀ pid < ir.predicates.length, ir.fieldRowRealB pid = true →
    ir.noGenPredB (ir.predicate pid).body = true → ir.HoldsWith rd (ir.predicate pid).body
  /-- The tails of the MAC checks over the fields of characteristic `2` hold. -/
  twoTail : ∀ st, ir.twoMacCB primeNodes G st = true →
    ir.HoldsWith rd (ir.predicate (ir.twoTail st)).body
  /-- The rows of the committed readings of the spectrally realized convolutions with their honest
  facts hold. -/
  specC : ∀ k cv, ir.convs[k]? = some cv → ir.specHonestCB primeNodes S G k = true →
    ∀ kc r, cv.committed = some (kc, r) → ir.noGenPredB (ir.predicate r).body = true →
      ir.HoldsWith rd (ir.predicate r).body

end

/-- **The MAC field decodes the constants `2^j` to the generator's powers** at a MAC site whose
facts hold at the generators `G`: `MacModel.mod` at the tail, the tail's
powers in the MAC field, of its width. -/
theorem MacBaseFactsC.macPow {ir : RealizedProgram} {I : Interp} {primeNodes : ℕ → List String}
    {S : Structure} {G : Gens} {st : MacSite}
    (F : ir.MacBaseFactsC (primeNodes := primeNodes) S G st)
    (hM : I.MacModel ir) :
    ∀ j < (ir.macCross st.pid).real.width, (I (ir.macCross st.pid).real.macField).decode (2 ^ j) =
      (I (ir.macCross st.pid).real.macField).decode 2 ^ j := by
  intro j hj
  obtain ⟨tb, htb⟩ := Expr.eq_leaf_of_isLeaf F.tailR
  have hb := F.hbt
  rw [eq_of_macUnits? F.hu, htb] at hb
  have hF := (hM.mod _ F.tail_lt _ _ _ _ _ _ _ _ _ hb).1
  have h := hF.decodePow j (F.width ▸ hj)
  rw [F.powField] at h
  exact h

section Sound

variable {ir : RealizedProgram} {I : Interp} {primeNodes : ℕ → List String} {rd : ir.Valuation I}
  {S : Structure} {G : Gens}

/-- **Every completeness rule is sound** at a reader with the rules' facts (`hE`), for the
derivation of predicate `pid` (`hpr`), where the predicates of smaller rank hold (`hc`): the step's
fact holds where its premises' do. -/
theorem cstepFact_sound (hE : ir.CEnvFacts I primeNodes S G rd) {P self pid : ℕ}
    {pr : Predicate}
    (hpr : ir.predicate pid = pr) (hpid : pid < ir.predicates.length)
    (hc : ∀ q < ir.predicates.length, rankOf P q < self → ir.HoldsWith rd (ir.predicate q).body)
    {fs : List Fact} (hfs : ∀ f ∈ fs, f.HoldsWith ir rd) {s : CStep} {f : Fact}
    (h : ir.cstepFact primeNodes S G P self pid pr fs s = some f) : f.HoldsWith ir rd := by
  subst hpr
  cases s with
  | pure s =>
    exact pureStepFact_sound hE.model hE.const (sr := [])
      (fun _ h => absurd h List.not_mem_nil) hE.bound hfs h
  | conclude k => exact concludeFact_sound hfs rfl h
  | source =>
    simp only [cstepFact, CReader.cstepFact, CReader.ofProgram_nPreds,
      CReader.ofProgram_site, CReader.ofProgram_commMod] at h
    split_ifs at h with hq
    cases h
    exact hE.source pid hpid hq
  | quotIn m =>
    simp only [cstepFact, CReader.cstepFact, CReader.ofProgram_nPreds,
      CReader.ofProgram_site, CReader.ofProgram_commMod] at h
    split_ifs at h with hq
    cases h
    exact hE.quotIn m pid hpid hq.1 hq.2
  | digitRow p =>
    simp only [cstepFact, CReader.cstepFact, CReader.ofProgram_nPreds,
      CReader.ofProgram_site, CReader.ofProgram_commMod] at h
    split_ifs at h with hq
    cases h
    exact hE.digitRow p pid hpid hq.1 hq.2
  | macRow g i role =>
    simp only [cstepFact, CReader.cstepFact, CReader.ofProgram_nPreds,
      CReader.ofProgram_site, CReader.ofProgram_commMod] at h
    split at h
    · rename_i st hst
      split_ifs at h with hq
      cases h
      simp only [siteCheckAt_of_some hst] at hq
      exact hE.macRow st role pid hpid hq.1 hq.2.1 hq.2.2.1 hq.2.2.2
    · cases h
  | padBool =>
    simp only [cstepFact, CReader.cstepFact, CReader.ofProgram_nPreds,
      CReader.ofProgram_site, CReader.ofProgram_commMod] at h
    split_ifs at h with hq
    cases h
    exact hE.padBool pid hpid hq.1 hq.2
  | commIn m j =>
    simp only [cstepFact, CReader.cstepFact, CReader.ofProgram_nPreds,
      CReader.ofProgram_site, CReader.ofProgram_commMod] at h
    split_ifs at h with hq
    cases h
    exact hE.commIn m j pid hpid hq.1 hq.2.1 hq.2.2
  | commRow m lks =>
    simp only [cstepFact, CReader.cstepFact, CReader.ofProgram_nPreds,
      CReader.ofProgram_site, CReader.ofProgram_commMod] at h
    split_ifs at h with hq
    cases h
    exact hE.commRow m lks pid hpid hq.1 hq.2
  | hyp q =>
    simp only [cstepFact, CReader.cstepFact, CReader.ofProgram_nPreds,
      CReader.ofProgram_site, CReader.ofProgram_commMod] at h
    split_ifs at h with hq
    cases h
    exact hc q hq.1 hq.2
  | specProd k =>
    simp only [cstepFact, CReader.cstepFact, CReader.ofProgram_nPreds,
      CReader.ofProgram_site, CReader.ofProgram_commMod] at h
    split_ifs at h with hq
    cases h
    obtain ⟨hk, hs, hn⟩ := hq
    rcases hcv : ir.convs[k]? with _ | cv
    · rw [hcv] at hk
      cases hk
    · rw [hcv, Option.map_some, Option.some.injEq] at hk
      subst hk
      exact hE.specProd k cv hcv hs hn
  | specRow m =>
    simp only [cstepFact, CReader.cstepFact, CReader.ofProgram_nPreds,
      CReader.ofProgram_site, CReader.ofProgram_commMod] at h
    split_ifs at h with hq
    cases h
    obtain ⟨hs, hm, hn⟩ := hq
    exact hE.specRow m pid hpid hs
      (hm.imp id fun ⟨hl, hr, hg⟩ => ⟨hl, hg, hc m hl hr⟩) hn
  | fieldRow =>
    simp only [cstepFact, CReader.cstepFact, CReader.ofProgram_nPreds,
      CReader.ofProgram_site, CReader.ofProgram_commMod] at h
    split_ifs at h with hq
    cases h
    exact hE.fieldRow pid hpid hq.1 hq.2
  | twoTail g i =>
    simp only [cstepFact, CReader.cstepFact, CReader.ofProgram_nPreds,
      CReader.ofProgram_site, CReader.ofProgram_commMod] at h
    split at h
    · rename_i st hst
      split_ifs at h with hq
      cases h
      simp only [siteCheckAt_of_some hst] at hq
      obtain ⟨h2, rfl⟩ := hq
      exact hE.twoTail st h2
    · cases h
  | specC k =>
    simp only [cstepFact, CReader.cstepFact, CReader.ofProgram_nPreds,
      CReader.ofProgram_site, CReader.ofProgram_commMod] at h
    split_ifs at h with hq
    cases h
    obtain ⟨hk, hs, hn⟩ := hq
    rcases hcv : ir.convs[k]? with _ | cv
    · rw [hcv] at hk
      cases hk
    · rw [hcv, Option.bind_some] at hk
      rcases hcm : cv.committed with _ | ⟨kc, r⟩
      · rw [hcm] at hk
        cases hk
      · rw [hcm, Option.map_some, Option.some.injEq] at hk
        subst hk
        exact hE.specC k cv hcv hs kc _ hcm hn

/-- **The steps of a completeness derivation that run give facts that hold**, from facts that
hold. -/
theorem runCSteps_sound (hE : ir.CEnvFacts I primeNodes S G rd) {P self pid : ℕ}
    {pr : Predicate}
    (hpr : ir.predicate pid = pr) (hpid : pid < ir.predicates.length)
    (hc : ∀ q < ir.predicates.length, rankOf P q < self → ir.HoldsWith rd (ir.predicate q).body) :
    ∀ {fs : List Fact} {steps : List CStep} {fs' : List Fact},
      (∀ f ∈ fs, f.HoldsWith ir rd) →
        ir.runCSteps primeNodes S G P self pid pr fs steps = some fs' →
        ∀ f ∈ fs', f.HoldsWith ir rd
  | fs, [], fs', h0, hr => by
    simp only [runCSteps, CReader.runCSteps, Option.some.injEq] at hr
    subst hr
    exact h0
  | fs, s :: ss, fs', h0, hr => by
    simp only [runCSteps, CReader.runCSteps] at hr
    rcases hs : @CReader.cstepFact ir (CReader.ofProgram ir primeNodes S G) primeNodes S G P self
      pid pr fs s with _ | g
    · rw [hs] at hr
      cases hr
    · rw [hs, Option.bind_some] at hr
      refine runCSteps_sound hE hpr hpid hc (fun f hf => ?_) hr
      rcases List.mem_append.1 hf with hf | hf
      · exact h0 f hf
      · rw [List.mem_singleton.1 hf]
        exact cstepFact_sound hE hpr hpid hc h0 hs

/-- **A completeness derivation that checks gives its predicate**, where the predicates of smaller
rank hold. -/
theorem cderivStepsB_sound (hE : ir.CEnvFacts I primeNodes S G rd) {P self pid : ℕ}
    (hpid : pid < ir.predicates.length)
    (hc : ∀ q < ir.predicates.length, rankOf P q < self → ir.HoldsWith rd (ir.predicate q).body)
    {steps : List CStep}
    (hd : ir.cderivStepsB primeNodes S G P self pid (ir.predicate pid) steps = true) :
    ir.HoldsWith rd (ir.predicate pid).body := by
  unfold cderivStepsB CReader.cderivStepsB at hd
  split at hd
  · rename_i fs hfs
    split at hd
    · rename_i p hl
      obtain rfl := beq_iff_eq.1 hd
      exact runCSteps_sound hE rfl hpid hc (fun _ h => absurd h List.not_mem_nil) hfs _
        (List.mem_of_getLast? hl)
    · cases hd
  · cases hd

/-- **The zipped checker checks each predicate's derivation.** -/
theorem allCDerivsB_sound {P : ℕ} : ∀ {pid : ℕ} {ps : List Predicate}
    {ds : List (List CStep)}, ir.allCDerivsB primeNodes S G P pid ps ds = true →
      ds.length = ps.length ∧ ∀ k < ps.length,
        ir.cderivStepsB primeNodes S G P (rankOf P (pid + k)) (pid + k) (ps.getD k default)
          (ds.getD k []) = true
  | _, [], [], _ => ⟨rfl, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | _, [], _ :: _, h => by simp [allCDerivsB, CReader.allCDerivsB] at h
  | _, _ :: _, [], h => by simp [allCDerivsB, CReader.allCDerivsB] at h
  | pid, pr :: ps, s :: ds, h => by
    simp only [allCDerivsB, CReader.allCDerivsB, Bool.and_eq_true] at h
    obtain ⟨hlen, hk⟩ := allCDerivsB_sound h.2
    refine ⟨by simp [hlen], fun k hk' => ?_⟩
    rcases k with _ | k
    · exact h.1
    · have := hk k (by simpa using hk')
      rw [show pid + (k + 1) = pid + 1 + k by omega]
      simpa using this

/-- **Completeness derivations for every predicate give every predicate** at a reader with the
rules' facts, by induction on the rank. -/
theorem holds_of_cderivs (hE : ir.CEnvFacts I primeNodes S G rd)
    {D : CDerivations} (hD : ir.cderivsB primeNodes S G D = true) :
    ∀ q < ir.predicates.length, ir.HoldsWith rd (ir.predicate q).body := by
  obtain ⟨-, hk⟩ := allCDerivsB_sound hD
  have hgood : ∀ n, ∀ q < ir.predicates.length, rankOf D.ranks q < n →
      ir.HoldsWith rd (ir.predicate q).body := by
    intro n
    induction n with
    | zero => exact fun _ _ h => absurd h (Nat.not_lt_zero _)
    | succ n ih =>
      intro q hq hlt
      rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with hlt | heq
      · exact ih q hq hlt
      · have := hk q hq
        rw [Nat.zero_add, ← predicate_eq_getD] at this
        exact cderivStepsB_sound hE hq (heq ▸ ih) this
  exact fun q hq => hgood (rankOf D.ranks q + 1) q hq (Nat.lt_succ_self _)

end Sound

end GordieHowe.RealizedProgram
