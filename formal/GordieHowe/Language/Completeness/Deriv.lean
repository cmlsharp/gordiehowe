-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Completeness.MacCheck
public import GordieHowe.Language.Completeness.CommDigits
public import GordieHowe.Language.Completeness.Spectral
public import GordieHowe.Language.Realizations.Derivation
public import GordieHowe.Language.Realizations.Derivation.Pure
public import GordieHowe.Language.Honest.Check

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
  holds (`macRow`), and so does the tail of a MAC check over a field of characteristic `2`
  (`twoTail`); the Boolean check of a pad copy holds (`padBool`); a digit lookup
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
-/

namespace GordieHowe.RealizedProgram

open Export Range IOP

deriving instance Repr for MacSite

/-- **A step of a completeness derivation**: premises are indices into the facts of the earlier
steps; program items are ids. -/
inductive CStep where
  /-- A soundness step whose rule reads only its premises and the program (`pureStepFact`). -/
  | pure (s : Step)
  /-- The fact `k` is the body of the derivation's predicate (`concludeFact`). -/
  | conclude (k : ℕ)
  /-- The derivation's predicate is a source predicate, and holds. -/
  | source
  /-- The derivation's predicate is the quotient's `in` of the one-digit `mod_q` `m`, whose honest
  quotient lies in its range (`oneDigitQuotAtB` at the source values' intervals). -/
  | quotIn (m : ℕ)
  /-- The derivation's predicate is the reconstruction or top row of the two-sided or digit lookup
  `p`, whose digits are generated as its digits (`digitRowB`). -/
  | digitRow (p : ℕ)
  /-- The derivation's predicate is a predicate of the MAC of the MAC site `st` (`macRoleCB`), whose
  MAC, tail (a grouped, a one-digit or an ungrouped digit tail) and interval facts check
  (`macBaseCB`, `macTailCB`, `macIvlB`). -/
  | macRow (st : MacSite)
  /-- The derivation's predicate is the Boolean check of a pad copy (`padCopyBoolB`). -/
  | padBool
  /-- The derivation's predicate is the digit lookup whose record is quotient digit `j` of the
  committed-digits `mod_q` `m`, its digits generated as committed digits (`commLookupCB`), `m` with
  its honest-quotient facts (`commModCB`). -/
  | commIn (m j : ℕ)
  /-- The derivation's predicate is the field equation of the committed-digits `mod_q` `m`, whose
  quotient digit `j` is the record of the lookup `lks[j]` (`commRowCB`). -/
  | commRow (m : ℕ) (lks : List ℕ)
  /-- The body of predicate `q` holds: `q`'s derivation has a smaller rank. -/
  | hyp (q : ℕ)
  /-- The derivation's predicate is the products predicate of the spectrally realized convolution
  `k` of `RealizedProgram.convs`, whose honest facts check (`specHonestCB`). -/
  | specProd (k : ℕ)
  /-- The derivation's predicate realizes the field equation of the source predicate `m` through
  the spectrally realized convolutions (`specRowCB`). -/
  | specRow (m : ℕ)
  /-- The derivation's predicate is the field equation of a source field-form `mod_q`
  (`fieldRowRealB`). -/
  | fieldRow
  /-- The derivation's predicate is the tail of the MAC check over a field of characteristic `2` of
  the MAC site `st` (`twoTail`), whose facts check (`twoMacCB`). -/
  | twoTail (st : MacSite)
  deriving Repr, Inhabited

/-- **The completeness derivations of a program**: one per predicate (aligned with the
predicates), and the predicates' ranks packed into one natural (`packRanks`, read by `rankOf`), so
reading a rank costs one shift. -/
structure CDerivations where
  /-- One derivation per predicate. -/
  derivs : List (List CStep)
  /-- The predicates' ranks, packed. -/
  ranks : ℕ
  deriving Repr, Inhabited

section

variable (ir : RealizedProgram) {I : Interp}

/-- **Predicate `pr` is a row of the two-sided or digit lookup `p`** whose facts hold at the
generators `G` (`DigitLookupFactsC`): the reconstruction or the top row of a two-sided lookup, the
reconstruction row of a digit lookup. -/
def digitRowB (G : Gens) (p : ℕ) (pr : Predicate) : Bool :=
  match (ir.predicate p).body with
  | .mem d [rec] (.range N) (.lookup r) =>
    decide (ir.DigitLookupFactsC G p d rec N r) &&
      ((r.kind == .twoSided && (ir.reconMatch d rec r pr.body || ir.topMatch d N rec r pr.body)) ||
        (r.kind == .digits && ir.reconMatch d rec r pr.body))
  | _ => false

/-- **The conclusion of a step** of the completeness derivation of predicate `pid` (`pr`, zipped
with the derivations) at rank `self`, with packed ranks `P`, from the facts `fs` of the earlier
steps; `none` when it does not check. -/
def cstepFact (primeNodes : ℕ → List String) (G : Gens) (P self pid : ℕ) (pr : Predicate)
    (fs : List Fact) : CStep → Option Fact
  | .pure s => ir.pureStepFact primeNodes [] pr.body fs s
  | .conclude k => ir.concludeFact fs pid pr.body k
  | .source => if ir.inSource pr = true then some (.holds pid) else none
  | .quotIn m =>
    if ir.oneDigitQuotAtB (ir.srcLeafIvl primeNodes) m pid = true ∧ ir.noGenPredB pr.body = true
    then some (.holds pid) else none
  | .digitRow p =>
    if ir.digitRowB G p pr = true ∧ ir.noGenPredB pr.body = true then some (.holds pid) else none
  | .macRow st =>
    if ir.macBaseCB primeNodes G st = true ∧ ir.macTailCB primeNodes G st = true ∧
        ir.macIvlB primeNodes st = true ∧ ir.macRoleCB primeNodes st pid = true
    then some (.holds pid) else none
  | .padBool =>
    if ir.padCopyBoolB pid = true ∧ ir.noGenPredB pr.body = true then some (.holds pid) else none
  | .commIn m j =>
    if ir.commLookupCB G pid m j = true ∧ ir.commModCB primeNodes m = true ∧
        ir.noGenPredB pr.body = true
    then some (.holds pid) else none
  | .commRow m lks =>
    if ir.commRowCB primeNodes G m lks pr = true ∧ ir.noGenPredB pr.body = true
    then some (.holds pid) else none
  | .hyp q => if q < ir.predicates.length ∧ rankOf P q < self then some (.holds q) else none
  | .specProd k =>
    if (ir.convs[k]?.map (·.products)) = some pid ∧ ir.specHonestCB primeNodes G k = true ∧
        ir.noGenPredB pr.body = true
    then some (.holds pid) else none
  | .specRow m =>
    if ir.specRowCB primeNodes G m pid = true ∧ ir.noGenPredB pr.body = true
    then some (.holds pid) else none
  | .fieldRow =>
    if ir.fieldRowRealB pid = true ∧ ir.noGenPredB pr.body = true then some (.holds pid) else none
  | .twoTail st =>
    if ir.twoMacCB primeNodes G st = true ∧ pid = ir.twoTail st then some (.holds pid) else none

/-- **Run the steps** of a completeness derivation, accumulating their facts. -/
def runCSteps (primeNodes : ℕ → List String) (G : Gens) (P self pid : ℕ) (pr : Predicate) :
    List Fact → List CStep → Option (List Fact)
  | fs, [] => some fs
  | fs, s :: ss =>
    (ir.cstepFact primeNodes G P self pid pr fs s).bind fun f =>
      runCSteps primeNodes G P self pid pr (fs ++ [f]) ss

/-- **The completeness derivation `steps` of predicate `pid` (`pr`) checks** at rank `self`:
every step checks and the last fact is `holds pid`. -/
def cderivStepsB (primeNodes : ℕ → List String) (G : Gens) (P self pid : ℕ) (pr : Predicate)
    (steps : List CStep) : Bool :=
  match ir.runCSteps primeNodes G P self pid pr [] steps with
  | some fs =>
    match fs.getLast? with
    | some (.holds p) => p == pid
    | _ => false
  | none => false

/-- **The completeness derivations `ds` of the predicates `ps` from `pid` on check**, the two
lists zipped. -/
def allCDerivsB (primeNodes : ℕ → List String) (G : Gens) (P : ℕ) :
    ℕ → List Predicate → List (List CStep) → Bool
  | _, [], [] => true
  | pid, pr :: ps, s :: ds =>
    ir.cderivStepsB primeNodes G P (rankOf P pid) pid pr s &&
      allCDerivsB primeNodes G P (pid + 1) ps ds
  | _, _, _ => false

/-- **The checker of the completeness derivations**: one per predicate, each checking at its
rank. -/
def cderivsB (primeNodes : ℕ → List String) (G : Gens) (D : CDerivations) : Bool :=
  ir.allCDerivsB primeNodes G D.ranks 0 ir.predicates D.derivs

variable (I) in
/-- **The facts of a reader the completeness rules read**: the model facts (`DerivModel`), the
constants and the values bound to their digits read as the program states, every source predicate
holds, and the predicates the rules `quotIn`, `digitRow`, `macRow`, `padBool`, `commIn`, `commRow`,
`specProd`, `specRow`, `fieldRow` and `twoTail` conclude hold. -/
structure CEnvFacts (primeNodes : ℕ → List String) (G : Gens) (rd : ir.Valuation I) : Prop where
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
    ir.oneDigitQuotAtB (ir.srcLeafIvl primeNodes) m rid = true → ir.noGenPredB (ir.predicate rid).body = true → ir.HoldsWith rd (ir.predicate rid).body
  /-- The rows of the two-sided and digit lookups hold. -/
  digitRow : ∀ p, ∀ pid < ir.predicates.length, ir.digitRowB G p (ir.predicate pid) = true →
    ir.noGenPredB (ir.predicate pid).body = true → ir.HoldsWith rd (ir.predicate pid).body
  /-- The predicates of the MACs hold. -/
  macRow : ∀ st, ∀ pid < ir.predicates.length, ir.macBaseCB primeNodes G st = true →
    ir.macTailCB primeNodes G st = true → ir.macIvlB primeNodes st = true →
      ir.macRoleCB primeNodes st pid = true →
      ir.HoldsWith rd (ir.predicate pid).body
  /-- The Boolean checks of the pad copies hold. -/
  padBool : ∀ pid < ir.predicates.length, ir.padCopyBoolB pid = true →
    ir.noGenPredB (ir.predicate pid).body = true → ir.HoldsWith rd (ir.predicate pid).body
  /-- The digit lookups whose records are quotient digits of committed-digits `mod_q`s hold. -/
  commIn : ∀ m j, ∀ pid < ir.predicates.length, ir.commLookupCB G pid m j = true →
    ir.commModCB primeNodes m = true → ir.noGenPredB (ir.predicate pid).body = true →
      ir.HoldsWith rd (ir.predicate pid).body
  /-- The field equations of the committed-digits `mod_q`s hold. -/
  commRow : ∀ m lks, ∀ pid < ir.predicates.length,
    ir.commRowCB primeNodes G m lks (ir.predicate pid) = true →
      ir.noGenPredB (ir.predicate pid).body = true → ir.HoldsWith rd (ir.predicate pid).body
  /-- The products predicates of the spectrally realized convolutions with their honest facts
  hold. -/
  specProd : ∀ k cv, ir.convs[k]? = some cv → ir.specHonestCB primeNodes G k = true →
    ir.noGenPredB (ir.predicate cv.products).body = true →
      ir.HoldsWith rd (ir.predicate cv.products).body
  /-- The realizations of the source predicates' field equations through the spectrally realized
  convolutions hold. -/
  specRow : ∀ m, ∀ pid < ir.predicates.length, ir.specRowCB primeNodes G m pid = true →
    ir.noGenPredB (ir.predicate pid).body = true → ir.HoldsWith rd (ir.predicate pid).body
  /-- The field equations of the source field-form `mod_q`s hold. -/
  fieldRow : ∀ pid < ir.predicates.length, ir.fieldRowRealB pid = true →
    ir.noGenPredB (ir.predicate pid).body = true → ir.HoldsWith rd (ir.predicate pid).body
  /-- The tails of the MAC checks over the fields of characteristic `2` hold. -/
  twoTail : ∀ st, ir.twoMacCB primeNodes G st = true →
    ir.HoldsWith rd (ir.predicate (ir.twoTail st)).body

end

/-- **The MAC field decodes the constants `2^j` to the generator's powers** at a MAC site whose
facts hold at the generators `G`: `MacModel.mod` at the tail, the tail's
powers in the MAC field, of its width. -/
theorem MacBaseFactsC.macPow {ir : RealizedProgram} {I : Interp} {primeNodes : ℕ → List String}
    {G : Gens} {st : MacSite} (F : ir.MacBaseFactsC (primeNodes := primeNodes) G st)
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
  {G : Gens}

/-- **Every completeness rule is sound** at a reader with the rules' facts (`hE`), for the
derivation of predicate `pid` (`hpr`), where the predicates of smaller rank hold (`hc`): the step's
fact holds where its premises' do. -/
theorem cstepFact_sound (hE : ir.CEnvFacts I primeNodes G rd) {P self pid : ℕ} {pr : Predicate}
    (hpr : ir.predicate pid = pr) (hpid : pid < ir.predicates.length)
    (hc : ∀ q < ir.predicates.length, rankOf P q < self → ir.HoldsWith rd (ir.predicate q).body)
    {fs : List Fact} (hfs : ∀ f ∈ fs, f.HoldsWith ir rd) {s : CStep} {f : Fact}
    (h : ir.cstepFact primeNodes G P self pid pr fs s = some f) : f.HoldsWith ir rd := by
  subst hpr
  cases s with
  | pure s =>
    exact pureStepFact_sound hE.model hE.const (sr := [])
      (fun _ h => absurd h List.not_mem_nil) hE.bound hfs h
  | conclude k => exact concludeFact_sound hfs rfl h
  | source =>
    simp only [cstepFact] at h
    split_ifs at h with hq
    cases h
    exact hE.source pid hpid hq
  | quotIn m =>
    simp only [cstepFact] at h
    split_ifs at h with hq
    cases h
    exact hE.quotIn m pid hpid hq.1 hq.2
  | digitRow p =>
    simp only [cstepFact] at h
    split_ifs at h with hq
    cases h
    exact hE.digitRow p pid hpid hq.1 hq.2
  | macRow st =>
    simp only [cstepFact] at h
    split_ifs at h with hq
    cases h
    exact hE.macRow st pid hpid hq.1 hq.2.1 hq.2.2.1 hq.2.2.2
  | padBool =>
    simp only [cstepFact] at h
    split_ifs at h with hq
    cases h
    exact hE.padBool pid hpid hq.1 hq.2
  | commIn m j =>
    simp only [cstepFact] at h
    split_ifs at h with hq
    cases h
    exact hE.commIn m j pid hpid hq.1 hq.2.1 hq.2.2
  | commRow m lks =>
    simp only [cstepFact] at h
    split_ifs at h with hq
    cases h
    exact hE.commRow m lks pid hpid hq.1 hq.2
  | hyp q =>
    simp only [cstepFact] at h
    split_ifs at h with hq
    cases h
    exact hc q hq.1 hq.2
  | specProd k =>
    simp only [cstepFact] at h
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
    simp only [cstepFact] at h
    split_ifs at h with hq
    cases h
    exact hE.specRow m pid hpid hq.1 hq.2
  | fieldRow =>
    simp only [cstepFact] at h
    split_ifs at h with hq
    cases h
    exact hE.fieldRow pid hpid hq.1 hq.2
  | twoTail st =>
    simp only [cstepFact] at h
    split_ifs at h with hq
    cases h
    obtain ⟨h2, rfl⟩ := hq
    exact hE.twoTail st h2

/-- **The steps of a completeness derivation that run give facts that hold**, from facts that
hold. -/
theorem runCSteps_sound (hE : ir.CEnvFacts I primeNodes G rd) {P self pid : ℕ} {pr : Predicate}
    (hpr : ir.predicate pid = pr) (hpid : pid < ir.predicates.length)
    (hc : ∀ q < ir.predicates.length, rankOf P q < self → ir.HoldsWith rd (ir.predicate q).body) :
    ∀ {fs : List Fact} {steps : List CStep} {fs' : List Fact},
      (∀ f ∈ fs, f.HoldsWith ir rd) → ir.runCSteps primeNodes G P self pid pr fs steps = some fs' →
        ∀ f ∈ fs', f.HoldsWith ir rd
  | fs, [], fs', h0, hr => by
    simp only [runCSteps, Option.some.injEq] at hr
    subst hr
    exact h0
  | fs, s :: ss, fs', h0, hr => by
    simp only [runCSteps] at hr
    rcases hs : ir.cstepFact primeNodes G P self pid pr fs s with _ | g
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
theorem cderivStepsB_sound (hE : ir.CEnvFacts I primeNodes G rd) {P self pid : ℕ}
    (hpid : pid < ir.predicates.length)
    (hc : ∀ q < ir.predicates.length, rankOf P q < self → ir.HoldsWith rd (ir.predicate q).body)
    {steps : List CStep}
    (hd : ir.cderivStepsB primeNodes G P self pid (ir.predicate pid) steps = true) :
    ir.HoldsWith rd (ir.predicate pid).body := by
  unfold cderivStepsB at hd
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
    {ds : List (List CStep)}, ir.allCDerivsB primeNodes G P pid ps ds = true →
      ds.length = ps.length ∧ ∀ k < ps.length,
        ir.cderivStepsB primeNodes G P (rankOf P (pid + k)) (pid + k) (ps.getD k default)
          (ds.getD k []) = true
  | _, [], [], _ => ⟨rfl, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | _, [], _ :: _, h => by simp [allCDerivsB] at h
  | _, _ :: _, [], h => by simp [allCDerivsB] at h
  | pid, pr :: ps, s :: ds, h => by
    simp only [allCDerivsB, Bool.and_eq_true] at h
    obtain ⟨hlen, hk⟩ := allCDerivsB_sound h.2
    refine ⟨by simp [hlen], fun k hk' => ?_⟩
    rcases k with _ | k
    · simpa using h.1
    · have := hk k (by simpa using hk')
      rw [show pid + (k + 1) = pid + 1 + k by omega]
      simpa using this

/-- **Completeness derivations for every predicate give every predicate** at a reader with the
rules' facts, by induction on the rank. -/
theorem holds_of_cderivs (hE : ir.CEnvFacts I primeNodes G rd) {D : CDerivations}
    (hD : ir.cderivsB primeNodes G D = true) :
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
        rw [Nat.zero_add] at this
        exact cderivStepsB_sound hE hq (heq ▸ ih) this
  exact fun q hq => hgood (rankOf D.ranks q + 1) q hq (Nat.lt_succ_self _)

end Sound

end GordieHowe.RealizedProgram
