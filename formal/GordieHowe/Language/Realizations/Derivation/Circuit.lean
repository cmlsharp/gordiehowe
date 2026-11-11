-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Derivation.Pure
public import GordieHowe.Language.Realizations.ProductEquation

@[expose] public section

/-!
# GordieHowe: the derivations of a GKR circuit's entries

The meaning of a GKR circuit (`GordieHowe.RealizedProgram.CircuitHolds`) is that every entry of
its emission order holds (`GordieHowe.RealizedProgram.EntryHolds`). The emitter's templates
conclude one fact per template instance, the instances following the entries in order. This file
derives each entry's meaning from those facts.

* **The steps** (`GordieHowe.RealizedProgram.circStepFact`): `circuitAssert k` concludes the fact of
  template instance `k`, `inputPremise k` the circuit's input premise `k`, and every other step is
  a reader-generic rule (`GordieHowe.RealizedProgram.pureStepFact`) in the circuit's domain, with
  no value ranges.
* **The final facts an entry accepts** (`GordieHowe.RealizedProgram.entryFactB`): the field equation
  `eq d e e'` of a Boolean check or placed predicate `e = e'` (a field `equal`, or a `mod_q` with
  `q = 0` or in the field form), `real rc` of a realization circuit `rc`, anything for an
  alignment entry. Each acceptance is sound because the fact and the entry's meaning are the same
  proposition (`GordieHowe.RealizedProgram.entryHolds_of_entryFactB`).
* **The checker** (`GordieHowe.RealizedProgram.circDerivsB`): one pass over the entries, the
  instance facts in lockstep: a listed entry takes the last fact of its steps, every other entry its
  own instance's fact.
* **Soundness** (`GordieHowe.RealizedProgram.circDerivsB_sound`): at any reader whose constants read
  their entries and whose bound values read their expressions, where the instances' facts and the
  input premises hold, every entry of the circuit holds.
-/

namespace GordieHowe.RealizedProgram

open Export

section

variable (ir : RealizedProgram)

/-- **The conclusion of a step of a circuit derivation** in domain `d`, from the instance facts
`concl`, the input premises `prem` and the facts `fs` of the earlier steps: `circuitAssert k` is
instance `k`'s fact, `inputPremise k` premise `k`, any other step a reader-generic rule
(`pureStepFact`, no value ranges). -/
def circStepFact (primeNodes : ℕ → List String) (concl prem : List Fact) (d : ℕ) (fs : List Fact) :
    Step → Option Fact
  | .circuitAssert k => concl[k]?
  | .inputPremise k => prem[k]?
  | s => ir.pureStepFact primeNodes [] (entryBody d) fs s

/-- **The facts of a circuit derivation**: one pass over the steps, each step's fact appended. -/
def circRunSteps (primeNodes : ℕ → List String) (concl prem : List Fact) (d : ℕ) :
    List Fact → List Step → Option (List Fact)
  | fs, [] => some fs
  | fs, s :: ss =>
    (ir.circStepFact primeNodes concl prem d fs s).bind fun f =>
      circRunSteps primeNodes concl prem d (fs ++ [f]) ss

/-- **The last fact of a circuit derivation's steps.** -/
def circLastFact (primeNodes : ℕ → List String) (concl prem : List Fact) (d : ℕ)
    (steps : List Step) : Option Fact :=
  (ir.circRunSteps primeNodes concl prem d [] steps).bind List.getLast?

/-- **A final fact a placed predicate of body `b` accepts**: the field equation `eq d e e'` of a
field `equal` `e = e'`, or of a `mod_q` `e ≡ e'` with `q = 0` or in the field form. -/
def placedFactB : PredBody → Fact → Bool
  | .equal d e e' _, f => f.beq (.eq d e e')
  | .mod d q e e' real, f => (Nat.beq q 0 || decide (real.form = .field)) && f.beq (.eq d e e')
  | _, _ => false

/-- **A final fact an entry of a circuit's emission order accepts**: a Boolean check's or placed
predicate's field equation (`placedFactB`), a realization circuit's `real` fact, anything for an
alignment entry. -/
def entryFactB : CircuitEntry → Fact → Bool
  | .typeCheck p, f => placedFactB (ir.predicate p).body f
  | .pred p, f => placedFactB (ir.predicate p).body f
  | .alignment _, _ => true
  | .realization rc, f =>
    match f with
    | .real rc' => decide (rc' = rc)
    | _ => false

/-- **The entries `ens` of a circuit hold by their derivations**, in domain `d`, the instance facts
`cs` in lockstep with the entries, the listed derivations `Δ` sorted by entry, the next listed one
`gap` entries ahead: a listed entry's last fact, every other entry's own instance fact, accepted by
the entry (`entryFactB`). -/
def circEntriesB (primeNodes : ℕ → List String) (concl prem : List Fact) (d : ℕ) :
    ℕ → List CircuitEntry → List Fact → List (ℕ × List Step) → Bool
  | _, [], _, _ => true
  | gap, en :: ens, cs, Δ =>
    match Δ, gap with
    | (k, steps) :: Δ', 0 =>
      match ir.circLastFact primeNodes concl prem d steps with
      | some f =>
        ir.entryFactB en f &&
          circEntriesB primeNodes concl prem d ((Δ'.headD (0, [])).1 - k - 1) ens cs.tail Δ'
      | none => false
    | _, gap =>
      match cs with
      | f :: cs' => ir.entryFactB en f && circEntriesB primeNodes concl prem d (gap - 1) ens cs' Δ
      | [] => false

/-- **The derivations of circuit `c`'s entries check** (`circEntriesB` on its emission order, in its
domain): from the instance facts `concl` (one per entry, in order), the input premises `prem` and
the listed derivations `Δ` (`(entry, steps)`, sorted by entry). -/
def circDerivsB (primeNodes : ℕ → List String) (c : ℕ) (concl prem : List Fact)
    (Δ : List (ℕ × List Step)) : Bool :=
  ir.circEntriesB primeNodes concl prem (ir.circuit c).domain ((Δ.headD (0, [])).1)
    (ir.circuit c).entries concl Δ

end

variable {ir : RealizedProgram} {I : Interp} {primeNodes : ℕ → List String}

/-- **An accepted final fact gives its entry's meaning** at any reader: the fact and the entry's
meaning are the same proposition. -/
theorem entryHolds_of_entryFactB {rd : ir.Valuation I} {en : CircuitEntry} {f : Fact}
    (h : ir.entryFactB en f = true)
    (hf : f.HoldsWith ir rd) : ir.EntryHolds rd en := by
  have placed : ∀ b, placedFactB b f = true → ir.PlacedHolds rd b := by
    intro b hb
    cases b with
    | equal d e e' r =>
      obtain rfl := Fact.eq_of_beq hb
      exact hf
    | mod d q e e' real =>
      simp only [placedFactB, Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq,
        decide_eq_true_eq] at hb
      obtain ⟨hq, hb⟩ := hb
      obtain rfl := Fact.eq_of_beq hb
      simp only [PlacedHolds, hq, ite_true]
      exact hf
    | mem _ _ _ _ => simp [placedFactB] at hb
    | cross _ _ _ _ _ _ => simp [placedFactB] at hb
  cases en with
  | typeCheck p => exact placed _ h
  | pred p => exact placed _ h
  | alignment _ => trivial
  | realization rc =>
    simp only [entryFactB] at h
    split at h
    · obtain rfl := of_decide_eq_true h
      exact hf
    · cases h

/-- **The facts of a circuit derivation hold** where its fact sources do. -/
theorem circRunSteps_sound (hM : ir.DerivModel I primeNodes) {rd : ir.Valuation I}
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0))
    (hB : ir.BoundReads rd) {concl prem : List Fact} {d : ℕ}
    (hc : ∀ (k : ℕ) (f : Fact), concl[k]? = some f → f.HoldsWith ir rd)
    (hp : ∀ (k : ℕ) (f : Fact), prem[k]? = some f → f.HoldsWith ir rd) :
    ∀ {fs : List Fact} {ss : List Step} {fs' : List Fact}, (∀ f ∈ fs, f.HoldsWith ir rd) →
      ir.circRunSteps primeNodes concl prem d fs ss = some fs' → ∀ f ∈ fs', f.HoldsWith ir rd
  | fs, [], fs', h0, hr => by
    simp only [circRunSteps, Option.some.injEq] at hr
    exact hr ▸ h0
  | fs, s :: ss, fs', h0, hr => by
    simp only [circRunSteps, Option.bind_eq_some_iff] at hr
    obtain ⟨f, hf, hr⟩ := hr
    refine circRunSteps_sound hM hK hB hc hp (fun g hg => ?_) hr
    rcases List.mem_append.1 hg with hg | hg
    · exact h0 g hg
    · rw [List.mem_singleton.1 hg]
      cases s with
      | circuitAssert k => exact hc k f (by simpa only [circStepFact] using hf)
      | inputPremise k => exact hp k f (by simpa only [circStepFact] using hf)
      | _ =>
        exact pureStepFact_sound hM hK (sr := []) (fun _ h => absurd h List.not_mem_nil) hB h0
          (by simpa only [circStepFact] using hf)

/-- **`circEntriesB` is sound**: every entry holds, where the instance facts in lockstep (`cs`) and
the fact sources hold. -/
theorem circEntriesB_sound (hM : ir.DerivModel I primeNodes) {rd : ir.Valuation I}
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0))
    (hB : ir.BoundReads rd) {concl prem : List Fact} {d : ℕ}
    (hc : ∀ (k : ℕ) (f : Fact), concl[k]? = some f → f.HoldsWith ir rd)
    (hp : ∀ (k : ℕ) (f : Fact), prem[k]? = some f → f.HoldsWith ir rd) :
    ∀ {gap : ℕ} {ens : List CircuitEntry} {cs : List Fact} {Δ : List (ℕ × List Step)},
      (∀ f ∈ cs, f.HoldsWith ir rd) →
      ir.circEntriesB primeNodes concl prem d gap ens cs Δ = true → ∀ en ∈ ens, ir.EntryHolds rd en
  | _, [], _, _, _, _ => by simp
  | gap, en :: ens, cs, Δ, hcs, h => by
    have hcs' : ∀ f ∈ cs.tail, f.HoldsWith ir rd := fun f hf => hcs f (List.mem_of_mem_tail hf)
    unfold circEntriesB at h
    split at h
    · rename_i k steps Δ'
      split at h
      · rename_i f hl
        simp only [Bool.and_eq_true] at h
        obtain ⟨he, h⟩ := h
        unfold circLastFact at hl
        simp only [Option.bind_eq_some_iff] at hl
        obtain ⟨fs, hfs, hl⟩ := hl
        have hf := circRunSteps_sound hM hK hB hc hp (fun _ h => absurd h List.not_mem_nil) hfs f
          (List.mem_of_getLast? hl)
        intro en' hen'
        rcases List.mem_cons.1 hen' with rfl | hen'
        · exact entryHolds_of_entryFactB he hf
        · exact circEntriesB_sound hM hK hB hc hp hcs' h en' hen'
      · cases h
    · split at h
      · rename_i f cs'
        simp only [Bool.and_eq_true] at h
        obtain ⟨he, h⟩ := h
        intro en' hen'
        rcases List.mem_cons.1 hen' with rfl | hen'
        · exact entryHolds_of_entryFactB he (hcs f (by simp))
        · exact circEntriesB_sound hM hK hB hc hp (fun g hg => hcs g (by simp [hg])) h en' hen'
      · cases h

/-- **`circDerivsB_sound`**: if the derivations of circuit `c`'s entries check, every entry of `c`
holds (`CircuitHolds`) at any reader `rd` whose constants read their entries (`hK`) and whose bound
values read their expressions (`hB`), where every template instance's fact (`hc`) and every input
premise (`hp`) holds. -/
theorem circDerivsB_sound (hM : ir.DerivModel I primeNodes) {rd : ir.Valuation I}
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0))
    (hB : ir.BoundReads rd) {c : ℕ} {concl prem : List Fact} {Δ : List (ℕ × List Step)}
    (hc : ∀ (k : ℕ) (f : Fact), concl[k]? = some f → f.HoldsWith ir rd)
    (hp : ∀ (k : ℕ) (f : Fact), prem[k]? = some f → f.HoldsWith ir rd)
    (h : ir.circDerivsB primeNodes c concl prem Δ = true) : ir.CircuitHolds I c rd := by
  have hcs : ∀ f ∈ concl, f.HoldsWith ir rd := fun f hf => by
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hf
    exact hc k _ (List.getElem?_eq_getElem hk)
  exact circEntriesB_sound hM hK hB hc hp hcs h

end GordieHowe.RealizedProgram
