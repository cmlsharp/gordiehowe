-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Derivation

@[expose] public section

/-!
# GordieHowe: the reader-generic rules of derivations

The rules of a derivation whose soundness reads only their premises' facts and the program's
structure, at any reader (`GordieHowe.RealizedProgram.pureStepFact`,
`GordieHowe.RealizedProgram.pureStepFact_sound`): no realized program (`RealizedAt`), no sampled
environment, no cited predicate. The completeness track runs them at the honest environment.

* **The rules**: `subst`, `linear`, `rangeNat`, `ivlNat`, `ivlExpr`, `ivlSolve`, `ivlApply`,
  `ivlLogic`, `ivlMeet`, `ivlDisjoint`, `fieldDvd`, `natIvl`, `transport`, `natComp`, `natLin`,
  `liftConst`, `lift`, `digits`, `linop`, `inDom`, and `src` from a constant's entries, a declared
  bound or a `nat` premise (`pureSrcFact`). Every other step concludes nothing here: `src` from a
  prime-subfield read, an opaque `Bit` value, a shift or root equations reads the realized
  program's facts (`RealizedAt`); `realized`, `natBool`, `lookup`, `holdsIn`, `mac`, `congr`,
  `conclude`, `hyp`, `fact` and `groupedMod` read the realized program or the cited predicates.
* **The model**: the program's structure (`DerivModel`), constants reading their entries (`hK`,
  which holds at the reader of every environment, `reader_of_constant`), the value ranges `sr`
  (`hS`) and the bound values' readings (`hB`) at the reader.
-/

namespace GordieHowe.RealizedProgram

open Export

section

variable (ir : RealizedProgram)

/-- **The reader-generic interval sources**: a constant's entries, a declared bound, a `nat`
premise (`srcFact`); none for the others. -/
def pureSrcFact (primeNodes : ℕ → List String) (sr : List (ℕ × ℕ)) (fs : List Fact) (d v : ℕ) :
    IvlSrc → Option Fact
  | .const => ir.srcFact primeNodes sr fs d v .const
  | .declared k => ir.srcFact primeNodes sr fs d v (.declared k)
  | .nat k => ir.srcFact primeNodes sr fs d v (.nat k)
  | _ => none

/-- **The conclusion of a reader-generic step** (`stepFact` on the rules whose soundness reads only
their premises), for a derivation of body `body` from the facts `fs`; `none` for every other
step. -/
def pureStepFact (primeNodes : ℕ → List String) (sr : List (ℕ × ℕ)) (body : PredBody)
    (fs : List Fact) : Step → Option Fact
  | .subst e₁ e₂ => ir.substFact body.dom e₁ e₂
  | .linear cs e₁ e₂ => ir.linearFact fs body.dom cs e₁ e₂
  | .rangeNat k => ir.rangeNatFact fs body.dom k
  | .src v s =>
    if ir.srcGuard body.dom v = true then ir.pureSrcFact primeNodes sr fs body.dom v s else none
  | .ivlNat k => ir.ivlNatFact fs body.dom k
  | .ivlExpr ks x lo hi => ir.ivlExprFact fs body.dom ks x lo hi
  | .ivlSolve k ks a j lo hi => ir.ivlSolveFact fs body.dom k ks a j lo hi
  | .ivlApply k a e lo hi => ir.ivlApplyFact fs body.dom k a e lo hi
  | .ivlLogic ks e => ir.ivlLogicFact fs body.dom ks e
  | .ivlMeet a b => ivlMeetFact fs a b
  | .ivlDisjoint a b => ir.ivlDisjointFact fs body.dom a b
  | .fieldDvd k a b => ir.fieldDvdFact fs body.dom k a b
  | .natIvl k => natIvlFact fs k
  | .transport k j => ir.transportFact fs k j
  | .natComp k j => ir.natCompFact fs body.dom k j
  | .natLin k ks => ir.natLinFact fs body.dom k ks
  | .liftConst k a => ir.liftConstFact fs body k a
  | .lift k a b => ir.liftFact fs k a b
  | .digits k ds T => ir.digitsFact fs body.dom k ds T
  | .linop s => ir.linopFact fs body.dom s
  | .inDom d s => pureStepFact primeNodes sr (entryBody d) fs s
  | _ => none

end

variable {ir : RealizedProgram} {I : Interp} {primeNodes : ℕ → List String}

/-- **`pureSrcFact_sound`**: the reader-generic interval sources are sound at any reader whose
constants read their entries (`hK`) and whose ranged values lie in their ranges (`hS`). -/
theorem pureSrcFact_sound (hwf : ir.WellFormed) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
    {sr : List (ℕ × ℕ)} {rd : ir.Valuation I}
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0))
    (hS : ∀ vN ∈ sr, ∀ i < (ir.value vN.1).size,
      ∃ n < vN.2, rd vN.1 i = ((n : ℕ) : (I (ir.valueField vN.1)).K))
    {fs : List Fact} (hfs : ∀ f ∈ fs, f.HoldsWith ir rd) {d v : ℕ} {s : IvlSrc} {f : Fact}
    (hg : ir.srcGuard d v = true) (hf : ir.pureSrcFact primeNodes sr fs d v s = some f) :
    f.HoldsWith ir rd := by
  unfold srcGuard at hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨⟨hv, hd⟩, hfd⟩, hp2⟩ := hg
  have hf' := domainField_lt hwf hd
  have hchar := charP_field hI hf'
  cases s with
  | const =>
    simp only [pureSrcFact, srcFact] at hf
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
        | some c => exact of_decide_eq_true (List.all_eq_true.1 hall c (List.mem_of_getElem? hes))
      have hint : ir.evalIntWith rd d (.leaf v) i =
          centeredZ (ir.charOf (ir.domainField d)) (es.getD i 0) := by
        change ir.intOf rd v i = _
        rw [intOf_of_constant _ hk, FieldInterp.centered_eq, hI.characteristic _ (hfd ▸ hf'), hfd]
      have hmem := mem_constIvlOf (p := ir.charOf (ir.domainField d)) (n := (ir.value v).size)
        (by omega) es hi
      rw [hint]
      refine ⟨hmem.1, hmem.2, ?_⟩
      change _ = castElt (rd v i)
      rw [hK v es hk i, castElt_decode' hfd, hL.decode_natCast _ hf' _ hc, centeredZ_cast]
    · cases hf
  | declared k =>
    simp only [pureSrcFact, srcFact] at hf
    split at hf
    · rename_i w N hk
      split_ifs at hf with hc
      cases hf
      obtain ⟨rfl, hpl, -, hN⟩ := hc
      exact ivl_of_natRead hwf hI hL hd hfd hpl hN (hS _ (List.mem_of_getElem? hk))
    · cases hf
  | nat k =>
    simp only [pureSrcFact, srcFact] at hf
    split at hf
    · rename_i d' x N hk
      split_ifs at hf with hc
      cases hf
      obtain ⟨rfl, hx, hpl, -, hN⟩ := hc
      obtain rfl := Expr.eq_of_beq hx
      have hn : Fact.HoldsWith ir rd (.nat d' (.leaf v) N) := hfs _ (List.mem_of_getElem? hk)
      refine ivl_of_natRead hwf hI hL hd hfd hpl hN fun i hi => ?_
      obtain ⟨n, hnN, hn'⟩ := hn i hi
      exact ⟨n, hnN, (eq_natCast_of_castElt hfd hn'.symm)⟩
    · cases hf
  | prime => simp [pureSrcFact] at hf
  | opaqueBit => simp [pureSrcFact] at hf
  | shift k => simp [pureSrcFact] at hf
  | quadRoot q r => simp [pureSrcFact] at hf
  | rootSet qs => simp [pureSrcFact] at hf

/-- **`pureStepFact_sound`**: every reader-generic rule is sound at any reader `rd` whose constants
read their entries (`hK`), whose ranged values lie in their ranges (`hS`) and whose bound values
read their expressions (`hB`), from its premises' facts at `rd`. -/
theorem pureStepFact_sound (hM : ir.DerivModel I primeNodes) {rd : ir.Valuation I}
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0))
    {sr : List (ℕ × ℕ)}
    (hS : ∀ vN ∈ sr, ∀ i < (ir.value vN.1).size,
      ∃ n < vN.2, rd vN.1 i = ((n : ℕ) : (I (ir.valueField vN.1)).K))
    (hB : ir.BoundReads rd) {body : PredBody} {fs : List Fact}
    (hfs : ∀ f ∈ fs, f.HoldsWith ir rd) {s : Step} {f : Fact}
    (h : ir.pureStepFact primeNodes sr body fs s = some f) : f.HoldsWith ir rd := by
  induction s generalizing body f with
  | subst e₁ e₂ => exact substFact_sound hM.wf hB h
  | linear cs e₁ e₂ => exact linearFact_sound hK hM.wf hM.registered hM.lawful hfs h
  | rangeNat k => exact rangeNatFact_sound hfs h
  | src v s =>
    simp only [pureStepFact] at h
    split_ifs at h with hg
    exact pureSrcFact_sound hM.wf hM.registered hM.lawful hK hS hfs hg h
  | ivlNat k => exact ivlNatFact_sound hM.wf hM.lawful hfs h
  | ivlExpr ks x lo hi => exact ivlExprFact_sound hM.wf hM.registered hM.lawful hK hfs h
  | ivlSolve k ks a j lo hi => exact ivlSolveFact_sound hM.registered hM.wf hfs h
  | ivlApply k a e lo hi => exact ivlApplyFact_sound hM.wf hM.registered hM.lawful hfs h
  | ivlLogic ks e => exact ivlLogicFact_sound hfs h
  | ivlMeet a b => exact ivlMeetFact_sound hfs h
  | ivlDisjoint a b => exact ivlDisjointFact_sound hfs h
  | fieldDvd k a b => exact fieldDvdFact_sound hM.wf hM.registered hfs h
  | natIvl k => exact natIvlFact_sound hfs h
  | transport k j => exact transportFact_sound hfs h
  | natComp k j => exact natCompFact_sound hM.wf hM.registered hM.lawful hK hfs h
  | natLin k ks => exact natLinFact_sound hM.wf hM.registered hM.lawful hK hfs h
  | liftConst k a => exact liftConstFact_sound hM.wf hM.registered hM.lawful hK hfs h
  | lift k a b => exact liftFact_sound hM.wf hM.registered hM.lawful hK hfs h
  | digits k ds T => exact digitsFact_sound hM.wf hM.registered hM.lawful hK hfs h
  | linop s => exact linopFact_sound hM.wf hM.registered hM.lawful hK hfs h
  | inDom d s ih => exact ih (by simpa only [pureStepFact] using h)
  | _ => simp [pureStepFact] at h

end GordieHowe.RealizedProgram
