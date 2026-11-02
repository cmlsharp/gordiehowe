-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.RingUnforgeability
public import GordieHowe.SPBCS.SimExtractJoint

@[expose] public section

/-!
# Knowledge soundness of a composition, with any default output

`Quantum.AdaptiveIAlg.acceptsTest_le_of_knowledgeBound`
(`GordieHowe/Applications/Ring/RingUnforgeability.lean`) reads the halted branches of the purified
composition as the composition's default output (`Alg.defaultOut`), which reads the initial state.
The extraction run of the bridge (`Quantum.extRun`,
`GordieHowe/Model/Quantum/Interactive/ReqBridge.lean`) reads them as a fixed default `d₀`, the
same for adversaries whose initial states differ. Any default does: the halted branches count in
neither the real law nor the extraction's event.

- `Quantum.AdaptiveIAlg.acceptsTest_le_of_knowledgeBound_default`, and `…_defaultR` with the
  composition read as `toKindAlg` and the oracle's average written out.
- `Quantum.AdaptiveIAlg.simProb_expandAdv_mapOut_drop`, `…_ins`: an output read through a map
  factoring through `drop`, as the event read through `drop`, or with a reinsertion `ins`.
-/

namespace GordieHowe

open IOP GordieHowe.SPBCS GordieHowe.QROM Quantum
open scoped NNReal ENNReal

namespace Quantum.AdaptiveIAlg

variable {m k e : ℕ} {Req Resp O O' Cl Stmt Wit : Type} [Fintype Req] [DecidableEq Req]
  [Fintype Resp] [DecidableEq Resp] [DecidableEq O']

/-- **An accepted claim passing a test is extracted, except with the knowledge error, with any
default output** `d₀` on the halted branches of the purified composition (as
`acceptsTest_le_of_knowledgeBound`, whose default is the composition's `defaultOut`). -/
theorem acceptsTest_le_of_knowledgeBound_default {V : NARG.QROM.Verifier m k e Cl Stmt}
    {rel : Set (Stmt × Wit)} {ext : Stmt → DB (Bits m) (Out k e) → Multiset Wit} {β : ℕ → ℝ≥0∞}
    (K : V.KnowledgeBound rel ext β) {shA : AlgShape (Bits m) (XOut k e) Req Resp} (A : AdaptiveIAlg shA O)
    (C : Challenger (Bits m) (XOut k e) Req Resp) (f : A.toKindAlg.CW C → O') (c : O' → Cl)
    (ok : O' → Prop) (d₀ : O') {t : ℕ} (ht : A.width * (A.budget + A.post) ≤ t) :
    ((A.toKindAlg.composeBothOut C f).realLaw (outEquiv k e)).toOuterMeasure
        {p | ∃ y ∈ p.out, V.Accepted p.oracle (c y) ∧ ok y} ≤
      simProb (outEquiv k e) (expandAdv (outEquiv k e) (SPBCS.QROM.expansionVia V c) V.kq
          ((A.toTPKindAlg.composeBothOut C f).toQueryAlgCoh.mapOut (·.getD d₀)))
          (fun y D => ok y ∧ NARG.ExtractsAt rel ext (V.stmt (c y)) D) +
        V.knowledgeError β (t + C.Q * C.q + V.kq) := by
  set B := A.toTPKindAlg.composeBothOut C f
  have hdom := A.realLaw_composeBothOut_le (freeze := false) C f (outEquiv k e)
    {p | ∃ y ∈ p.out, V.Accepted p.oracle (c y) ∧ ok y}
    (fun p ⟨y, hy, _⟩ => by rw [Option.mem_def] at hy; rw [hy]; simp)
  have hle : (B.realLaw (outEquiv k e)).toOuterMeasure
      {p | ∃ y ∈ p.out, V.Accepted p.oracle (c y) ∧ ok y} ≤
      (B.realLaw (outEquiv k e)).toOuterMeasure
      {p | ∃ y ∈ p.out, ok y ∧ V.Accepted p.oracle (c y)} :=
    MeasureTheory.measure_mono fun p ⟨y, hy, hw⟩ => ⟨y, hy, hw.2, hw.1⟩
  have hpure := B.toOuterMeasure_realLaw_le_coh (outEquiv k e) d₀
    {p | ok p.out ∧ V.Accepted p.oracle (c p.out)}
  have hacc := SPBCS.QROM.acceptsTest_le_pure_of_queryCount K c ok
    (B.toQueryAlgCoh.mapOut (·.getD d₀))
    (AdaptiveIAlg.tpQueryCount (outEquiv k e) A C f (·.getD d₀))
  refine hdom.trans (hle.trans (hpure.trans (hacc.trans (add_le_add le_rfl ?_))))
  refine V.knowledgeError_mono K.mono (Nat.add_le_add_right ?_ _)
  change A.width * A.budget + C.Q * C.q + A.width * A.post ≤ t + C.Q * C.q
  nlinarith

/-- **`acceptsTest_le_of_knowledgeBound_default` with the composition read as `toKindAlg`**
(definitionally `toKindAlg`), the form in which the absorbed adversaries' laws are stated. -/
theorem acceptsTest_le_of_knowledgeBound_defaultR {V : NARG.QROM.Verifier m k e Cl Stmt}
    {rel : Set (Stmt × Wit)} {ext : Stmt → DB (Bits m) (Out k e) → Multiset Wit} {β : ℕ → ℝ≥0∞}
    (K : V.KnowledgeBound rel ext β) {shA : AlgShape (Bits m) (XOut k e) Req Resp} (A : AdaptiveIAlg shA O)
    (C : Challenger (Bits m) (XOut k e) Req Resp) (c : A.toKindAlg.CW C → Cl)
    (ok : A.toKindAlg.CW C → Prop) (d₀ : A.toKindAlg.CW C) {t : ℕ}
    (ht : A.width * (A.budget + A.post) ≤ t) :
    ∑' H, PMF.uniformOfFintype (Bits m → XOut k e) H *
      ((A.toKindAlg.composeBothOut C id).outLaw H).toOuterMeasure
        {o | ∃ y ∈ o, V.Accepted (outEquiv k e ∘ H) (c y) ∧ ok y} ≤
      simProb (outEquiv k e) (expandAdv (outEquiv k e) (SPBCS.QROM.expansionVia V c) V.kq
          ((A.toTPKindAlg.composeBothOut C id).toQueryAlgCoh.mapOut (·.getD d₀)))
          (fun y D => ok y ∧ NARG.ExtractsAt rel ext (V.stmt (c y)) D) +
        V.knowledgeError β (t + C.Q * C.q + V.kq) := by
  have h := acceptsTest_le_of_knowledgeBound_default K A C id c ok d₀ ht
  simp only [Alg.realLaw, PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_map_apply] at h
  exact h

/-- **An extraction run's output read through a map factoring through `drop`**: the probability of
an event `P` of the run read through `g` (`g o = drop (o.getD d₀')`) and expanded by the claims `c`
is that of the event `P ∘ drop` of the run read with the default `d₀'` and expanded by the claims
`c ∘ drop`. -/
theorem simProb_expandAdv_mapOut_drop {V : NARG.QROM.Verifier m k e Cl Stmt} {CW R : Type}
    {t : ℕ} (Qa : QueryAlg (Bits m) (XOut k e) t (Option CW)) (drop : CW → R) (d₀' : CW)
    (g : Option CW → R) (hg : ∀ o, g o = drop (o.getD d₀')) (c : R → Cl) (kq : ℕ)
    (P : R → DB (Bits m) (Out k e) → Prop) :
    simProb (outEquiv k e) (expandAdv (outEquiv k e) (SPBCS.QROM.expansionVia V (c ∘ drop)) kq
        (Qa.mapOut (·.getD d₀'))) (fun y D => P (drop y) D) =
      simProb (outEquiv k e) (expandAdv (outEquiv k e) (SPBCS.QROM.expansionVia V c) kq
        (Qa.mapOut g)) P := by
  have h1 : Qa.mapOut g = (Qa.mapOut (·.getD d₀')).mapOut drop := by
    have : g = drop ∘ (·.getD d₀') := funext hg
    subst this
    rfl
  rw [h1, QROM.expandAdv_mapOut]
  rfl

/-- **An extraction run read through a map with a reinsertion**: for `g o = drop (o.getD d₀')`, an
expansion `Ex` and an event `W` of the run read with the default `d₀'` that see their input only
through `ins ∘ drop` (`hEx`, `hW`), the probability of `W` is that of `W ∘ ins` of the run read
through `g` and expanded by `Ex ∘ ins`. -/
theorem simProb_expandAdv_mapOut_ins {CW R : Type} {t : ℕ}
    (Qa : QueryAlg (Bits m) (XOut k e) t (Option CW)) (drop : CW → R) (ins : R → CW) (d₀' : CW)
    (g : Option CW → R) (hg : ∀ o, g o = drop (o.getD d₀'))
    (Ex : Expansion (Bits m) (Out k e) CW) (hEx : ∀ c, Ex.next (ins (drop c)) = Ex.next c)
    (kq : ℕ) (W : CW → DB (Bits m) (Out k e) → Prop)
    (hW : ∀ c D, W (ins (drop c)) D ↔ W c D) :
    simProb (outEquiv k e) (expandAdv (outEquiv k e) Ex kq (Qa.mapOut (·.getD d₀'))) W =
      simProb (outEquiv k e) (expandAdv (outEquiv k e) ⟨fun r => Ex.next (ins r)⟩ kq
        (Qa.mapOut g)) (fun r D => W (ins r) D) := by
  have h1 : Qa.mapOut g = (Qa.mapOut (·.getD d₀')).mapOut drop := by
    have : g = drop ∘ (·.getD d₀') := funext hg
    subst this
    rfl
  have h2 : (⟨fun c => (⟨fun r => Ex.next (ins r)⟩ : Expansion (Bits m) (Out k e) R).next
      (drop c)⟩ : Expansion (Bits m) (Out k e) CW) = Ex := by
    cases Ex
    simp only [Expansion.mk.injEq]
    funext c
    exact hEx c
  rw [h1, QROM.expandAdv_mapOut (outEquiv k e) ⟨fun r => Ex.next (ins r)⟩ kq
    (Qa.mapOut (·.getD d₀')) drop, h2]
  unfold simProb
  rw [QROM.simLaw_mapOut]
  congr 1
  ext p
  exact (hW _ _).symm

end Quantum.AdaptiveIAlg

end GordieHowe
