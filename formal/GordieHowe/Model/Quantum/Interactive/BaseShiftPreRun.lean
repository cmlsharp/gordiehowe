-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.BaseShiftPreCirc

@[expose] public section

/-!
# The expanded run of a composition whose adversary's Kraus maps are read after permutations

`KindAlg.simLaw_composeBothOut_pre`: for Kraus maps `st` of `T` that are `T`'s read after
permutations `σ k` (`KrausMap.RightPerm`), the expanded coherent run of the composition of
`T.withStep st`, its steps read after `W`, has the law of that of `T` with its steps read after
`W` and then the permutations at the starts of the query intervals (`KindAlg.prePerms`).
-/

open Matrix
open scoped BigOperators

namespace GordieHowe.Quantum

open GordieHowe.QROM

namespace KindAlg

variable {m : ℕ} {I J B Req Resp O : Type} [Fintype I] [Fintype J] [DecidableEq I]
  [DecidableEq J] [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  [Nonempty (Bits m)] {ksT : KindShape (Bits m) (BitStr I J) Req Resp} {T : KindAlg ksT O}
  {C : Challenger (Bits m) (BitStr I J) Req Resp}

/-- **The composition with the Kraus maps read after permutations** (module docstring), for
trace-preserving steps (`hTP`, `hTP'`). -/
theorem simLaw_composeBothOut_pre {C' : Type} (E : Expansion (Bits m) B C')
    (e : BitStr I J ≃ B) (kq : ℕ)
    {σ : StepIdx T.slots T.post → Equiv.Perm (DReg T.W T.width (Bits m) (BitStr I J) Req Resp)}
    {st : StepIdx T.slots T.post → KrausMap T.R (DReg T.W T.width (Bits m) (BitStr I J) Req Resp)
      (DReg T.W T.width (Bits m) (BitStr I J) Req Resp)}
    (hst : ∀ k, KrausMap.RightPerm (σ k) (st k) (T.step k))
    (hTP : T.StepsTP) (hTP' : (T.withStep st).StepsTP)
    (W : ℕ → Equiv.Perm (ReprogrammedQueryReg (T.CW C) (Bits m) (BitStr I J)))
    (g : Option (T.CW C) → C') :
    simLaw e (expandAdv e E kq ((((T.withStep st).composeBothOut C id).precomp
        fun j => W j).toQueryAlgCoh.mapOut g)) =
      simLaw e (expandAdv e E kq (((T.composeBothOut C id).precomp
        fun j => (W j).trans (T.prePerms C σ j)).toQueryAlgCoh.mapOut g)) := by
  have hsp := T.segPerm_fullCircBoth C hst
  have hdep : ((T.withStep st).composeBothOut C id).depth = (T.composeBothOut C id).depth :=
    hsp.queries_eq
  rw [← simLaw_expandAdv_castDepth e E kq
    (((T.withStep st).composeBothOut C id).precomp fun j => W j) _ hdep]
  refine simLaw_expandAdv_transport e E kq
    ((T.composeBothOut C id).precomp fun j => (W j).trans (T.prePerms C σ j))
    (Alg.tracePreserving_precomp (hTP.tracePreserving_composeBothOut C id) _)
    (((((T.withStep st).composeBothOut C id).precomp fun j => W j).castDepth _ hdep).step)
    (tracePreserving_castDepth (Alg.tracePreserving_precomp
      (hTP'.tracePreserving_composeBothOut C id) _) _ hdep)
    (fun _ => 1) (fun _ => Set.univ) rfl rfl (fun i ρ _ => ?_) (fun _ _ _ => fun _ _ _ =>
      ⟨trivial, trivial⟩) (fun _ _ => ⟨fun _ => 1, fun _ => rfl⟩) (fun _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ => ⟨trivial, trivial⟩) g
  change (((T.withStep st).composeBothOut C id).precomp fun j => W j).step
      (Fin.cast (congrArg (· + 1) hdep.symm) i) (ρ.submatrix (Equiv.refl _).symm
        (Equiv.refl _).symm) = _
  rw [compiled_precomp_apply, compiled_precomp_apply]
  simp only [Fin.val_cast]
  rw [Circuit.SegPerm.seg_apply _ hsp, Circuit.submatrix_perm_mul]
  rw [Equiv.Perm.mul_def]
  rfl

end KindAlg

end GordieHowe.Quantum
