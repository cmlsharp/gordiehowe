-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Pure.Bridge
public import GordieHowe.Model.QROM.ExpandAt
public import GordieHowe.Model.Quantum.O2H.Mixed
public import GordieHowe.Model.QROM.CoherentBridgeCore

@[expose] public section

/-!
# The pure algorithm of a core algorithm keeps the classes its Kraus maps keep

`KeepsClasses` (`GordieHowe/Model/QROM/ExpandAt.lean`) asks that the unitaries of a pure algorithm after a step
`s` commute, on the states of its runs, with the projections onto the classes of a function `κ`
of its work register. For the coherent pure algorithm of a core algorithm (`Alg.toQueryAlgCoh`,
`GordieHowe/Model/QROM/CoherentBridgeCore.lean`: halting completion, Stinespring dilation, relabelling) this
follows from a property of the core algorithm's Kraus maps after step `s`
(`Alg.StepsKeep`, `Alg.keepsClasses_toQueryAlgCoh`): each is trace preserving and joins only basis states with the
same value of a function `f` of the work register. The control is then `f` on runs that have not
halted and a fixed value `c₀` on halted ones.

- `KrausChannel.KeepsFn F K`: the operators of `K` join only basis states with the same `F`.
- `krausAct_mask_comm`, `stinespring_mask_comm`: the Stinespring map of such a family commutes
  with the projections onto the classes of `F` (on fresh vectors, for the unitary).
- `KrausMap.keepsFn_complete`: the halting completion of a trace-preserving Kraus map that keeps
  `f` keeps the classes of `f` extended by `c₀` on halted states (its halting operator is `0`).
- `MixedAlg.dilStep_mask_comm`: the dilation's unitaries commute
  with the projections on the clean vectors of its run (`CleanVec`, `GordieHowe/Model/Quantum/Core/MixedAlg.lean`).
-/

open Finset Matrix
open scoped BigOperators ComplexOrder

namespace GordieHowe.Quantum

/-! ### Kraus families that keep a function of the basis state -/

section Keeps

variable {R ι Γ : Type*} [Fintype R] [Fintype ι] [DecidableEq ι]

/-- **A Kraus family keeps a function `F` of the basis state**: its operators join only basis
states with the same value of `F`. -/
def KrausChannel.KeepsFn (F : ι → Γ) (K : KrausChannel R ι ι) : Prop :=
  ∀ r i' i, K.op r i' i ≠ 0 → F i' = F i

/-- The computational-basis measurement keeps every function of the basis state. -/
theorem KrausChannel.keepsFn_basis (F : ι → Γ) : (KrausChannel.basis ι).KeepsFn F := by
  intro r i' i h
  simp only [KrausChannel.basis, Matrix.single_apply] at h
  split_ifs at h with hh
  · rw [← hh.1, ← hh.2]
  · exact absurd rfl h

variable {A C : Type*} [Fintype A] [Fintype C] {e : A ≃ R × C} {r₀ : R}

omit [Fintype C] in
/-- **The Stinespring map of a family that keeps `F` commutes with the projections onto the
classes of `F`.** -/
theorem krausAct_mask_comm {K : KrausChannel R ι ι} {F : ι → Γ} (hK : K.KeepsFn F) (T : Set Γ)
    (ψ : QState (ι × A)) :
    krausAct e r₀ K (mask {p : ι × A | F p.1 ∈ T} ψ) = mask {p | F p.1 ∈ T} (krausAct e r₀ K ψ) := by
  ext ⟨k, a⟩
  rw [krausAct_apply, mask_apply]
  by_cases hk : F k ∈ T
  · rw [Set.indicator_of_mem (show (k, a) ∈ {p : ι × A | F p.1 ∈ T} from hk), krausAct_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mask_apply]
    by_cases hop : K.op (e a).1 k j = 0
    · simp [hop]
    · have hj : F j ∈ T := by
        rw [← hK _ _ _ hop]
        exact hk
      rw [Set.indicator_of_mem (show (j, e.symm (r₀, (e a).2)) ∈ {p : ι × A | F p.1 ∈ T} from hj)]
  · rw [Set.indicator_of_notMem (show (k, a) ∉ {p : ι × A | F p.1 ∈ T} from hk)]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [mask_apply]
    by_cases hop : K.op (e a).1 k j = 0
    · simp [hop]
    · have hj : F j ∉ T := by
        rw [← hK _ _ _ hop]
        exact hk
      rw [Set.indicator_of_notMem (show (j, e.symm (r₀, (e a).2)) ∉ {p : ι × A | F p.1 ∈ T} from hj),
        mul_zero]

omit [Fintype R] [Fintype C] [DecidableEq ι] in
/-- A projection onto a set of basis states keeps a vector fresh. -/
theorem Fresh.mask {ψ : QState (ι × A)} (h : Fresh e r₀ ψ) (S : Set (ι × A)) :
    Fresh e r₀ (Quantum.mask S ψ) := fun i a ha => by
  classical
  rw [mask_apply, Set.indicator_apply]
  split_ifs
  · exact h i a ha
  · rfl

/-- **The Stinespring unitary of a family that keeps `F` commutes with the projections onto the
classes of `F`** on fresh vectors. -/
theorem stinespring_mask_comm {K : KrausChannel R ι ι} {F : ι → Γ} (hK : K.KeepsFn F) (T : Set Γ)
    {ψ : QState (ι × A)} (hψ : Fresh e r₀ ψ) :
    stinespring e r₀ K (mask {p : ι × A | F p.1 ∈ T} ψ) =
      mask {p | F p.1 ∈ T} (stinespring e r₀ K ψ) := by
  rw [stinespring_apply_of_fresh K (hψ.mask _), stinespring_apply_of_fresh K hψ,
    krausAct_mask_comm hK]

end Keeps

/-! ### The halting completion -/

namespace KrausMap

variable {R ι Γ : Type*} [Fintype R] [Fintype ι] [DecidableEq ι]

/-- **The halting completion keeps the classes of `f`, extended by `c₀` on halted states**, for a
trace-preserving Kraus map that keeps `f`. -/
theorem keepsFn_complete {K : KrausMap R ι ι} (htp : ∑ r, (K.op r)ᴴ * K.op r = 1) {f : ι → Γ}
    (hK : ∀ r i' i, K.op r i' i ≠ 0 → f i' = f i) (c₀ : Γ) :
    K.complete.KeepsFn fun p : ι × Bool => if p.2 then c₀ else f p.1 := by
  intro o p' p h
  show (if p'.2 = true then c₀ else f p'.1) = (if p.2 = true then c₀ else f p.1)
  rcases o with r | b
  · simp only [complete, completeOp, Matrix.kroneckerMap_apply, Matrix.single_apply] at h
    split_ifs at h with hb
    · obtain ⟨hb1, hb2⟩ := hb
      rw [← hb1, ← hb2]
      simp only [Bool.false_eq_true, if_false]
      exact hK r p'.1 p.1 fun h0 => h (by rw [h0, zero_mul])
    · exact absurd (mul_zero _) h
  · cases b
    · simp [complete, completeOp, haltOp_eq_zero htp] at h
    · simp only [complete, completeOp, Matrix.kroneckerMap_apply, Matrix.single_apply,
        Matrix.one_apply] at h
      split_ifs at h with h1 h2
      · rw [← h2.1, ← h2.2]
        rfl
      · exact absurd (mul_zero _) h
      · exact absurd (zero_mul _) h
      · exact absurd (zero_mul _) h

end KrausMap

/-! ### The dilation -/

namespace MixedAlg

variable {Z ι R M Γ : Type*} [Fintype ι] [DecidableEq ι] [Fintype R] [Fintype M] {d : ℕ}
  (G : MixedAlg Z ι d R M) [Nonempty R] [Nonempty M]

/-- **A step of the dilation commutes with the projections onto the classes of `F`** on a clean
vector, when the step keeps `F`. -/
theorem dilStep_mask_comm (z : Z) {n : ℕ} {F : ι → Γ}
    (hK : ∀ h : n < d + 1, (G.step z ⟨n, h⟩).KeepsFn F) (T : Set Γ) {ψ : QState (ι × Anc ι d R M)}
    (hψ : CleanVec n ψ) :
    G.dilStep z n (mask {p | F p.1 ∈ T} ψ) = mask {p | F p.1 ∈ T} (G.dilStep z n ψ) := by
  by_cases h : n < d + 1
  · simp only [dilStep, h, dite_true]
    exact stinespring_mask_comm (hK h) T (hψ.fresh (k := ⟨n, h⟩) le_rfl)
  · simp [dilStep, h]

end MixedAlg

end GordieHowe.Quantum

namespace GordieHowe.Quantum.Alg

open GordieHowe.QROM

/-! ### The pure algorithm of a core algorithm -/

variable {X Y O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  (A : Alg X Y O) {Γ : Type}

/-- **The core Kraus maps after step `s` are trace preserving and keep `f`**: for each `j` with
`s < j`, the map number `j` has `∑ r, (op r)ᴴ op r = 1` and joins only basis states with the same
value of `f` on the work register. -/
structure StepsKeep (s : ℕ) (f : A.V → Γ) : Prop where
  /-- Trace preservation after step `s`. -/
  tp : ∀ j (hj : j < A.depth + 1), s < j → ∑ r, ((A.step ⟨j, hj⟩).op r)ᴴ * (A.step ⟨j, hj⟩).op r = 1
  /-- The classes of `f` are kept after step `s`. -/
  keeps : ∀ j (hj : j < A.depth + 1), s < j → ∀ r i' i, (A.step ⟨j, hj⟩).op r i' i ≠ 0 →
    f i'.1 = f i.1

variable {A}

/-- **The coherent pure algorithm of a core algorithm keeps the classes of its output** when the
core Kraus maps after step `s` are trace preserving and keep the output: if they keep
`π ∘ g ∘ some ∘ A.out`, the unitaries of `A.toQueryAlgCoh.mapOut g` after step `s` keep the
classes of `π` of its output (read from the system register, `haltOutCoh`) on its runs. On a run
before step `j` the dilation's ancilla is clean from `j` on (`MixedAlg.dilRun_spec`), and its step
`j` acts there as the Stinespring map of the halting completion of `A`'s map `j`
(`MixedAlg.dilStep_mask_comm`, `KrausMap.keepsFn_complete`). -/
theorem keepsClasses_toQueryAlgCoh {C' : Type} (g : Option O → C') (π : C' → Γ) {s : ℕ}
    (hA : A.StepsKeep s fun v => π (g (some (A.out v)))) :
    KeepsClasses (A.toQueryAlgCoh.mapOut g) s fun w => π ((A.toQueryAlgCoh.mapOut g).out w) := by
  intro H j hsj hjd T
  have := A.init.nonempty
  set σ := haltRelabel A.V A.HaltAnc X Y
  set D := A.halting.dilateCoh fun _ => ∅
  set πH := MixedAlg.liftPerm (A := A.HaltAnc) (MixedAlg.liftPerm (A := Bool) (queryPerm (W := A.V) (n := 1) H))
  set F : QueryReg A.V 1 X Y × Bool → Γ := fun p =>
    if p.2 then π (g none) else π (g (some (A.out p.1.1)))
  have hmask : ∀ v, mask {r : QueryReg ((A.V × Bool) × A.HaltAnc) 1 X Y |
      π ((A.toQueryAlgCoh.mapOut g).out r.1) ∈ T} (relabel σ v) =
      relabel σ (mask {p | F p.1 ∈ T} v) := fun v => by
    classical
    ext r
    have hF : π ((A.toQueryAlgCoh.mapOut g).out r.1) = F (σ.symm r).1 := by
      show π (g (A.haltOutCoh r.1)) = _
      rw [haltOutCoh, apply_ite g, apply_ite π]
      rfl
    simp only [relabel_apply, mask_apply]
    rw [Set.indicator_apply, Set.indicator_apply]
    simp only [Set.mem_setOf_eq, hF]
  have hstage : ((A.toQueryAlgCoh.mapOut g).toOracleAlg ∅).stage (queryPerm H) () (j - 1) =
      relabel σ (D.stage πH () (j - 1)) :=
    D.stage_relabel σ (fun _ => rfl) () (j - 1)
  have hq : ∀ v, permOp (queryPerm H) (relabel σ v) = relabel σ (permOp πH v) :=
    fun v => OracleAlg.permOp_relabel σ (fun _ => rfl) v
  have hrun : D.stage πH () (j - 1) = A.halting.dilRun (MixedAlg.liftPerm (queryPerm H)) () (j - 1) :=
    A.halting.stage_dilateCoh _ _ () (by omega)
  have hclean : MixedAlg.CleanVec j (permOp πH (D.stage πH () (j - 1))) := by
    rw [hrun]
    have := ((A.halting.dilRun_spec (MixedAlg.liftPerm (queryPerm H)) () (j - 1)).1.permOp
      (MixedAlg.liftPerm (queryPerm H)))
    rwa [show j - 1 + 1 = j by omega] at this
  rw [hstage]
  have hj' : j < A.depth + 1 := Nat.lt_succ_of_le hjd
  rw [OracleAlg.stepAt_of_lt _ hj']
  show relabel σ (D.step () ⟨j, hj'⟩ (relabel σ.symm
      (mask {r : QueryReg ((A.V × Bool) × A.HaltAnc) 1 X Y |
        π ((A.toQueryAlgCoh.mapOut g).out r.1) ∈ T}
        (permOp (queryPerm H) (relabel σ (D.stage πH () (j - 1))))))) =
    mask {r : QueryReg ((A.V × Bool) × A.HaltAnc) 1 X Y |
      π ((A.toQueryAlgCoh.mapOut g).out r.1) ∈ T}
      (relabel σ (D.step () ⟨j, hj'⟩ (relabel σ.symm
        (permOp (queryPerm H) (relabel σ (D.stage πH () (j - 1)))))))
  rw [hq, hmask, relabel_symm_relabel, relabel_symm_relabel, hmask]
  congr 1
  have hK : ∀ h : j < A.depth + 1, (A.halting.step () ⟨j, h⟩).KeepsFn F := fun h =>
    KrausMap.keepsFn_complete (hA.tp j h hsj) (f := fun i => π (g (some (A.out i.1))))
      (hA.keeps j h hsj) (π (g none))
  exact A.halting.dilStep_mask_comm () hK T hclean

omit [AddCommGroup Y] in
/-- The classes of a function of `f` are kept where those of `f` are. -/
theorem StepsKeep.map {Γ' : Type} {s : ℕ} {f : A.V → Γ} (h : A.StepsKeep s f) (φ : Γ → Γ') :
    A.StepsKeep s (φ ∘ f) :=
  ⟨h.tp, fun j hj hsj r i' i hne => by simp only [Function.comp_apply]; rw [h.keeps j hj hsj r i' i hne]⟩

end GordieHowe.Quantum.Alg
