-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.QueryBounded
public import GordieHowe.Model.QROM.AdaptiveCount
public import GordieHowe.Model.QROM.AdaptiveTestClasses

@[expose] public section

/-!
# Trace-preserving adversaries within their budget

An adversary with run-time kinds (`AdaptiveIAlg`, `GordieHowe/Model/Quantum/Interactive/Adaptive.lean`) has two
semantics: the model's run `compose` (= `toKindAlg.composeBoth`), which projects away a branch that
asks for a query slot over its budget and loses the weight its own Kraus maps lose, and the run of
its trace-preserving form `toTPKindAlg` (`GordieHowe/Model/Quantum/Interactive/AdaptiveTP.lean`), in which such a
branch aborts to the ended value of its query counter. Simulation-sound extractability runs the
first in its real game and the second in its extraction game. This file proves that for the
adversaries of `def:adversary` (trace-preserving steps, `AdaptiveIAlg.TracePreserving`; the query
bound on every branch, `AdaptiveIAlg.WithinBudget`) the two coincide, and that aborting an
over-budget call is equivalent to the bound on every branch.

## Results

- (i) `AdaptiveIAlg.TracePreserving.haltOp_eq_zero`: the halting operators of a trace-preserving
  adversary are zero, so its trace-preserving form ends a branch only at an over-budget call.
- `AdaptiveIAlg.WithinBudget` (the every-branch query bound): the trace-preserving form ends with
  probability `0` against every challenger and oracle. `AdaptiveIAlg.withinBudget_iff`: this holds
  exactly when the model's run outputs `none` with probability `0` against every challenger and
  oracle.
- (ii) `AdaptiveIAlg.WithinBudget.outLaw_compose_none`: the model's run terminates with
  probability one.
- (iii) `AdaptiveIAlg.WithinBudget.final_compose_eq`, `outLaw_compose_eq`, `realLaw_compose_eq`
  (and the `composeBothOut` forms for an output of all composed registers): the model's run and the
  trace-preserving form's run have the same final state and the same output law.
- (iv) `AdaptiveIAlg.abortAlg`, the aborting completion: the adversary that counts its query slots
  and aborts an over-budget call to a fixed counter value. It is trace preserving and within its
  budget for every adversary (`tracePreserving_abortAlg`, `withinBudget_abortAlg`), and for an
  adversary within its budget its model run has the adversary's output law and final state, the
  latter placed along the map that adds the completion's counter
  (`WithinBudget.outLaw_compose_abortAlg`, `WithinBudget.final_compose_abortAlg`).

The proofs of (iii) and of the last two statements do not use `TracePreserving`: `WithinBudget`
excludes both the projected over-budget weight and the lost weight. With `TracePreserving`, the
lost weight is zero by (i), so `WithinBudget` is the query bound alone.

## Method

A circuit of trace-preserving Kraus maps keeps the trace (`ReprogrammedCircuit.AllTP.trace_run`). A
positive semidefinite matrix whose part on a set has its whole trace is that part
(`cutTo_eq_self_of_trace`); with the intertwining of the two compositions
(`AdaptiveIAlg.intertwined_fullCircBoth`) this gives (iii). For (iv), a set of workspaces closed under
the adversary's steps holds through the composition (`KindAlg.Invariant`), and the aborting
completion's composition simulates the trace-preserving form's along the lift of registers
(`ReprogrammedCircuit.Sim`, `AdaptiveIAlg.sim_fullCircBoth`).
-/

open Finset Matrix
open scoped BigOperators ENNReal Kronecker ComplexOrder MatrixOrder

namespace GordieHowe.Quantum

/-! ### Circuits whose Kraus maps all preserve the trace -/

section TraceRun

variable {ι : Type*} [Fintype ι]

/-- Conjugating by a basis permutation keeps the trace. -/
theorem trace_submatrix_perm (π : Equiv.Perm ι) (ρ : Matrix ι ι ℂ) :
    (ρ.submatrix π.symm π.symm).trace = ρ.trace :=
  trace_submatrix_equiv ρ π.symm

end TraceRun

namespace ReprogrammedCircuit

variable {V X Y : Type} [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y]

/-- **Every Kraus map of the circuit is trace preserving.** -/
def AllTP : ReprogrammedCircuit V X Y → Prop
  | nil => True
  | kraus K c => (∑ r, (K.op r)ᴴ * K.op r = 1) ∧ AllTP c
  | rquery _ c => AllTP c

theorem AllTP.append : ∀ {c d : ReprogrammedCircuit V X Y}, AllTP c → AllTP d → AllTP (c ++ d)
  | nil, _, _, hd => hd
  | kraus _ c, _, ⟨hK, hc⟩, hd => ⟨hK, AllTP.append (c := c) hc hd⟩
  | rquery _ c, _, hc, hd => AllTP.append (c := c) hc hd

theorem AllTP.concat : ∀ {cs : List (ReprogrammedCircuit V X Y)}, (∀ c ∈ cs, AllTP c) →
    AllTP (ReprogrammedCircuit.concat cs)
  | [], _ => trivial
  | c :: cs, h => (h c (List.mem_cons_self ..)).append
      (AllTP.concat (cs := cs) fun d hd => h d (List.mem_cons_of_mem _ hd))

/-- **A circuit maps positive semidefinite matrices to positive semidefinite matrices.** -/
theorem posSemidef_run [AddGroup Y] (H : X → Y) : ∀ (c : ReprogrammedCircuit V X Y)
    {ρ : Matrix (QueryReg V 1 X Y) (QueryReg V 1 X Y) ℂ}, ρ.PosSemidef → (c.run H ρ).PosSemidef
  | nil, _, hρ => hρ
  | kraus K c, _, hρ => posSemidef_run H c (K.posSemidef_apply hρ)
  | rquery _ c, _, hρ => posSemidef_run H c (hρ.submatrix _)

/-- **A circuit of trace-preserving Kraus maps keeps the trace.** -/
theorem AllTP.trace_run [AddGroup Y] (H : X → Y) : ∀ {c : ReprogrammedCircuit V X Y}, AllTP c →
    ∀ ρ, (c.run H ρ).trace = ρ.trace
  | nil, _, _ => rfl
  | kraus K c, ⟨hK, hc⟩, ρ => by
    rw [run, AllTP.trace_run H (c := c) hc, K.trace_apply_of_tp hK]
  | rquery a c, hc, ρ => by
    rw [run, AllTP.trace_run H (c := c) hc, trace_submatrix_perm]

end ReprogrammedCircuit

/-! ### The composition of a trace-preserving core algorithm keeps the trace -/

namespace KindAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  (B : KindAlg X Y Req Resp O) (C : Challenger X Y Req Resp)

/-- **Every step of the core algorithm with kinds is trace preserving.** -/
def StepsTP : Prop :=
  ∀ k, ∑ r, ((B.step k).op r)ᴴ * (B.step k).op r = 1

variable [Nonempty X] [AddGroup Y]

omit [Nonempty X] [AddGroup Y] in
open ReprogrammedCircuit in
theorem allTP_advQueries (ass : B.CW C → List (Assignment X Y)) : AllTP (B.advQueries C ass) := by
  refine AllTP.concat fun c hc => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hc
  exact ⟨KrausMap.tp_ofPerm _, KrausMap.tp_ofPerm _, trivial⟩

open ReprogrammedCircuit in
theorem allTP_chalQueries (j : Fin B.slots) : AllTP (B.chalQueries C j) := by
  refine AllTP.concat fun c hc => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hc
  exact ⟨KrausMap.tp_ofPerm _, KrausMap.tp_ofPerm _, trivial⟩

variable {B}

open ReprogrammedCircuit in
/-- **The composition of a core algorithm with trace-preserving steps is a circuit of
trace-preserving Kraus maps.** -/
theorem StepsTP.allTP_fullCircBoth (hB : B.StepsTP) : AllTP (B.fullCircBoth C) := by
  have hadv : ∀ k, ∑ r, ((B.advKraus C k).op r)ᴴ * (B.advKraus C k).op r = 1 :=
    fun k => KrausMap.tp_tensorId_reindex (hB k) _
  refine AllTP.append (AllTP.append (AllTP.concat fun c hc => ?_) (AllTP.concat fun c hc => ?_))
    ⟨hadv _, trivial⟩
  · obtain ⟨j, -, rfl⟩ := List.mem_map.1 hc
    exact ⟨hadv _, KrausMap.tp_comp (KrausMap.tp_ofPerm _) (KrausMap.tp_measureFn _),
      (B.allTP_chalQueries C j).append ⟨KrausMap.tp_ofPerm _, B.allTP_advQueries C _⟩⟩
  · obtain ⟨b, -, rfl⟩ := List.mem_map.1 hc
    exact ⟨hadv _, B.allTP_advQueries C _⟩

open ReprogrammedCircuit in
/-- **The composition at a fixed schedule of a core algorithm with trace-preserving steps is a
circuit of trace-preserving Kraus maps.** -/
theorem StepsTP.allTP_fullCirc (hB : B.StepsTP) (sched : Fin B.slots → Bool) :
    AllTP (B.fullCirc C sched) := by
  have hadv : ∀ k, ∑ r, ((B.advKraus C k).op r)ᴴ * (B.advKraus C k).op r = 1 :=
    fun k => KrausMap.tp_tensorId_reindex (hB k) _
  refine AllTP.append (AllTP.append (AllTP.concat fun c hc => ?_) (AllTP.concat fun c hc => ?_))
    ⟨hadv _, trivial⟩
  · obtain ⟨j, -, rfl⟩ := List.mem_map.1 hc
    refine ⟨hadv _, KrausMap.tp_comp (KrausMap.tp_ofPerm _) (KrausMap.tp_measureFn _), ?_⟩
    cases sched j
    · exact AllTP.append (c := .nil) trivial ⟨KrausMap.tp_ofPerm _, B.allTP_advQueries C _⟩
    · exact (B.allTP_chalQueries C j).append ⟨KrausMap.tp_ofPerm _, trivial⟩
  · obtain ⟨b, -, rfl⟩ := List.mem_map.1 hc
    exact ⟨hadv _, B.allTP_advQueries C _⟩

variable [Nonempty Y]

omit [Nonempty X] [AddGroup Y] in
theorem trace_withAnc {V : Type} [Fintype V] [DecidableEq V] (x₀ : X)
    (ρ : Matrix (QueryReg V 1 X Y) (QueryReg V 1 X Y) ℂ) : (withAnc x₀ ρ).trace = ρ.trace := by
  rw [withAnc_eq_kronecker]
  have h : ((ρ ⊗ₖ reprogAnc (Y := Y) x₀).submatrix (ancSplit V X Y) (ancSplit V X Y)).trace =
      (ρ ⊗ₖ reprogAnc (Y := Y) x₀).trace := by
    simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
    exact Equiv.sum_comp (ancSplit V X Y) fun q => (ρ ⊗ₖ reprogAnc (Y := Y) x₀) q q
  rw [h]
  rw [trace_kronecker, trace_reprogAnc, mul_one]

/-- The final state of a composition with an output of the composed registers is the run of its
circuit on the initial state, with the clean ancilla. -/
theorem final_composeBothOut {O' : Type} (B : KindAlg X Y Req Resp O) (f : B.CW C → O')
    (H : X → Y) :
    (B.composeBothOut C f).final H =
      withAnc x₀ ((B.fullCircBoth C).run H (B.initSys C).mat) := by
  rw [Circuit.toAlg_final]
  exact ReprogrammedCircuit.run_toCircuit H _ _ _

/-- The composition reads the adversary's output from the composed registers. -/
theorem composeBoth_eq_composeBothOut (B : KindAlg X Y Req Resp O) :
    B.composeBoth C = B.composeBothOut C fun v => B.out v.adv.workspace :=
  rfl

/-- **The final state of the composition of a core algorithm with trace-preserving steps has
trace one.** -/
theorem StepsTP.trace_final (hB : B.StepsTP) {O' : Type} (f : B.CW C → O') (H : X → Y) :
    ((B.composeBothOut C f).final H).trace = 1 := by
  rw [final_composeBothOut, trace_withAnc, (hB.allTP_fullCircBoth C).trace_run H,
    (B.initSys C).trace_eq_one]

end KindAlg

/-- **The probability of non-termination** is the trace missing from the final state. -/
theorem Alg.outLaw_none {X Y O : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    [AddGroup Y] (A : Alg X Y O) (H : X → Y) :
    A.outLaw H none = ENNReal.ofReal (1 - (A.final H).trace.re) := by
  rw [Alg.outLaw, PMF.map_apply, tsum_fintype, Fintype.sum_option]
  simp [basisLaw]

/-! ### Positive semidefinite matrices with a zero diagonal entry -/

section PSD

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- **A diagonal entry of a positive semidefinite matrix with nonpositive real part is zero.** -/
theorem _root_.Matrix.PosSemidef.diag_eq_zero_of_re_nonpos {M : Matrix ι ι ℂ} (hM : M.PosSemidef) {i : ι}
    (hi : (M i i).re ≤ 0) : M i i = 0 := by
  obtain ⟨h1, h2⟩ := Complex.nonneg_iff.1 (hM.diag_nonneg (i := i))
  exact Complex.ext (by simp only [Complex.zero_re]; linarith) (by simp only [Complex.zero_im]; exact h2.symm)

/-- **A row of a positive semidefinite matrix through a zero diagonal entry is zero.** -/
theorem _root_.Matrix.PosSemidef.apply_eq_zero_of_diag {M : Matrix ι ι ℂ} (hM : M.PosSemidef) {i : ι}
    (hi : M i i = 0) (j : ι) : M j i = 0 ∧ M i j = 0 := by
  have h1 : star (Pi.single i 1 : ι → ℂ) ⬝ᵥ M *ᵥ Pi.single i 1 = 0 := by
    simp [Matrix.mulVec_single, hi]
  have h2 := congrFun (hM.dotProduct_mulVec_zero_iff.1 h1) j
  have h3 : M j i = 0 := by simpa using h2
  refine ⟨h3, ?_⟩
  rw [← hM.isHermitian.apply i j, h3, star_zero]

/-- **A positive semidefinite matrix whose part on `T` has its whole trace is its part on `T`.** -/
theorem cutTo_eq_self_of_trace {M : Matrix ι ι ℂ} (hM : M.PosSemidef) {T : Set ι}
    (htr : (cutTo T M).trace.re = M.trace.re) : cutTo T M = M := by
  classical
  have hd : ∀ i, 0 ≤ (M i i).re := fun i => (Complex.nonneg_iff.1 (hM.diag_nonneg (i := i))).1
  have hre : ∑ i, (cutTo T M i i).re = ∑ i, (M i i).re := by
    simpa [Matrix.trace, Complex.re_sum] using htr
  have hsplit : ∀ i, (M i i).re = (cutTo T M i i).re + (if i ∈ T then 0 else (M i i).re) :=
    fun i => by by_cases hi : i ∈ T <;> simp [cutTo, hi]
  have hz : ∑ i, (if i ∈ T then 0 else (M i i).re) = 0 := by
    have h1 : ∑ i, (M i i).re = ∑ i, (cutTo T M i i).re +
        ∑ i, (if i ∈ T then 0 else (M i i).re) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => hsplit i
    linarith
  have hz' := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => by
    split_ifs; exact le_rfl; exact hd i).1 hz
  have h0 : ∀ i, i ∉ T → M i i = 0 := fun i hi => by
    have := hz' i (Finset.mem_univ _)
    rw [if_neg hi] at this
    exact hM.diag_eq_zero_of_re_nonpos this.le
  ext i j
  simp only [cutTo]
  split_ifs with h
  · rfl
  · rcases not_and_or.1 h with hi | hj
    · exact ((hM.apply_eq_zero_of_diag (h0 i hi) j).2).symm
    · exact ((hM.apply_eq_zero_of_diag (h0 j hj) i).1).symm

end PSD

/-! ### Kraus maps that keep a set of basis states -/

namespace KrausMap

variable {R ι : Type*} [Fintype R] [Fintype ι] [DecidableEq ι]

/-- **A Kraus map that never leaves `T`**: no operator sends a basis state in `T` outside `T`. -/
def MapsInto (K : KrausMap R ι ι) (T : Set ι) : Prop :=
  ∀ r i j, K.op r i j ≠ 0 → j ∈ T → i ∈ T

theorem MapsInto.op_mul_projOn {K : KrausMap R ι ι} {T : Set ι} (h : K.MapsInto T) (r : R) :
    K.op r * projOn T = projOn T * K.op r * projOn T := by
  classical
  ext i j
  simp only [projOn, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hj : j ∈ T
  · by_cases hi : i ∈ T
    · simp [hi, hj]
    · simp only [hi, hj, if_true, if_false, mul_one, zero_mul]
      by_contra hne
      exact hi (h r i j hne hj)
  · simp [hj]

/-- **A Kraus map that never leaves `T` keeps the matrices on `T`.** -/
theorem MapsInto.cutTo_apply {K : KrausMap R ι ι} {T : Set ι} (h : K.MapsInto T)
    {ρ : Matrix ι ι ℂ} (hρ : cutTo T ρ = ρ) : cutTo T (K ρ) = K ρ := by
  classical
  have hPP : projOn T * projOn T = (projOn T : Matrix ι ι ℂ) := by
    rw [projOn, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases hi : i ∈ T <;> simp [hi]
  have hPP' : ∀ M : Matrix ι ι ℂ, M * projOn T * projOn T = M * projOn T := fun M => by
    rw [Matrix.mul_assoc, hPP]
  rw [← hρ, KrausMap.apply, cutTo_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  have h' : projOn T * (K.op r)ᴴ = projOn T * (K.op r)ᴴ * projOn T := by
    have := congrArg Matrix.conjTranspose (h.op_mul_projOn r)
    simp only [Matrix.conjTranspose_mul, projOn_conjTranspose] at this
    rw [Matrix.mul_assoc]
    exact this
  have e1 : K.op r * cutTo T ρ * (K.op r)ᴴ =
      (projOn T * K.op r * projOn T) * ρ * (projOn T * (K.op r)ᴴ * projOn T) := by
    rw [cutTo_eq, ← h.op_mul_projOn r, ← h']
    simp only [Matrix.mul_assoc]
  rw [e1, cutTo_eq]
  simp only [← Matrix.mul_assoc, hPP, hPP']

/-- **A Kraus map that sends nothing from `S \ T` into `T`**: on a matrix on `S`, its part on
`T` depends only on the part of the matrix on `T`. -/
theorem cutTo_apply_of_absorb {K : KrausMap R ι ι} {S T : Set ι} (hTS : T ⊆ S)
    (h : ∀ r i a, K.op r i a ≠ 0 → a ∈ S → a ∉ T → i ∉ T) {ρ : Matrix ι ι ℂ}
    (hρ : cutTo S ρ = ρ) : cutTo T (K ρ) = cutTo T (K (cutTo T ρ)) := by
  classical
  have hkey : ∀ r, projOn T * K.op r * projOn S = projOn T * K.op r * projOn T := fun r => by
    ext i a
    simp only [projOn, Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hi : i ∈ T
    · by_cases ha : a ∈ T
      · simp [hi, ha, hTS ha]
      · by_cases haS : a ∈ S
        · have : K.op r i a = 0 := by
            by_contra hne
            exact h r i a hne haS ha hi
          simp [this]
        · simp [ha, haS]
    · simp [hi]
  have hkey' : ∀ r, projOn S * (K.op r)ᴴ * projOn T = projOn T * (K.op r)ᴴ * projOn T := fun r => by
    have := congrArg Matrix.conjTranspose (hkey r)
    simp only [Matrix.conjTranspose_mul, projOn_conjTranspose] at this
    simpa only [Matrix.mul_assoc] using this
  conv_lhs => rw [← hρ]
  rw [KrausMap.apply, KrausMap.apply, cutTo_sum, cutTo_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [cutTo_eq]
  calc projOn T * (K.op r * (projOn S * ρ * projOn S) * (K.op r)ᴴ) * projOn T
      = (projOn T * K.op r * projOn S) * ρ * (projOn S * (K.op r)ᴴ * projOn T) := by
        simp only [Matrix.mul_assoc]
    _ = (projOn T * K.op r * projOn T) * ρ * (projOn T * (K.op r)ᴴ * projOn T) := by
        rw [hkey, hkey']
    _ = projOn T * (K.op r * (projOn T * ρ * projOn T) * (K.op r)ᴴ) * projOn T := by
        simp only [Matrix.mul_assoc]

end KrausMap

namespace ReprogrammedCircuit

variable {V X Y : Type} [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y]

/-- **No Kraus map of the circuit leaves the work registers in `Sv`.** -/
def MapsInto (Sv : Set V) : ReprogrammedCircuit V X Y → Prop
  | nil => True
  | kraus K c => K.MapsInto (workIn Sv) ∧ MapsInto Sv c
  | rquery _ c => MapsInto Sv c

theorem MapsInto.append {Sv : Set V} : ∀ {c d : ReprogrammedCircuit V X Y}, MapsInto Sv c →
    MapsInto Sv d → MapsInto Sv (c ++ d)
  | nil, _, _, hd => hd
  | kraus _ c, _, ⟨hK, hc⟩, hd => ⟨hK, MapsInto.append (c := c) hc hd⟩
  | rquery _ c, _, hc, hd => MapsInto.append (c := c) hc hd

theorem MapsInto.concat {Sv : Set V} : ∀ {cs : List (ReprogrammedCircuit V X Y)},
    (∀ c ∈ cs, MapsInto Sv c) → MapsInto Sv (ReprogrammedCircuit.concat cs)
  | [], _ => trivial
  | c :: cs, h => (h c (List.mem_cons_self ..)).append
      (MapsInto.concat (cs := cs) fun d hd => h d (List.mem_cons_of_mem _ hd))

/-- Circuits whose Kraus maps keep the classes of `Sv` never leave `Sv`. -/
theorem KeepsAll.mapsInto {Sv : Set V} : ∀ {c : ReprogrammedCircuit V X Y}, KeepsAll Sv c →
    MapsInto Sv c
  | nil, _ => trivial
  | kraus _ c, ⟨hK, hc⟩ => ⟨fun r i j h hj => (hK r i j h).2 hj, KeepsAll.mapsInto (c := c) hc⟩
  | rquery _ c, hc => KeepsAll.mapsInto (c := c) hc

/-- **A circuit that never leaves `Sv` keeps the matrices on `Sv`.** -/
theorem MapsInto.cutTo_run [AddGroup Y] {Sv : Set V} (H : X → Y) :
    ∀ {c : ReprogrammedCircuit V X Y}, MapsInto Sv c → ∀ {ρ}, cutTo (workIn Sv) ρ = ρ →
      cutTo (workIn Sv) (c.run H ρ) = c.run H ρ
  | nil, _, _, hρ => hρ
  | kraus K c, ⟨hK, hc⟩, ρ, hρ => MapsInto.cutTo_run H (c := c) hc (hK.cutTo_apply hρ)
  | rquery a c, hc, ρ, hρ => MapsInto.cutTo_run H (c := c) hc (by
      rw [cutTo_submatrix (fun p => Iff.rfl), hρ])

end ReprogrammedCircuit

/-! ### An invariant of the adversary's workspace holds in the composition -/

namespace KindAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  (B : KindAlg X Y Req Resp O) (C : Challenger X Y Req Resp)

/-- **A set of workspaces closed under the adversary's steps** (proof-internal): the initial state
lies on it, and no Kraus map sends a register whose workspace is in it to one whose workspace is
not. -/
structure Invariant (S : Set B.W) : Prop where
  /-- The initial state lies on the set. -/
  init : ∀ a b, (B.init.mat a b ≠ 0) → a.workspace ∈ S ∧ b.workspace ∈ S
  /-- No Kraus operator leaves the set. -/
  step : ∀ k r (y x : DReg B.W B.width X Y Req Resp), (B.step k).op r y x ≠ 0 →
    x.workspace ∈ S → y.workspace ∈ S

/-- The composed registers whose adversary workspace is in `S`. -/
def advIn (S : Set B.W) : Set (B.CW C) := {v | v.adv.workspace ∈ S}

variable {B} {S : Set B.W}

open ReprogrammedCircuit in
theorem keepsAll_chalQueries_advIn [Nonempty X] [AddGroup Y] (j : Fin B.slots) :
    KeepsAll (X := X) (Y := Y) (B.advIn C S) (B.chalQueries C j) := by
  refine KeepsAll.concat fun c hc => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hc
  exact ⟨keeps_ofPerm fun p => Iff.rfl, keeps_ofPerm fun p => Iff.rfl, trivial⟩

open ReprogrammedCircuit in
theorem keepsAll_advQueries_advIn (ass : B.CW C → List (Assignment X Y)) :
    KeepsAll (B.advIn C S) (B.advQueries C ass) := by
  refine KeepsAll.concat fun c hc => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hc
  exact ⟨keeps_ofPerm fun p => Iff.rfl, keeps_ofPerm fun p => Iff.rfl, trivial⟩

open ReprogrammedCircuit in
theorem keeps_writeReply_advIn (j : Fin B.slots) :
    ∀ r i i', (KrausMap.ofPerm (B.writeReply C j)).op r i i' ≠ 0 →
      (i ∈ workIn (B.advIn C S) ↔ i' ∈ workIn (B.advIn C S)) :=
  keeps_ofPerm fun p => by
    change (if (p.1.chal.logs j).isSome = true then _ else p).1 ∈ _ ↔ _
    split_ifs <;> exact Iff.rfl

/-- The request copy of slot `j` on a register. -/
theorem copyReq_apply (j : Fin B.slots) (p : QueryReg (B.CW C) 1 X Y) :
    B.copyReq C j p = if B.kind p.1.adv.workspace = true then
      (⟨p.1.adv, p.1.chal.swapLog j p.1.adv.request⟩, p.2) else p :=
  rfl

open ReprogrammedCircuit in
theorem keeps_measReq_advIn (j : Fin B.slots) :
    ∀ o i i', (B.measReq C j).op o i i' ≠ 0 →
      (i ∈ workIn (B.advIn C S) ↔ i' ∈ workIn (B.advIn C S)) := by
  intro o y x h
  rw [AdaptiveIAlg.measReq_op_apply] at h
  have hy : y = B.copyReq C j x := by
    by_contra hne
    exact h (mul_eq_zero_of_left (if_neg hne) _)
  subst hy
  change (if B.kind x.1.adv.workspace = true then
    (⟨x.1.adv, x.1.chal.swapLog j x.1.adv.request⟩, x.2) else x).1.adv.workspace ∈ S ↔
      x.1.adv.workspace ∈ S
  split_ifs <;> exact Iff.rfl

open ReprogrammedCircuit in
theorem mapsInto_measReq_advIn (j : Fin B.slots) :
    (B.measReq C j).MapsInto (workIn (B.advIn C S)) :=
  fun o i i' h hi => (keeps_measReq_advIn C j o i i' h).2 hi

open ReprogrammedCircuit in
theorem Invariant.mapsInto_advKraus (hS : B.Invariant S) (k : StepIdx B.slots B.post) :
    (B.advKraus C k).MapsInto (workIn (B.advIn C S)) := by
  intro r y x h hx
  rw [KindAlg.advKraus, KrausMap.tensorId_reindex_op_apply] at h
  exact hS.step k r _ _ (left_ne_zero_of_mul h) hx

variable [Nonempty X] [AddGroup Y]

open ReprogrammedCircuit in
/-- **The composition never leaves the registers whose workspace is in an invariant set.** -/
theorem Invariant.mapsInto_fullCircBoth (hS : B.Invariant S) :
    MapsInto (B.advIn C S) (B.fullCircBoth C) := by
  refine MapsInto.append (MapsInto.append (MapsInto.concat fun c hc => ?_)
    (MapsInto.concat fun c hc => ?_)) ⟨hS.mapsInto_advKraus C _, trivial⟩
  · obtain ⟨j, -, rfl⟩ := List.mem_map.1 hc
    exact ⟨hS.mapsInto_advKraus C _, mapsInto_measReq_advIn C j,
      (keepsAll_chalQueries_advIn C j).mapsInto.append
        ⟨fun r i i' h hi => (keeps_writeReply_advIn C j r i i' h).2 hi,
          (keepsAll_advQueries_advIn C _).mapsInto⟩⟩
  · obtain ⟨b, -, rfl⟩ := List.mem_map.1 hc
    exact ⟨hS.mapsInto_advKraus C _, (keepsAll_advQueries_advIn C _).mapsInto⟩

variable [Nonempty Y]

omit [Nonempty Y] in
theorem Invariant.cutTo_initSys (hS : B.Invariant S) :
    cutTo (ReprogrammedCircuit.workIn (B.advIn C S)) (B.initSys C).mat = (B.initSys C).mat := by
  classical
  ext i j
  simp only [cutTo]
  split_ifs with h
  · rfl
  · symm
    simp only [KindAlg.initSys, MState.mix, MState.reindex, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.submatrix_apply, MState.tensorKet_mat, Matrix.kroneckerMap_apply]
    refine Finset.sum_eq_zero fun ω _ => ?_
    simp only [KindAlg.advSplit, Equiv.coe_fn_symm_mk, smul_eq_mul, mul_eq_zero]
    refine Or.inr (Or.inl ?_)
    by_contra hne
    exact h ⟨(hS.init _ _ hne).1, (hS.init _ _ hne).2⟩

/-- **The final state of the composition vanishes off an invariant set of workspaces.** -/
theorem Invariant.final_apply_eq_zero (hS : B.Invariant S) {O' : Type} (f : B.CW C → O')
    (H : X → Y) {p : ReprogrammedQueryReg (B.CW C) X Y} (hp : p.1.1.adv.workspace ∉ S) :
    (B.composeBothOut C f).final H p p = 0 := by
  rw [final_composeBothOut]
  have h := (hS.mapsInto_fullCircBoth C).cutTo_run H (hS.cutTo_initSys C)
  simp only [withAnc]
  rw [← h]
  simp [cutTo, ReprogrammedCircuit.workIn, advIn, hp]

end KindAlg

/-! ### The trace-preserving form and the model's run -/

namespace AdaptiveIAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  (A : AdaptiveIAlg X Y Req Resp O)

/-- **(i) The halting operators of a trace-preserving adversary are zero**, so in its
trace-preserving form a branch ends only by asking for a query slot over its budget. -/
theorem TracePreserving.haltOp_eq_zero {A : AdaptiveIAlg X Y Req Resp O} (hA : A.TracePreserving)
    (k : StepIdx A.slots A.post) : (A.step k).haltOp = 0 :=
  KrausMap.haltOp_eq_zero (hA k)

/-- The steps of the trace-preserving form are trace preserving. -/
theorem stepsTP_toTPKindAlg : A.toTPKindAlg.StepsTP :=
  A.toTPKindAlg_step_tp

variable [Nonempty X] [AddGroup Y] [Nonempty Y]

variable {A} (C : Challenger X Y Req Resp)

open Classical in
/-- **The final state of the model's composition is the part of the trace-preserving one on the
branches that have not ended**, entry by entry. -/
theorem final_composeBothOut_apply' {O' : Type} (f : A.toKindAlg.CW C → O') (H : X → Y)
    (p p' : ReprogrammedQueryReg (A.toKindAlg.CW C) X Y) :
    (A.toKindAlg.composeBothOut C f).final H p p' =
      if p.1.1 ∈ A.aliveC C ∧ p'.1.1 ∈ A.aliveC C then
        (A.toTPKindAlg.composeBothOut C f).final H p p' else 0 := by
  rw [KindAlg.final_composeBothOut, KindAlg.final_composeBothOut]
  have hrun : (A.toKindAlg.fullCircBoth C).run H (A.toKindAlg.initSys C).mat =
      cutTo (ReprogrammedCircuit.workIn (A.aliveC C))
        ((A.toTPKindAlg.fullCircBoth C).run H (A.toTPKindAlg.initSys C).mat) := by
    rw [(A.intertwined_fullCircBoth C).run H, A.cutTo_initSys C]
    rfl
  rw [hrun]
  simp only [withAnc, cutTo, ReprogrammedCircuit.workIn, Set.mem_ofPred_eq]
  split_ifs <;> simp

/-- The final state of a composition is positive semidefinite. -/
theorem posSemidef_final {O' : Type} (B : KindAlg X Y Req Resp O) (f : B.CW C → O') (H : X → Y) :
    ((B.composeBothOut C f).final H).PosSemidef :=
  (B.composeBothOut C f).posSemidef_stage H _

/-- **Within the budget, the trace-preserving form's final state vanishes on ended branches.** -/
theorem WithinBudget.final_apply_eq_zero (hB : A.WithinBudget) {O' : Type}
    (f : A.toKindAlg.CW C → O') (H : X → Y) {p : ReprogrammedQueryReg (A.toKindAlg.CW C) X Y}
    (hp : p.1.1 ∉ A.aliveC C) : (A.toTPKindAlg.composeBothOut C f).final H p p = 0 := by
  have h := hB C H
  rw [Alg.outLaw] at h
  have h' := (map_basisLaw_apply_some _ _ _ _ true).symm.trans h
  rw [Finset.sum_eq_zero_iff] at h'
  have hp' := h' p (Finset.mem_univ _)
  have he : A.endedFlag C p.1.1 = true := by
    simpa [endedFlag, aliveC] using hp
  split_ifs at hp' with hc
  swap
  · exact absurd (congrArg some he.symm) hc
  exact (posSemidef_final C _ _ H).diag_eq_zero_of_re_nonpos (ENNReal.ofReal_eq_zero.1 hp')

/-- **(iii) Within the budget, the model's composition and the trace-preserving form's have the
same final state**, for every output read from the composed registers. -/
theorem WithinBudget.final_composeBothOut_eq (hB : A.WithinBudget) {O' : Type}
    (f : A.toKindAlg.CW C → O') (H : X → Y) :
    (A.toKindAlg.composeBothOut C f).final H = (A.toTPKindAlg.composeBothOut C f).final H := by
  ext p p'
  rw [final_composeBothOut_apply']
  split_ifs with h
  · rfl
  · have hpsd := posSemidef_final C A.toTPKindAlg f H
    rcases not_and_or.1 h with hp | hp
    · exact ((hpsd.apply_eq_zero_of_diag (hB.final_apply_eq_zero C f H hp) p').2).symm
    · exact ((hpsd.apply_eq_zero_of_diag (hB.final_apply_eq_zero C f H hp) p).1).symm

/-- **(iii) Within the budget, the two compositions have the same output law.** -/
theorem WithinBudget.outLaw_composeBothOut_eq (hB : A.WithinBudget) {O' : Type}
    (f : A.toKindAlg.CW C → O') (H : X → Y) :
    (A.toKindAlg.composeBothOut C f).outLaw H = (A.toTPKindAlg.composeBothOut C f).outLaw H := by
  have hf := hB.final_composeBothOut_eq C f H
  ext o
  rcases o with _ | o
  · rw [Alg.outLaw_none, Alg.outLaw_none, hf]
  · classical
    rw [Alg.outLaw, Alg.outLaw]
    refine (map_basisLaw_apply_some _ _ _ _ o).trans
      (Eq.trans ?_ (map_basisLaw_apply_some _ _ _ _ o).symm)
    rw [hf]

/-- **(iii) Within the budget, the two compositions have the same law of output and oracle.** -/
theorem WithinBudget.realLaw_composeBothOut_eq (hB : A.WithinBudget) {O' B : Type}
    (f : A.toKindAlg.CW C → O') (e : Y ≃ B) :
    (A.toKindAlg.composeBothOut C f).realLaw e = (A.toTPKindAlg.composeBothOut C f).realLaw e := by
  unfold Alg.realLaw
  congr 1
  funext H
  rw [hB.outLaw_composeBothOut_eq C f H]

/-- The model's composition reads the adversary's output from the composed registers. -/
theorem compose_eq_composeBothOut :
    A.compose C = A.toKindAlg.composeBothOut C fun v => A.toKindAlg.out v.adv.workspace :=
  rfl

/-- **(iii) Within the budget, the model's run and the trace-preserving form's run have the same
final state.** -/
theorem WithinBudget.final_compose_eq (hB : A.WithinBudget) (H : X → Y) :
    (A.compose C).final H = (A.toTPKindAlg.composeBoth C).final H := by
  exact hB.final_composeBothOut_eq C (fun v => A.toKindAlg.out v.adv.workspace) H

/-- **(iii) Within the budget, the model's run and the trace-preserving form's run have the same
output law.** -/
theorem WithinBudget.outLaw_compose_eq (hB : A.WithinBudget) (H : X → Y) :
    (A.compose C).outLaw H = (A.toTPKindAlg.composeBoth C).outLaw H := by
  exact hB.outLaw_composeBothOut_eq C (fun v => A.toKindAlg.out v.adv.workspace) H

/-- **(iii) Within the budget, the model's run and the trace-preserving form's run have the same
law of output and oracle.** -/
theorem WithinBudget.realLaw_compose_eq (hB : A.WithinBudget) {B : Type} (e : Y ≃ B) :
    (A.compose C).realLaw e = (A.toTPKindAlg.composeBoth C).realLaw e := by
  exact hB.realLaw_composeBothOut_eq C (fun v => A.toKindAlg.out v.adv.workspace) e

/-- **(ii) Within the budget, the model's run terminates with probability one.** -/
theorem WithinBudget.outLaw_compose_none (hB : A.WithinBudget) (H : X → Y) :
    (A.compose C).outLaw H none = 0 := by
  have htr : ((A.compose C).final H).trace = 1 :=
    (congrArg Matrix.trace (hB.final_compose_eq C H)).trans
      ((A.stepsTP_toTPKindAlg).trace_final C (fun v => A.toKindAlg.out v.adv.workspace) H)
  rw [Alg.outLaw_none, htr]
  simp

variable (A) in
/-- **(iv) Within the budget means the model's run never fails to terminate**: the adversary stays
within its budget on every branch exactly when, against every challenger and oracle, the model's
run (which projects away a branch asking for an over-budget query slot, and loses the weight the
adversary's own Kraus maps lose) outputs `none` with probability `0`. For a trace-preserving
adversary only the first kind of loss exists (`TracePreserving.haltOp_eq_zero`). -/
theorem withinBudget_iff :
    A.WithinBudget ↔ ∀ (C : Challenger X Y Req Resp) (H : X → Y), (A.compose C).outLaw H none = 0 := by
  refine ⟨fun hB C H => hB.outLaw_compose_none C H, fun h C H => ?_⟩
  classical
  let f : A.toKindAlg.CW C → O := fun v => A.toKindAlg.out v.adv.workspace
  set F := (A.toTPKindAlg.composeBothOut C f).final H
  have hF : F.PosSemidef := posSemidef_final C A.toTPKindAlg f H
  have hd : ∀ p, 0 ≤ (F p p).re := fun p => (Complex.nonneg_iff.1 (hF.diag_nonneg (i := p))).1
  have htr : ∑ p, (F p p).re = 1 := by
    have := (A.stepsTP_toTPKindAlg).trace_final C f H
    simp only [Matrix.trace, Matrix.diag] at this
    simpa [Complex.re_sum] using congrArg Complex.re this
  have hG : 1 ≤ ∑ p, if p.1.1 ∈ A.aliveC C then (F p p).re else 0 := by
    have h0 := h C H
    rw [Alg.outLaw_none, ENNReal.ofReal_eq_zero, compose_eq_composeBothOut, Matrix.trace,
      Complex.re_sum] at h0
    have he : ∀ p, ((A.toKindAlg.composeBothOut C fun v => A.toKindAlg.out v.adv.workspace).final
        H p p).re = if p.1.1 ∈ A.aliveC C then (F p p).re else 0 := fun p => by
      rw [final_composeBothOut_apply']
      by_cases hp : p.1.1 ∈ A.aliveC C <;> simp [hp, F, f]
    simp only [Matrix.diag] at h0
    rw [Finset.sum_congr rfl fun p _ => he p] at h0
    linarith
  have hz : ∑ p, (if p.1.1 ∈ A.aliveC C then 0 else (F p p).re) = 0 := by
    have hsplit : ∀ p, (F p p).re = (if p.1.1 ∈ A.aliveC C then (F p p).re else 0) +
        (if p.1.1 ∈ A.aliveC C then 0 else (F p p).re) := fun p => by split_ifs <;> simp
    have : ∑ p, (F p p).re = ∑ p, (if p.1.1 ∈ A.aliveC C then (F p p).re else 0) +
        ∑ p, (if p.1.1 ∈ A.aliveC C then 0 else (F p p).re) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun p _ => hsplit p
    have hnn : 0 ≤ ∑ p, (if p.1.1 ∈ A.aliveC C then 0 else (F p p).re) :=
      Finset.sum_nonneg fun p _ => by split_ifs; exact le_rfl; exact hd p
    linarith
  have hz' := (Finset.sum_eq_zero_iff_of_nonneg fun p _ => by
    split_ifs; exact le_rfl; exact hd p).1 hz
  rw [Alg.outLaw]
  refine (map_basisLaw_apply_some _ _ _ _ true).trans (Finset.sum_eq_zero fun p _ => ?_)
  split_ifs with hc
  · have hp : p.1.1 ∉ A.aliveC C := by
      have : A.endedFlag C p.1.1 = true := (Option.some_inj.1 hc).symm
      simpa [endedFlag, aliveC] using this
    have := hz' p (Finset.mem_univ _)
    rw [if_neg hp] at this
    change ENNReal.ofReal (F p p).re = 0
    rw [this, ENNReal.ofReal_zero]
  · rfl

end AdaptiveIAlg

section Entries

variable {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι] [DecidableEq κ]

open Classical in
/-- An entry of `projOn T₂ * M * jmat e * projOn T₁`. -/
theorem projOn_mul_jmat_mul_projOn_apply (T₂ : Set ι) (M : Matrix ι ι ℂ) (e : κ → ι) (T₁ : Set κ)
    (i : ι) (a : κ) :
    (projOn T₂ * M * jmat e * projOn T₁) i a =
      (if i ∈ T₂ then 1 else 0) * M i (e a) * (if a ∈ T₁ then 1 else 0) := by
  classical
  rw [projOn, projOn, Matrix.mul_diagonal, Matrix.mul_apply]
  congr 1
  rw [Finset.sum_eq_single (e a)]
  · simp [jmat, Matrix.diagonal_mul]
  · intro c _ hc
    simp [jmat, Ne.symm hc]
  · simp

omit [Fintype ι] in
open Classical in
/-- An entry of `jmat e * projOn T₁ * N * projOn T₁`. -/
theorem jmat_mul_projOn_mul_projOn_apply (e : κ → ι) (T₁ : Set κ) (N : Matrix κ κ ℂ)
    (i : ι) (a : κ) :
    (jmat e * projOn T₁ * N * projOn T₁) i a =
      (∑ b, if e b = i ∧ b ∈ T₁ then N b a else 0) * (if a ∈ T₁ then 1 else 0) := by
  classical
  rw [projOn, Matrix.mul_diagonal, Matrix.mul_apply]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.mul_diagonal]
  simp only [jmat]
  by_cases h1 : e b = i <;> by_cases h2 : b ∈ T₁ <;> simp [h1, h2]

end Entries

/-! ### Simulating one circuit by another along a map of work registers -/

namespace ReprogrammedCircuit

variable {V₁ V₂ X Y : Type} [Fintype V₁] [DecidableEq V₁] [Fintype V₂] [DecidableEq V₂]
  [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- The basis map of query registers along a map of work registers. -/
def liftQ (ι : V₁ → V₂) : QueryReg V₁ 1 X Y → QueryReg V₂ 1 X Y :=
  Prod.map ι id

omit [Fintype V₁] [DecidableEq V₁] [Fintype V₂] [DecidableEq V₂] [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] in
theorem liftQ_injective {ι : V₁ → V₂} (h : Function.Injective ι) :
    Function.Injective (liftQ (X := X) (Y := Y) ι) := fun a b hab =>
  Prod.ext (h (congrArg Prod.fst hab)) (by
    have := congrArg Prod.snd hab
    exact this)

/-- **A Kraus map simulated by another along `ι`** (proof-internal): from a matrix `ρ` on `S₂` whose
part on `T₂` is the part on `T₁` of `σ` placed along `ι`, the second map gives a matrix on `S₂`
whose part on `T₂` is the part on `T₁` of the first map's image of `σ`, placed. -/
def KSim (ι : V₁ → V₂) (T₁ : Set V₁) (S₂ T₂ : Set V₂) {R₁ R₂ : Type} [Fintype R₁] [Fintype R₂]
    (K₁ : KrausMap R₁ (QueryReg V₁ 1 X Y) (QueryReg V₁ 1 X Y))
    (K₂ : KrausMap R₂ (QueryReg V₂ 1 X Y) (QueryReg V₂ 1 X Y)) : Prop :=
  ∀ σ ρ, cutTo (workIn S₂) ρ = ρ →
    cutTo (workIn T₂) ρ = embed (liftQ ι) (cutTo (workIn T₁) σ) →
      cutTo (workIn S₂) (K₂ ρ) = K₂ ρ ∧
        cutTo (workIn T₂) (K₂ ρ) = embed (liftQ ι) (cutTo (workIn T₁) (K₁ σ))

/-- **A circuit simulated by another along `ι`** (proof-internal): the same shape, simulated Kraus
maps, and reprogrammed queries whose assignments agree along `ι`. -/
def Sim (ι : V₁ → V₂) (T₁ : Set V₁) (S₂ T₂ : Set V₂) :
    ReprogrammedCircuit V₁ X Y → ReprogrammedCircuit V₂ X Y → Prop
  | nil, nil => True
  | kraus K₁ c₁, kraus K₂ c₂ => KSim ι T₁ S₂ T₂ K₁ K₂ ∧ Sim ι T₁ S₂ T₂ c₁ c₂
  | rquery a₁ c₁, rquery a₂ c₂ => (∀ v, a₂ (ι v) = a₁ v) ∧ Sim ι T₁ S₂ T₂ c₁ c₂
  | _, _ => False

variable {ι : V₁ → V₂} {T₁ : Set V₁} {S₂ T₂ : Set V₂}

theorem Sim.append : ∀ {c₁ d₁ : ReprogrammedCircuit V₁ X Y} {c₂ d₂ : ReprogrammedCircuit V₂ X Y},
    Sim ι T₁ S₂ T₂ c₁ c₂ → Sim ι T₁ S₂ T₂ d₁ d₂ → Sim ι T₁ S₂ T₂ (c₁ ++ d₁) (c₂ ++ d₂)
  | nil, _, nil, _, _, hd => hd
  | kraus _ c₁, _, kraus _ c₂, _, ⟨hK, hc⟩, hd => ⟨hK, Sim.append (c₁ := c₁) (c₂ := c₂) hc hd⟩
  | rquery _ c₁, _, rquery _ c₂, _, ⟨ha, hc⟩, hd => ⟨ha, Sim.append (c₁ := c₁) (c₂ := c₂) hc hd⟩
  | nil, _, kraus _ _, _, h, _ => h.elim
  | nil, _, rquery _ _, _, h, _ => h.elim
  | kraus _ _, _, nil, _, h, _ => h.elim
  | kraus _ _, _, rquery _ _, _, h, _ => h.elim
  | rquery _ _, _, nil, _, h, _ => h.elim
  | rquery _ _, _, kraus _ _, _, h, _ => h.elim

theorem Sim.concat : ∀ {cs : List (ReprogrammedCircuit V₁ X Y)}
    {ds : List (ReprogrammedCircuit V₂ X Y)},
    List.Forall₂ (Sim ι T₁ S₂ T₂) cs ds → Sim ι T₁ S₂ T₂ (ReprogrammedCircuit.concat cs) (ReprogrammedCircuit.concat ds)
  | [], [], _ => trivial
  | _ :: _, _ :: _, .cons h hs => h.append (Sim.concat hs)

/-- A reprogrammed query keeps the simulation when the assignments agree along `ι`. -/
theorem cutTo_embed_submatrix_query [AddGroup Y] (H : X → Y) {a₁ : V₁ → List (Assignment X Y)}
    {a₂ : V₂ → List (Assignment X Y)} (ha : ∀ v, a₂ (ι v) = a₁ v) (σ : Matrix _ _ ℂ)
    {ρ : Matrix (QueryReg V₂ 1 X Y) (QueryReg V₂ 1 X Y) ℂ}
    (hT : cutTo (workIn T₂) ρ = embed (liftQ ι) (cutTo (workIn T₁) σ)) :
    cutTo (workIn T₂) (ρ.submatrix (queryPermOf fun s => H.reprogram (a₂ s)).symm
        (queryPermOf fun s => H.reprogram (a₂ s)).symm) =
      embed (liftQ ι) (cutTo (workIn T₁) (σ.submatrix
        (queryPermOf fun s => H.reprogram (a₁ s)).symm
        (queryPermOf fun s => H.reprogram (a₁ s)).symm)) := by
  rw [cutTo_submatrix (fun p => Iff.rfl), hT, cutTo_submatrix (fun p => Iff.rfl)]
  refine submatrix_embed (S := Set.univ) (fun a _ => ?_) (fun a b h => by simp at h)
  obtain ⟨v, q⟩ := a
  simp only [liftQ, Prod.map, queryPermOf_apply, id, ha]

/-- **A simulated circuit simulates its run.** -/
theorem Sim.run [AddGroup Y] (H : X → Y) : ∀ {c₁ : ReprogrammedCircuit V₁ X Y}
    {c₂ : ReprogrammedCircuit V₂ X Y}, Sim ι T₁ S₂ T₂ c₁ c₂ → ∀ σ ρ,
      cutTo (workIn S₂) ρ = ρ → cutTo (workIn T₂) ρ = embed (liftQ ι) (cutTo (workIn T₁) σ) →
        cutTo (workIn S₂) (c₂.run H ρ) = c₂.run H ρ ∧
          cutTo (workIn T₂) (c₂.run H ρ) = embed (liftQ ι) (cutTo (workIn T₁) (c₁.run H σ))
  | nil, nil, _, _, _, hS, hT => ⟨hS, hT⟩
  | kraus K₁ c₁, kraus K₂ c₂, ⟨hK, hc⟩, σ, ρ, hS, hT => by
    obtain ⟨hS', hT'⟩ := hK σ ρ hS hT
    exact Sim.run H (c₁ := c₁) (c₂ := c₂) hc _ _ hS' hT'
  | rquery a₁ c₁, rquery a₂ c₂, ⟨ha, hc⟩, σ, ρ, hS, hT => by
    refine Sim.run H (c₁ := c₁) (c₂ := c₂) hc _ _ ?_ (cutTo_embed_submatrix_query H ha σ hT)
    rw [cutTo_submatrix (fun p => Iff.rfl), hS]
  | nil, kraus _ _, h, _, _, _, _ => h.elim
  | nil, rquery _ _, h, _, _, _, _ => h.elim
  | kraus _ _, nil, h, _, _, _, _ => h.elim
  | kraus _ _, rquery _ _, h, _, _, _, _ => h.elim
  | rquery _ _, nil, h, _, _, _, _ => h.elim
  | rquery _ _, kraus _ _, h, _, _, _, _ => h.elim

omit [DecidableEq V₁] [Fintype V₂] in
/-- The part on `T₂` of a placed matrix is the placed part on `T₁`, when `T₁` is the preimage of
`T₂`. -/
theorem cutTo_embed (hT : ∀ v, ι v ∈ T₂ ↔ v ∈ T₁) (σ : Matrix (QueryReg V₁ 1 X Y) _ ℂ) :
    cutTo (workIn T₂) (embed (liftQ ι) σ) = embed (liftQ ι) (cutTo (workIn T₁) σ) := by
  classical
  ext i j
  simp only [cutTo, embed, workIn, Set.mem_ofPred_eq]
  split_ifs with h
  · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    by_cases hab : liftQ ι a = i ∧ liftQ ι b = j
    · obtain ⟨rfl, rfl⟩ := hab
      simp only [liftQ, Prod.map_fst, hT] at h
      simp [liftQ, h]
    · simp [hab]
  · symm
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    by_cases hab : liftQ ι a = i ∧ liftQ ι b = j
    · obtain ⟨rfl, rfl⟩ := hab
      simp only [liftQ, Prod.map_fst, hT] at h
      simp [liftQ, h]
    · simp [hab]

/-- **Kraus maps intertwined along `ι` that keep the sets are simulated.** -/
theorem KSim.of_intertwine {R : Type} [Fintype R]
    {K₁ : KrausMap R (QueryReg V₁ 1 X Y) (QueryReg V₁ 1 X Y)}
    {K₂ : KrausMap R (QueryReg V₂ 1 X Y) (QueryReg V₂ 1 X Y)}
    (h : ∀ r, K₂.op r * jmat (liftQ ι) = jmat (liftQ ι) * K₁.op r)
    (hS₂ : ∀ r i j, K₂.op r i j ≠ 0 → (i ∈ workIn S₂ ↔ j ∈ workIn S₂))
    (hT₂ : ∀ r i j, K₂.op r i j ≠ 0 → (i ∈ workIn T₂ ↔ j ∈ workIn T₂))
    (hT₁ : ∀ r i j, K₁.op r i j ≠ 0 → (i ∈ workIn T₁ ↔ j ∈ workIn T₁)) :
    KSim ι T₁ S₂ T₂ K₁ K₂ := by
  intro σ ρ hS hTρ
  refine ⟨by rw [K₂.cutTo_apply_of_keeps hS₂, hS], ?_⟩
  rw [K₂.cutTo_apply_of_keeps hT₂, hTρ, KrausMap.apply_embed_of_intertwine h,
    K₁.cutTo_apply_of_keeps hT₁]

/-- A basis permutation that commutes with `ι` intertwines along it. -/
theorem ofPerm_intertwine {π₁ : Equiv.Perm (QueryReg V₁ 1 X Y)}
    {π₂ : Equiv.Perm (QueryReg V₂ 1 X Y)} (h : ∀ a, π₂ (liftQ ι a) = liftQ ι (π₁ a)) (r : Unit) :
    (KrausMap.ofPerm π₂).op r * jmat (liftQ ι) = jmat (liftQ ι) * (KrausMap.ofPerm π₁).op r := by
  ext i a
  simp only [Matrix.mul_apply, KrausMap.ofPerm_op_apply, jmat]
  rw [Finset.sum_eq_single (liftQ ι a) (fun b _ hb => by simp [Ne.symm hb]) (by simp),
    Finset.sum_eq_single (π₁ a) (fun b _ hb => by simp [hb]) (by simp)]
  simp [h, eq_comm]

/-- The measurement of a function that agrees along `ι` intertwines along it. -/
theorem measureFn_intertwine {M : Type} [Fintype M] [DecidableEq M] {f₁ : QueryReg V₁ 1 X Y → M}
    {f₂ : QueryReg V₂ 1 X Y → M} (h : ∀ a, f₂ (liftQ ι a) = f₁ a) (m : M) :
    (KrausMap.measureFn f₂).op m * jmat (liftQ ι) = jmat (liftQ ι) * (KrausMap.measureFn f₁).op m := by
  ext i a
  simp only [KrausMap.measureFn, Matrix.diagonal_mul, Matrix.mul_diagonal, jmat]
  by_cases hi : liftQ ι a = i
  · subst hi
    simp [h]
  · simp [hi]

/-- Intertwining along `ι` is kept by composition. -/
theorem comp_intertwine {R₁ R₂ : Type} [Fintype R₁] [Fintype R₂]
    {K₁ : KrausMap R₁ (QueryReg V₁ 1 X Y) (QueryReg V₁ 1 X Y)}
    {K₁' : KrausMap R₁ (QueryReg V₂ 1 X Y) (QueryReg V₂ 1 X Y)}
    {K₂ : KrausMap R₂ (QueryReg V₁ 1 X Y) (QueryReg V₁ 1 X Y)}
    {K₂' : KrausMap R₂ (QueryReg V₂ 1 X Y) (QueryReg V₂ 1 X Y)}
    (h₁ : ∀ r, K₁'.op r * jmat (liftQ ι) = jmat (liftQ ι) * K₁.op r)
    (h₂ : ∀ r, K₂'.op r * jmat (liftQ ι) = jmat (liftQ ι) * K₂.op r) (r : R₁ × R₂) :
    (K₂'.comp K₁').op r * jmat (liftQ ι) = jmat (liftQ ι) * (K₂.comp K₁).op r := by
  simp only [KrausMap.comp]
  rw [Matrix.mul_assoc, h₁, ← Matrix.mul_assoc, h₂, Matrix.mul_assoc]

/-- The basis map of query registers with the ancilla along a map of work registers. -/
def liftR (ι : V₁ → V₂) : ReprogrammedQueryReg V₁ X Y → ReprogrammedQueryReg V₂ X Y :=
  fun p => ((ι p.1.1, p.1.2), p.2)

omit [Fintype V₁] [DecidableEq V₁] [Fintype V₂] [DecidableEq V₂] [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] in
theorem liftR_injective {ι : V₁ → V₂} (h : Function.Injective ι) :
    Function.Injective (liftR (X := X) (Y := Y) ι) := fun a b hab => by
  have h1 : (liftR ι a).1.1 = (liftR (X := X) (Y := Y) ι b).1.1 := congrArg (fun p => p.1.1) hab
  have h2 : (liftR ι a).1.2 = (liftR (X := X) (Y := Y) ι b).1.2 := congrArg (fun p => p.1.2) hab
  have h3 : (liftR ι a).2 = (liftR (X := X) (Y := Y) ι b).2 := congrArg Prod.snd hab
  exact Prod.ext (Prod.ext (h h1) h2) h3

omit [DecidableEq V₁] in
/-- **Appending the clean ancilla commutes with placing along a map of work registers.** -/
theorem withAnc_embed {ι : V₁ → V₂} (hι : Function.Injective ι) (x₀ : X)
    (σ : Matrix (QueryReg V₁ 1 X Y) (QueryReg V₁ 1 X Y) ℂ) :
    withAnc x₀ (embed (liftQ ι) σ) = embed (liftR ι) (withAnc x₀ σ) := by
  classical
  have hr : ∀ q : ReprogrammedQueryReg V₂ X Y, (∃ b, liftQ ι b = (q.1.1, q.2)) →
      ∃ a, liftR ι a = q := by
    rintro q ⟨b, hb⟩
    refine ⟨((b.1, q.1.2), b.2), ?_⟩
    have h1 : ι b.1 = q.1.1 := congrArg Prod.fst hb
    have h2 : b.2 = q.2 := congrArg Prod.snd hb
    exact Prod.ext (Prod.ext h1 rfl) h2
  ext p p'
  by_cases hp : ∃ a, liftR ι a = p
  · by_cases hp' : ∃ b, liftR ι b = p'
    · obtain ⟨a, rfl⟩ := hp
      obtain ⟨b, rfl⟩ := hp'
      rw [embed_apply_of_injective (liftR_injective hι)]
      simp only [withAnc]
      exact congrArg (· * _) (embed_apply_of_injective (liftQ_injective hι) σ (a.1.1, a.2)
        (b.1.1, b.2))
    · rw [embed_apply_of_notMem_right _ _ (fun b hb => hp' ⟨b, hb⟩)]
      simp only [withAnc]
      rw [embed_apply_of_notMem_right _ _ (fun b hb => hp' (hr p' ⟨b, hb⟩)), zero_mul]
  · rw [embed_apply_of_notMem_left _ (fun a ha => hp ⟨a, ha⟩)]
    simp only [withAnc]
    rw [embed_apply_of_notMem_left _ (fun b hb => hp (hr p ⟨b, hb⟩)), zero_mul]

end ReprogrammedCircuit

/-! ### The aborting completion -/

namespace AdaptiveIAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  (A : AdaptiveIAlg X Y Req Resp O)

/-- **The aborting completion of an adversary**: the adversary that keeps its own count of query
slots in its workspace, aborts a branch that asks for a query slot over `budget` (or that the
adversary's Kraus maps lose) by moving its counter to the ended value, and requests at every later
slot of an ended branch. Its steps are those of the trace-preserving form `toTPKindAlg`, and its
output is the adversary's, read from the workspace without the counter. -/
noncomputable def abortAlg : AdaptiveIAlg X Y Req Resp O where
  W := A.W × Fin (A.budget + 2)
  width := A.width
  width_pos := A.width_pos
  slots := A.slots
  post := A.post
  budget := A.budget
  kind := A.toTPKindAlg.kind
  R := A.toTPKindAlg.R
  init := A.toTPKindAlg.init
  step := A.toTPKindAlg.step
  out := A.toTPKindAlg.out

/-- **The aborting completion is trace preserving**, whatever the adversary. -/
theorem tracePreserving_abortAlg : A.abortAlg.TracePreserving :=
  A.toTPKindAlg_step_tp

/-- The halting operators of the aborting completion are zero. -/
theorem haltOp_abortAlg (k : StepIdx A.slots A.post) : (A.abortAlg.step k).haltOp = 0 :=
  A.tracePreserving_abortAlg.haltOp_eq_zero k

/-- **The counters of the aborting completion's trace-preserving form**: the outer counter (of the
trace-preserving form) has not ended, and on a branch whose inner counter (the completion's own)
has not ended the two agree. -/
def counterInv : Set A.abortAlg.toTPKindAlg.W :=
  {w | w.2 ≠ A.ended ∧ (w.1.2 ≠ A.ended → w.1.2 = w.2)}

theorem cntSplit_fst_workspace (y : A.abortAlg.CReg) :
    (A.abortAlg.cntSplit y).1.workspace = y.workspace.1 :=
  rfl

theorem val_ended : ((A.ended : Fin (A.budget + 2)) : ℕ) = A.budget + 1 :=
  rfl

theorem ne_ended_iff (c : Fin (A.budget + 2)) : c ≠ A.ended ↔ (c : ℕ) ≤ A.budget := by
  constructor
  · intro h
    have h1 : (c : ℕ) ≠ A.budget + 1 := fun h' => h (Fin.ext h')
    omega
  · intro h h'
    rw [h', val_ended] at h
    omega


/-! #### The aborting completion's trace-preserving steps on registers with equal counters -/

/-- The register determines its part without the counter and the counter. -/
theorem cntSplit_ext {u v : A.CReg} (h1 : (A.cntSplit u).1 = (A.cntSplit v).1)
    (h2 : u.workspace.2 = v.workspace.2) : u = v :=
  A.cntSplit.injective (Prod.ext h1 h2)

/-- The counter step keeps the register without the counter. -/
theorem cntSplit_fst_tpShift (u : A.CReg) : (A.cntSplit (A.tpShift u)).1 = (A.cntSplit u).1 :=
  rfl

/-- The exchange of the counter values `budget` and `ended` keeps the register without the
counter. -/
theorem cntSplit_fst_endSwap (u : A.CReg) : (A.cntSplit (A.endSwap u)).1 = (A.cntSplit u).1 :=
  rfl

theorem cntSplit_fst_tpShift_symm (u : A.CReg) :
    (A.cntSplit (A.tpShift.symm u)).1 = (A.cntSplit u).1 := by
  rw [← A.cntSplit_fst_tpShift, Equiv.apply_symm_apply]

theorem cntSplit_fst_endSwap_symm (u : A.CReg) :
    (A.cntSplit (A.endSwap.symm u)).1 = (A.cntSplit u).1 := by
  rw [← A.cntSplit_fst_endSwap, Equiv.apply_symm_apply]

/-- **The register of the aborting completion's trace-preserving form with both counters equal to
the counter of `d`** (proof-internal). -/
noncomputable def liftD (d : A.CReg) : A.abortAlg.CReg :=
  A.abortAlg.cntSplit.symm (d, d.workspace.2)

theorem cntSplit_liftD (d : A.CReg) : A.abortAlg.cntSplit (A.liftD d) = (d, d.workspace.2) :=
  Equiv.apply_symm_apply _ _

theorem liftD_injective : Function.Injective A.liftD := fun a b h => by
  have := congrArg (fun u => (A.abortAlg.cntSplit u).1) h
  simp only [cntSplit_liftD] at this
  exact this

/-- The kind of the aborting completion on a workspace whose counter has not ended is the
adversary's. -/
theorem abortAlg_kind_of_ne {w : A.W × Fin (A.budget + 2)} (hw : w.2 ≠ A.ended) :
    A.abortAlg.kind w = A.kind w.1 := by
  change (A.kind w.1 || decide (w.2 = A.ended)) = _
  rw [decide_eq_false hw, Bool.or_false]

theorem abortAlg_step_op (k : StepIdx A.abortAlg.slots A.abortAlg.post) (r : A.abortAlg.R) (y x : A.CReg) :
    (A.abortAlg.step k).op r y x = A.tpOp k r y x :=
  rfl

/-- **On registers with equal counters that have not ended, the aborting completion's
trace-preserving operators are the trace-preserving form's.** -/
theorem tpOp_abortAlg_inl (k : StepIdx A.abortAlg.slots A.abortAlg.post) (r : A.abortAlg.R)
    {y : A.CReg} (x : A.CReg) (hy : y.workspace.2 ≠ A.ended) :
    A.abortAlg.tpOp k (.inl r) (A.liftD y) (A.liftD x) = A.tpOp k r y x := by
  have ey : ((A.liftD y).workspace.2 : ℕ) = y.workspace.2 :=
    congrArg (fun p => (p.2 : ℕ)) (A.cntSplit_liftD y)
  have ex : ((A.liftD x).workspace.2 : ℕ) = x.workspace.2 :=
    congrArg (fun p => (p.2 : ℕ)) (A.cntSplit_liftD x)
  by_cases hk : (k : ℕ) < A.slots
  · conv_lhs => simp only [tpOp, show (k : ℕ) < A.abortAlg.slots from hk, if_true,
      restrict_permConj_op_apply]
    rw [cntKraus_op_apply, cntSplit_fst_tpShift_symm, cntSplit_liftD, cntSplit_liftD,
      abortAlg_step_op]
    by_cases hA : A.tpOp k r y x = 0
    · rw [hA]
      simp
    · have hc := A.tp_slot_counter hk r y x hA
      rcases hc with hc | ⟨hxe, hc, hlt⟩
      · exact absurd hc hy
      set u₀ : A.abortAlg.CReg := A.abortAlg.cntSplit.symm (y, x.workspace.2)
      have hu₀ : A.abortAlg.cntSplit u₀ = (y, x.workspace.2) := Equiv.apply_symm_apply _ _
      have e1 : u₀.workspace.1 = y.workspace := congrArg (fun p => p.1.workspace) hu₀
      have e2 : (u₀.workspace.2 : ℕ) = x.workspace.2 := congrArg (fun p => (p.2 : ℕ)) hu₀
      have hb : A.abortAlg.inBudget u₀ = true := by
        rw [inBudget_of_alive_kind]
        by_cases hkd : A.kind y.workspace.1 = true
        · left
          rw [e1, A.abortAlg_kind_of_ne hy]
          exact hkd
        · right
          have h1 := hlt (by simpa using hkd)
          intro h
          have := congrArg Fin.val h
          rw [e2] at this
          simp only [Fin.coe_castSucc, Fin.val_last] at this
          change (x.workspace.2 : ℕ) = A.budget at this
          omega
      have ha : u₀ ∈ A.abortAlg.aliveD := by
        change u₀.workspace.2 ≠ A.ended
        intro h
        have := congrArg Fin.val h
        rw [e2] at this
        exact hxe (Fin.ext this)
      obtain ⟨-, h2, -⟩ := A.abortAlg.tpShift_counter hb ha
      have hshift : A.abortAlg.tpShift u₀ = A.liftD y := by
        refine A.abortAlg.cntSplit_ext ?_ ?_
        · rw [cntSplit_fst_tpShift, hu₀, cntSplit_liftD]
        · apply Fin.ext
          rw [h2, e2, e1, A.abortAlg_kind_of_ne hy, ey, hc]
      have hu : A.abortAlg.tpShift.symm (A.liftD y) = u₀ := by
        rw [← hshift, Equiv.symm_apply_apply]
      have e4 : u₀.workspace.2 = (A.liftD x).workspace.2 := Fin.ext (by rw [e2, ex])
      rw [hu, hb, e4, Matrix.one_apply_eq]
      simp
  · conv_lhs => simp only [tpOp, show ¬ (k : ℕ) < A.abortAlg.slots from hk, if_false]
    rw [cntKraus_op_apply, cntSplit_liftD, cntSplit_liftD, abortAlg_step_op]
    by_cases hA : A.tpOp k r y x = 0
    · rw [hA]
      simp
    · rcases A.tp_post_counter hk r y x hA with hc | hc
      · exact absurd hc hy
      · have e : (A.liftD y).workspace.2 = (A.liftD x).workspace.2 :=
          Fin.ext (by rw [ey, ex, hc])
        rw [e, Matrix.one_apply_eq, mul_one]

/-- **On registers with equal counters that have not ended, the extra operators of the aborting
completion's trace-preserving form vanish.** -/
theorem tpOp_abortAlg_inr (k : StepIdx A.abortAlg.slots A.abortAlg.post)
    (t : A.abortAlg.R ⊕ Fin (A.abortAlg.budget + 2)) {y : A.CReg} (x : A.CReg)
    (hy : y.workspace.2 ≠ A.ended) :
    A.abortAlg.tpOp k (.inr t) (A.liftD y) (A.liftD x) = 0 := by
  have ex : ((A.liftD x).workspace.2 : ℕ) = x.workspace.2 :=
    congrArg (fun p => (p.2 : ℕ)) (A.cntSplit_liftD x)
  rcases t with r | c
  · by_cases hk : (k : ℕ) < A.slots
    · simp only [tpOp, show (k : ℕ) < A.abortAlg.slots from hk, if_true,
        restrict_permConj_op_apply]
      by_contra hne
      set v := A.abortAlg.endSwap.symm (A.liftD y)
      have hb : A.abortAlg.inBudget v = false := by
        by_contra hb
        have hb' : A.abortAlg.inBudget v = true := by simpa using hb
        exact hne (by simp [hb'])
      have hK : (A.abortAlg.cntKraus k).op r v (A.liftD x) ≠ 0 := fun h' =>
        hne (by rw [h', mul_zero])
      have hc := A.abortAlg.cntKraus_op_ne_zero hK
      rw [cntKraus_op_apply, cntSplit_fst_endSwap_symm, cntSplit_liftD, cntSplit_liftD,
        abortAlg_step_op] at hK
      have hin := A.tp_slot_counter hk r y x (left_ne_zero_of_mul hK)
      have hv := (A.abortAlg.inBudget_of_alive_kind v).not.1 (by rw [hb]; exact Bool.false_ne_true)
      rw [not_or, not_not] at hv
      obtain ⟨hvk, hvb⟩ := hv
      have hvw : v.workspace.1 = y.workspace := by
        have := A.abortAlg.cntSplit_fst_endSwap_symm (A.liftD y)
        rw [cntSplit_liftD] at this
        exact congrArg (fun p => p.workspace) this
      rw [hvw, A.abortAlg_kind_of_ne hy] at hvk
      rcases hin with hin | ⟨-, -, hlt⟩
      · exact hy hin
      · have h1 := hlt (by simpa using hvk)
        have hxv : (x.workspace.2 : ℕ) = A.budget := by
          have := congrArg Fin.val (hc.symm.trans hvb)
          simp only [Fin.coe_castSucc, Fin.val_last] at this
          rw [ex] at this
          exact this
        omega
    · simp [tpOp, show ¬ (k : ℕ) < A.abortAlg.slots from hk]
  · simp [tpOp, A.haltOp_abortAlg k]

/-- **An ended branch stays ended under the aborting completion's trace-preserving steps**: a
register whose inner counter has ended is sent only to registers whose inner counter has ended. -/
theorem tpOp_abortAlg_absorb (k : StepIdx A.abortAlg.slots A.abortAlg.post)
    (z : A.abortAlg.R ⊕ (A.abortAlg.R ⊕ Fin (A.abortAlg.budget + 2))) (y a : A.abortAlg.CReg)
    (h : A.abortAlg.tpOp k z y a ≠ 0) (ha : a.workspace.1.2 = A.ended) :
    y.workspace.1.2 = A.ended := by
  have habs : ∀ (r : A.abortAlg.R) (u : A.abortAlg.CReg),
      (A.abortAlg.cntKraus k).op r u a ≠ 0 → u.workspace.1.2 = A.ended := by
    intro r u hu
    rw [cntKraus_op_apply] at hu
    have := A.tp_habs k r _ _ (left_ne_zero_of_mul hu) (fun h => h ha)
    by_contra hne
    exact this hne
  rcases z with r | r | c
  · by_cases hk : (k : ℕ) < A.slots
    · simp only [tpOp, show (k : ℕ) < A.abortAlg.slots from hk, if_true,
        restrict_permConj_op_apply] at h
      have := habs r _ (right_ne_zero_of_mul h)
      have e := congrArg (fun p => p.workspace.2) (A.abortAlg.cntSplit_fst_tpShift_symm y)
      exact e.symm.trans this
    · simp only [tpOp, show ¬ (k : ℕ) < A.abortAlg.slots from hk, if_false] at h
      exact habs r y h
  · by_cases hk : (k : ℕ) < A.slots
    · simp only [tpOp, show (k : ℕ) < A.abortAlg.slots from hk, if_true,
        restrict_permConj_op_apply] at h
      have := habs r _ (right_ne_zero_of_mul h)
      have e := congrArg (fun p => p.workspace.2) (A.abortAlg.cntSplit_fst_endSwap_symm y)
      exact e.symm.trans this
    · simp [tpOp, show ¬ (k : ℕ) < A.abortAlg.slots from hk] at h
  · simp [tpOp, A.haltOp_abortAlg k] at h

variable [Nonempty X] [AddGroup Y] [Nonempty Y]

/-- **The counters of the aborting completion agree**: its trace-preserving form keeps
`counterInv`. -/
theorem invariant_counterInv : A.abortAlg.toTPKindAlg.Invariant A.counterInv := by
  constructor
  · intro a b hab
    have hz : ∀ d : A.abortAlg.CReg, A.abortAlg.toTPKindAlg.init.mat a b ≠ 0 →
        (d = a ∨ d = b) → d.workspace.2 = 0 ∧ d.workspace.1.2 = 0 := by
      intro d hne hd
      have h1 : a.workspace.2 = 0 ∧ b.workspace.2 = 0 := by
        by_contra h
        exact hne (A.abortAlg.init_mat_eq_zero a b (by tauto))
      have he : A.abortAlg.toTPKindAlg.init.mat a b =
          A.toKindAlg.init.mat (A.abortAlg.cntSplit a).1 (A.abortAlg.cntSplit b).1 *
            Matrix.single (0 : Fin (A.budget + 2)) 0 (1 : ℂ) a.workspace.2 b.workspace.2 :=
        rfl
      rw [he] at hne
      have h2 := left_ne_zero_of_mul hne
      have h2' : (A.abortAlg.cntSplit a).1.workspace.2 = 0 ∧
          (A.abortAlg.cntSplit b).1.workspace.2 = 0 := by
        by_contra h
        exact h2 (A.init_mat_eq_zero _ _ (by tauto))
      rcases hd with rfl | rfl
      · exact ⟨h1.1, h2'.1⟩
      · exact ⟨h1.2, h2'.2⟩
    have hS : ∀ d, (d = a ∨ d = b) → d.workspace ∈ A.counterInv := by
      intro d hd
      obtain ⟨h1, h2⟩ := hz d hab hd
      refine ⟨?_, fun _ => ?_⟩
      · rw [h1]
        exact (A.ne_ended_iff 0).2 (Nat.zero_le _)
      · exact h2.trans h1.symm
    exact ⟨hS a (Or.inl rfl), hS b (Or.inr rfl)⟩
  · intro (k : StepIdx A.abortAlg.slots A.abortAlg.post)
      (z : A.abortAlg.R ⊕ (A.abortAlg.R ⊕ Fin (A.abortAlg.budget + 2)))
      (y : A.abortAlg.CReg) (x : A.abortAlg.CReg) h hx
    obtain ⟨hxo, hxi⟩ := hx
    change A.abortAlg.tpOp k z y x ≠ 0 at h
    rcases z with r | r | c
    · by_cases hk : (k : ℕ) < A.slots
      · simp only [tpOp, show (k : ℕ) < A.abortAlg.slots from hk, if_true,
          restrict_permConj_op_apply] at h
        set u := A.abortAlg.tpShift.symm y
        have huy : A.abortAlg.tpShift u = y := Equiv.apply_symm_apply _ _
        have hb : A.abortAlg.inBudget u = true := by
          by_contra hb
          exact h (by simp [hb])
        have hK : (A.abortAlg.cntKraus k).op r u x ≠ 0 := fun h' => h (by rw [h', mul_zero])
        have hc := A.abortAlg.cntKraus_op_ne_zero hK
        rw [cntKraus_op_apply] at hK
        have hA := left_ne_zero_of_mul hK
        have ha : u ∈ A.abortAlg.aliveD := by
          simp only [aliveD, Set.mem_ofPred_eq, hc]
          exact hxo
        obtain ⟨h1, h2, h3⟩ := A.abortAlg.tpShift_counter hb ha
        rw [huy] at h1 h2
        have hin := A.tp_slot_counter hk r _ _ hA
        rw [cntSplit_fst_workspace, cntSplit_fst_workspace] at hin
        refine ⟨?_, fun hyi => ?_⟩
        · refine (A.ne_ended_iff _).2 ?_
          change (y.workspace.2 : ℕ) ≤ A.budget
          rw [h2, hc]
          have hxo' := (A.ne_ended_iff _).1 hxo
          by_cases hkd : A.abortAlg.kind u.workspace.1 = true
          · simp only [hkd, if_true, add_zero]
            exact hxo'
          · have := h3 (by simpa using hkd)
            rw [hc] at this
            simp only [hkd, Bool.false_eq_true, if_false]
            exact this
        · rw [h1] at hyi
          rcases hin with hin | ⟨hxi', hin, -⟩
          · exact absurd hin hyi
          · apply Fin.ext
            rw [h2, h1, hin, hxi hxi', hc]
            have hkind : A.abortAlg.kind u.workspace.1 = A.kind u.workspace.1.1 := by
              change (A.kind _ || decide (_ = A.ended)) = _
              rw [decide_eq_false hyi, Bool.or_false]
            rw [hkind]
      · simp only [tpOp, show ¬ (k : ℕ) < A.abortAlg.slots from hk, if_false] at h
        have hc := A.abortAlg.cntKraus_op_ne_zero h
        rw [cntKraus_op_apply] at h
        have hin := A.tp_post_counter hk r _ _ (left_ne_zero_of_mul h)
        rw [cntSplit_fst_workspace, cntSplit_fst_workspace] at hin
        refine ⟨by rw [hc]; exact hxo, fun hyi => ?_⟩
        rcases hin with hin | hin
        · exact absurd hin hyi
        · rw [hin, hc]
          exact hxi (hin ▸ hyi)
    · exfalso
      by_cases hk : (k : ℕ) < A.slots
      · simp only [tpOp, show (k : ℕ) < A.abortAlg.slots from hk, if_true,
          restrict_permConj_op_apply] at h
        set v := A.abortAlg.endSwap.symm y
        have hb : A.abortAlg.inBudget v = false := by
          by_contra hb
          have hb' : A.abortAlg.inBudget v = true := by simpa using hb
          exact h (by simp [hb'])
        have hK : (A.abortAlg.cntKraus k).op r v x ≠ 0 := fun h' => h (by rw [h', mul_zero])
        have hc := A.abortAlg.cntKraus_op_ne_zero hK
        rw [cntKraus_op_apply] at hK
        have hin := A.tp_slot_counter hk r _ _ (left_ne_zero_of_mul hK)
        rw [cntSplit_fst_workspace, cntSplit_fst_workspace] at hin
        have hv := (A.abortAlg.inBudget_of_alive_kind v).not.1 (by rw [hb]; exact Bool.false_ne_true)
        rw [not_or, not_not] at hv
        obtain ⟨hvk, hvb⟩ := hv
        have hvk' : A.kind v.workspace.1.1 = false ∧ v.workspace.1.2 ≠ A.ended := by
          have : (A.kind v.workspace.1.1 || decide (v.workspace.1.2 = A.ended)) = false :=
            Bool.not_eq_true _ ▸ hvk
          rw [Bool.or_eq_false_iff, decide_eq_false_iff_not] at this
          exact this
        rcases hin with hin | ⟨hxi', -, hlt⟩
        · exact hvk'.2 hin
        · have h1 := hlt hvk'.1
          rw [hxi hxi', ← hc, hvb] at h1
          exact lt_irrefl A.budget h1
      · simp [tpOp, show ¬ (k : ℕ) < A.abortAlg.slots from hk] at h
    · exfalso
      simp [tpOp, A.haltOp_abortAlg k] at h

/-- **The aborting completion of any adversary is within its budget.** -/
theorem withinBudget_abortAlg : A.abortAlg.WithinBudget := by
  intro C H
  rw [Alg.outLaw]
  refine (map_basisLaw_apply_some _ _ _ _ true).trans (Finset.sum_eq_zero fun p _ => ?_)
  split_ifs with hc
  · have hp : p.1.1.adv.workspace ∉ A.counterInv := by
      have : A.abortAlg.endedFlag C p.1.1 = true := (Option.some_inj.1 hc).symm
      simp only [endedFlag, decide_eq_true_eq] at this
      exact fun h => h.1 this
    rw [A.invariant_counterInv.final_apply_eq_zero C _ H hp, Complex.zero_re, ENNReal.ofReal_zero]
  · rfl

/-! ### The aborting completion does not change an adversary within its budget -/

section Simulation

variable (C : Challenger X Y Req Resp)

open ReprogrammedCircuit

/-- **The composed register of the aborting completion's trace-preserving form with both counters
equal to the counter of `v`** (proof-internal). -/
noncomputable def liftCW (v : A.toTPKindAlg.CW C) : A.abortAlg.toTPKindAlg.CW C :=
  ⟨A.liftD v.adv, v.chal⟩

omit [Nonempty X] [AddGroup Y] [Nonempty Y] in
theorem liftCW_injective : Function.Injective (A.liftCW C) := fun a b h => by
  have h1 : A.liftD a.adv = A.liftD b.adv := congrArg CWork.adv h
  have h2 : (A.liftCW C a).chal = (A.liftCW C b).chal := congrArg CWork.chal h
  exact CWork.ext (A.liftD_injective h1) h2

omit [Nonempty X] [AddGroup Y] [Nonempty Y] in
theorem liftD_workspace (d : A.CReg) : (A.liftD d).workspace = (d.workspace, d.workspace.2) :=
  rfl

/-- The workspaces of the trace-preserving form whose counter has not ended. -/
def aliveW : Set A.toTPKindAlg.W := {w | w.2 ≠ A.ended}

/-- The workspaces of the aborting completion's trace-preserving form whose inner counter has not
ended and equals the outer one. -/
def equalW : Set A.abortAlg.toTPKindAlg.W := {w | w.1.2 ≠ A.ended ∧ w.2 = w.1.2}

omit [Nonempty X] [AddGroup Y] [Nonempty Y] in
theorem liftCW_mem_equal (v : A.toTPKindAlg.CW C) :
    A.liftCW C v ∈ A.abortAlg.toTPKindAlg.advIn C A.equalW ↔
      v ∈ A.toTPKindAlg.advIn C A.aliveW := by
  change (v.adv.workspace.2 ≠ A.ended ∧ v.adv.workspace.2 = v.adv.workspace.2) ↔
    v.adv.workspace.2 ≠ A.ended
  simp

omit [Nonempty X] [AddGroup Y] [Nonempty Y] in
theorem equal_subset_inv : workIn (X := X) (Y := Y) (A.abortAlg.toTPKindAlg.advIn C A.equalW) ⊆
    workIn (A.abortAlg.toTPKindAlg.advIn C A.counterInv) := fun _ hv =>
  ⟨fun h => hv.1 (hv.2 ▸ h), fun _ => hv.2.symm⟩

omit [Nonempty X] [AddGroup Y] [Nonempty Y] in
/-- Every register on which both counters agree and have not ended is lifted. -/
theorem exists_liftQ {i : QueryReg (A.abortAlg.toTPKindAlg.CW C) 1 X Y}
    (hi : i ∈ workIn (A.abortAlg.toTPKindAlg.advIn C A.equalW)) :
    ∃ b, b ∈ workIn (A.toTPKindAlg.advIn C A.aliveW) ∧ liftQ (A.liftCW C) b = i := by
  refine ⟨(⟨(A.abortAlg.cntSplit i.1.adv).1, i.1.chal⟩, i.2), hi.1, ?_⟩
  refine Prod.ext (CWork.ext (A.abortAlg.cntSplit.injective (Prod.ext rfl ?_)) rfl) rfl
  exact hi.2.symm

omit [Nonempty X] [AddGroup Y] [Nonempty Y] in
/-- The adversary's Kraus map of the aborting completion's form, on lifted registers. -/
theorem advKraus_abortAlg_op_lift (k : StepIdx A.slots A.post)
    (z : A.abortAlg.toTPKindAlg.R) (a b : QueryReg (A.toTPKindAlg.CW C) 1 X Y) :
    (A.abortAlg.toTPKindAlg.advKraus C k).op z (liftQ (A.liftCW C) a) (liftQ (A.liftCW C) b) =
      A.abortAlg.tpOp k z (A.liftD a.1.adv) (A.liftD b.1.adv) *
        (1 : Matrix (CRest X Y Req A.toTPKindAlg.slots C.q C.Coins) _ ℂ) (a.1.chal, a.2)
          (b.1.chal, b.2) :=
  KrausMap.tensorId_reindex_op_apply _ _ _ _ _

omit [Nonempty X] [AddGroup Y] [Nonempty Y] in
theorem advKraus_op_apply' (k : StepIdx A.slots A.post) (r : A.toTPKindAlg.R)
    (a b : QueryReg (A.toTPKindAlg.CW C) 1 X Y) :
    (A.toTPKindAlg.advKraus C k).op r a b =
      A.tpOp k r a.1.adv b.1.adv *
        (1 : Matrix (CRest X Y Req A.toTPKindAlg.slots C.q C.Coins) _ ℂ) (a.1.chal, a.2)
          (b.1.chal, b.2) :=
  KrausMap.tensorId_reindex_op_apply _ _ _ _ _

/-- **The adversary's Kraus maps are simulated** along the lift. -/
theorem ksim_advKraus (k : StepIdx A.slots A.post) :
    KSim (A.liftCW C) (A.toTPKindAlg.advIn C A.aliveW)
      (A.abortAlg.toTPKindAlg.advIn C A.counterInv) (A.abortAlg.toTPKindAlg.advIn C A.equalW)
      (A.toTPKindAlg.advKraus C k) (A.abortAlg.toTPKindAlg.advKraus C k) := by
  classical
  intro σ ρ hS hT
  refine ⟨(A.invariant_counterInv.mapsInto_advKraus C k).cutTo_apply hS, ?_⟩
  set T₁ := workIn (X := X) (Y := Y) (A.toTPKindAlg.advIn C A.aliveW)
  set T₂ := workIn (X := X) (Y := Y) (A.abortAlg.toTPKindAlg.advIn C A.equalW)
  set K₁ := A.toTPKindAlg.advKraus C k
  set K₂ := A.abortAlg.toTPKindAlg.advKraus C k
  set ι := liftQ (X := X) (Y := Y) (A.liftCW C)
  -- the ended branches of the aborting form never return
  have habs₂ : ∀ z i a, K₂.op z i a ≠ 0 →
      a ∈ workIn (A.abortAlg.toTPKindAlg.advIn C A.counterInv) → a ∉ T₂ → i ∉ T₂ := by
    intro z i a h ha haT hiT
    have hae : a.1.adv.workspace.1.2 = A.ended := by
      by_contra hne
      exact haT ⟨hne, (ha.2 hne).symm⟩
    rw [show K₂.op z i a = _ from KrausMap.tensorId_reindex_op_apply _ _ _ _ _] at h
    exact hiT.1 (A.tpOp_abortAlg_absorb k z _ _ (left_ne_zero_of_mul h) hae)
  have habs₁ : ∀ r i a, K₁.op r i a ≠ 0 → a ∈ (Set.univ : Set _) → a ∉ T₁ → i ∉ T₁ := by
    intro r i a h _ haT hiT
    rw [advKraus_op_apply'] at h
    exact A.tp_habs k r _ _ (left_ne_zero_of_mul h) haT hiT
  have hcut₂ := KrausMap.cutTo_apply_of_absorb (A.equal_subset_inv C) habs₂ hS
  have hcut₁ := KrausMap.cutTo_apply_of_absorb (Set.subset_univ _) habs₁
    (ρ := σ) (by ext i j; simp [cutTo])
  rw [hcut₂, hT, hcut₁]
  set τ := cutTo T₁ σ
  have hτ : τ = projOn T₁ * τ * projOn T₁ := by rw [← cutTo_eq, cutTo_cutTo]
  set J := jmat ι
  set P₁ := projOn T₁
  set P₂ := projOn T₂
  -- the operators on lifted registers
  have hcl : ∀ r, P₂ * K₂.op (.inl r) * J * P₁ = J * P₁ * K₁.op r * P₁ := by
    intro r
    ext i a
    rw [projOn_mul_jmat_mul_projOn_apply, jmat_mul_projOn_mul_projOn_apply]
    by_cases ha : a ∈ T₁
    · rw [if_pos ha, mul_one, mul_one]
      by_cases hi : i ∈ T₂
      · obtain ⟨b₀, hb₀, rfl⟩ := A.exists_liftQ C hi
        rw [if_pos hi, one_mul, Finset.sum_eq_single b₀ (fun b _ hb => by
            rw [if_neg fun h => hb ((liftQ_injective (A.liftCW_injective C)) h.1)]) (by simp),
          if_pos ⟨rfl, hb₀⟩]
        change (A.abortAlg.toTPKindAlg.advKraus C k).op (.inl r) (ι b₀) (ι a) =
          (A.toTPKindAlg.advKraus C k).op r b₀ a
        rw [A.advKraus_abortAlg_op_lift C, A.tpOp_abortAlg_inl k r a.1.adv hb₀]
        exact (A.advKraus_op_apply' C k r b₀ a).symm
      · rw [if_neg hi, zero_mul]
        symm
        refine Finset.sum_eq_zero fun b _ => ?_
        rw [if_neg]
        rintro ⟨hb, hbT⟩
        subst hb
        exact hi ((A.liftCW_mem_equal C b.1).2 hbT)
    · simp [ha]
  have hcr : ∀ t, P₂ * K₂.op (.inr t) * J * P₁ = 0 := by
    intro t
    ext i a
    rw [projOn_mul_jmat_mul_projOn_apply, Matrix.zero_apply]
    by_cases ha : a ∈ T₁
    · by_cases hi : i ∈ T₂
      · obtain ⟨b₀, hb₀, rfl⟩ := A.exists_liftQ C hi
        change _ * (A.abortAlg.toTPKindAlg.advKraus C k).op (.inr t) (ι b₀) (ι a) * _ = 0
        rw [A.advKraus_abortAlg_op_lift C, A.tpOp_abortAlg_inr k t a.1.adv hb₀]
        simp
      · simp [hi]
    · simp [ha]
  have hP₁ : P₁ᴴ = P₁ := projOn_conjTranspose _
  have hP₂ : P₂ᴴ = P₂ := projOn_conjTranspose _
  have hsand : ∀ (z : A.abortAlg.toTPKindAlg.R),
      P₂ * (K₂.op z * (J * τ * Jᴴ) * (K₂.op z)ᴴ) * P₂ =
        (P₂ * K₂.op z * J * P₁) * τ * (P₂ * K₂.op z * J * P₁)ᴴ := by
    intro z
    conv_lhs => rw [hτ]
    simp only [Matrix.conjTranspose_mul, hP₁, hP₂, Matrix.mul_assoc]
  have hsand₁ : ∀ r, J * (P₁ * (K₁.op r * τ * (K₁.op r)ᴴ) * P₁) * Jᴴ =
      (J * P₁ * K₁.op r * P₁) * τ * (J * P₁ * K₁.op r * P₁)ᴴ := by
    intro r
    conv_lhs => rw [hτ]
    simp only [Matrix.conjTranspose_mul, hP₁, Matrix.mul_assoc]
  rw [embed_eq_jmat, embed_eq_jmat, KrausMap.apply, KrausMap.apply, cutTo_sum, cutTo_sum,
    Fintype.sum_sum_type, Matrix.mul_sum, Matrix.sum_mul]
  refine (congrArg₂ (· + ·) (Finset.sum_congr rfl fun r _ => ?_)
    (Finset.sum_eq_zero fun t _ => ?_)).trans (add_zero _)
  · rw [cutTo_eq, cutTo_eq]
    calc _ = (P₂ * K₂.op (.inl r) * J * P₁) * τ * (P₂ * K₂.op (.inl r) * J * P₁)ᴴ :=
          hsand (.inl r)
      _ = (J * P₁ * K₁.op r * P₁) * τ * (J * P₁ * K₁.op r * P₁)ᴴ := by rw [hcl r]
      _ = _ := (hsand₁ r).symm
  · rw [cutTo_eq]
    calc _ = (P₂ * K₂.op (.inr t) * J * P₁) * τ * (P₂ * K₂.op (.inr t) * J * P₁)ᴴ :=
          hsand (.inr t)
      _ = 0 := by rw [hcr t]; simp

/-- The sets of the simulation: lifted registers on `equalW` simulate registers on `aliveW`, and
the aborting form stays on `counterInv`. -/
abbrev SimTP : ReprogrammedCircuit (A.toTPKindAlg.CW C) X Y →
    ReprogrammedCircuit (A.abortAlg.toTPKindAlg.CW C) X Y → Prop :=
  Sim (A.liftCW C) (A.toTPKindAlg.advIn C A.aliveW)
    (A.abortAlg.toTPKindAlg.advIn C A.counterInv) (A.abortAlg.toTPKindAlg.advIn C A.equalW)

omit [Nonempty X] [AddGroup Y] [Nonempty Y] in
/-- A basis permutation that keeps the adversary's workspace and commutes with the lift is
simulated. -/
theorem ksim_ofPerm {π₁ : Equiv.Perm (QueryReg (A.toTPKindAlg.CW C) 1 X Y)}
    {π₂ : Equiv.Perm (QueryReg (A.abortAlg.toTPKindAlg.CW C) 1 X Y)}
    (h : ∀ a, π₂ (liftQ (A.liftCW C) a) = liftQ (A.liftCW C) (π₁ a))
    (hk₁ : ∀ p, (π₁ p).1.adv.workspace = p.1.adv.workspace)
    (hk₂ : ∀ p, (π₂ p).1.adv.workspace = p.1.adv.workspace) :
    KSim (A.liftCW C) (A.toTPKindAlg.advIn C A.aliveW)
      (A.abortAlg.toTPKindAlg.advIn C A.counterInv) (A.abortAlg.toTPKindAlg.advIn C A.equalW)
      (KrausMap.ofPerm π₁) (KrausMap.ofPerm π₂) :=
  KSim.of_intertwine (ofPerm_intertwine h)
    (keeps_ofPerm fun p => by
      change (π₂ p).1.adv.workspace ∈ A.counterInv ↔ p.1.adv.workspace ∈ A.counterInv
      rw [hk₂])
    (keeps_ofPerm fun p => by
      change (π₂ p).1.adv.workspace ∈ A.equalW ↔ p.1.adv.workspace ∈ A.equalW
      rw [hk₂])
    (keeps_ofPerm fun p => by
      change (π₁ p).1.adv.workspace ∈ A.aliveW ↔ p.1.adv.workspace ∈ A.aliveW
      rw [hk₁])

omit [Nonempty X] [AddGroup Y] [Nonempty Y] in
theorem liftQ_adv (a : QueryReg (A.toTPKindAlg.CW C) 1 X Y) :
    (liftQ (A.liftCW C) a).1.adv = A.liftD a.1.adv :=
  rfl

omit [Nonempty X] [AddGroup Y] [Nonempty Y] in
/-- The kind of the aborting form on a lifted workspace is the trace-preserving form's. -/
theorem kind_liftD (d : A.CReg) :
    A.abortAlg.toTPKindAlg.kind (A.liftD d).workspace = A.toTPKindAlg.kind d.workspace := by
  change ((A.kind d.workspace.1 || decide (d.workspace.2 = A.ended)) ||
    decide (d.workspace.2 = A.ended)) = (A.kind d.workspace.1 || decide (d.workspace.2 = A.ended))
  rw [Bool.or_assoc, Bool.or_self]

omit [Nonempty X] [AddGroup Y] [Nonempty Y] in
theorem ksim_measReq (j : Fin A.slots) :
    KSim (A.liftCW C) (A.toTPKindAlg.advIn C A.aliveW)
      (A.abortAlg.toTPKindAlg.advIn C A.counterInv) (A.abortAlg.toTPKindAlg.advIn C A.equalW)
      (A.toTPKindAlg.measReq C j) (A.abortAlg.toTPKindAlg.measReq C j) := by
  have h1 : ∀ m, (KrausMap.measureFn (A.abortAlg.toTPKindAlg.reqOutcome C)).op m *
      jmat (liftQ (A.liftCW C)) =
        jmat (liftQ (A.liftCW C)) * (KrausMap.measureFn (A.toTPKindAlg.reqOutcome C)).op m := by
    refine measureFn_intertwine fun a => ?_
    unfold KindAlg.reqOutcome
    rw [liftQ_adv, A.kind_liftD a.1.adv]
    rfl
  have h2 : ∀ r, (KrausMap.ofPerm (A.abortAlg.toTPKindAlg.copyReq C j)).op r *
      jmat (liftQ (A.liftCW C)) =
        jmat (liftQ (A.liftCW C)) * (KrausMap.ofPerm (A.toTPKindAlg.copyReq C j)).op r := by
    refine ofPerm_intertwine fun a => ?_
    refine (KindAlg.copyReq_apply (B := A.abortAlg.toTPKindAlg) C j _).trans ?_
    rw [KindAlg.copyReq_apply (B := A.toTPKindAlg) C j a]
    have hk2 : A.abortAlg.toTPKindAlg.kind (liftQ (A.liftCW C) a).1.adv.workspace =
        A.toTPKindAlg.kind a.1.adv.workspace := A.kind_liftD a.1.adv
    by_cases hk : A.toTPKindAlg.kind a.1.adv.workspace = true
    · rw [if_pos (hk2.trans hk), if_pos hk]
      rfl
    · rw [if_neg (by rwa [hk2]), if_neg hk]
  have h3 : ∀ r, (A.abortAlg.toTPKindAlg.measReq C j).op r * jmat (liftQ (A.liftCW C)) =
      jmat (liftQ (A.liftCW C)) * (A.toTPKindAlg.measReq C j).op r :=
    comp_intertwine h1 h2
  have k1 := KindAlg.keeps_measReq_advIn (B := A.abortAlg.toTPKindAlg) (S := A.counterInv) C j
  have k2 := KindAlg.keeps_measReq_advIn (B := A.abortAlg.toTPKindAlg) (S := A.equalW) C j
  have k3 := KindAlg.keeps_measReq_advIn (B := A.toTPKindAlg) (S := A.aliveW) C j
  exact KSim.of_intertwine h3 k1 k2 k3

omit [Nonempty X] [AddGroup Y] [Nonempty Y] in
theorem ksim_writeReply (j : Fin A.slots) :
    KSim (A.liftCW C) (A.toTPKindAlg.advIn C A.aliveW)
      (A.abortAlg.toTPKindAlg.advIn C A.counterInv) (A.abortAlg.toTPKindAlg.advIn C A.equalW)
      (KrausMap.ofPerm (A.toTPKindAlg.writeReply C j))
      (KrausMap.ofPerm (A.abortAlg.toTPKindAlg.writeReply C j)) := by
  refine A.ksim_ofPerm C (fun a => ?_) (fun p => ?_) (fun p => ?_)
  · change (if (a.1.chal.logs j).isSome = true then _ else liftQ (A.liftCW C) a) =
      liftQ (A.liftCW C) (if (a.1.chal.logs j).isSome = true then _ else a)
    split_ifs <;> rfl
  · change (if (p.1.chal.logs j).isSome = true then _ else p).1.adv.workspace = _
    split_ifs <;> rfl
  · change (if (p.1.chal.logs j).isSome = true then _ else p).1.adv.workspace = _
    split_ifs <;> rfl

omit [Nonempty X] [AddGroup Y] [Nonempty Y] in
theorem sim_advQueries {ass₁ : A.toTPKindAlg.CW C → List (Assignment X Y)}
    {ass₂ : A.abortAlg.toTPKindAlg.CW C → List (Assignment X Y)}
    (h : ∀ v, ass₂ (A.liftCW C v) = ass₁ v) :
    A.SimTP C (A.toTPKindAlg.advQueries C ass₁) (A.abortAlg.toTPKindAlg.advQueries C ass₂) :=
  Sim.concat (List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2
    (List.forall₂_same.2 fun _ _ =>
      ⟨A.ksim_ofPerm C (fun _ => rfl) (fun _ => rfl) (fun _ => rfl),
        h, A.ksim_ofPerm C (fun _ => rfl) (fun _ => rfl) (fun _ => rfl), trivial⟩)))

omit [Nonempty Y] in
theorem sim_chalQueries (j : Fin A.slots) :
    A.SimTP C (A.toTPKindAlg.chalQueries C j) (A.abortAlg.toTPKindAlg.chalQueries C j) :=
  Sim.concat (List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2
    (List.forall₂_same.2 fun _ _ =>
      ⟨A.ksim_ofPerm C (fun _ => rfl) (fun _ => rfl) (fun _ => rfl),
        fun _ => rfl, A.ksim_ofPerm C (fun _ => rfl) (fun _ => rfl) (fun _ => rfl), trivial⟩)))

/-- **The composition of the aborting completion's trace-preserving form simulates the
trace-preserving form's.** -/
theorem sim_fullCircBoth :
    A.SimTP C (A.toTPKindAlg.fullCircBoth C) (A.abortAlg.toTPKindAlg.fullCircBoth C) :=
  Sim.append (Sim.append
    (Sim.concat (List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2
      (List.forall₂_same.2 fun j _ =>
        ⟨A.ksim_advKraus C (slotStep j), A.ksim_measReq C j,
          (A.sim_chalQueries C j).append ⟨A.ksim_writeReply C j, A.sim_advQueries C fun _ => rfl⟩⟩))))
    (Sim.concat (List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2
      (List.forall₂_same.2 fun b _ =>
        ⟨A.ksim_advKraus C (postStep b), A.sim_advQueries C fun _ => rfl⟩)))))
    ⟨A.ksim_advKraus C lastStep, trivial⟩


/-- The initial state of the aborting completion's form on lifted registers. -/
theorem init_liftD (d d' : A.CReg) :
    A.abortAlg.toTPKindAlg.init.mat (A.liftD d) (A.liftD d') = A.toTPKindAlg.init.mat d d' := by
  have he : A.abortAlg.toTPKindAlg.init.mat (A.liftD d) (A.liftD d') =
      A.toKindAlg.init.mat d d' *
        Matrix.single (0 : Fin (A.budget + 2)) 0 (1 : ℂ) d.workspace.2 d'.workspace.2 :=
    rfl
  rw [he]
  by_cases h0 : d.workspace.2 = 0 ∧ d'.workspace.2 = 0
  · rw [h0.1, h0.2, Matrix.single_apply_same, mul_one]
  · rw [show A.toKindAlg.init.mat d d' = 0 from A.init_mat_eq_zero d d' (by tauto), zero_mul]

theorem initSys_liftQ (a b : QueryReg (A.toTPKindAlg.CW C) 1 X Y) :
    (A.abortAlg.toTPKindAlg.initSys C).mat (liftQ (A.liftCW C) a) (liftQ (A.liftCW C) b) =
      (A.toTPKindAlg.initSys C).mat a b := by
  simp only [KindAlg.initSys, MState.mix, MState.reindex, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.submatrix_apply, MState.tensorKet_mat, Matrix.kroneckerMap_apply]
  refine Finset.sum_congr rfl fun ω _ => ?_
  congr 2
  exact A.init_liftD a.1.adv b.1.adv

/-- The initial states agree along the lift on the registers that have not ended. -/
theorem cutTo_initSys_lift :
    cutTo (workIn (A.abortAlg.toTPKindAlg.advIn C A.equalW)) (A.abortAlg.toTPKindAlg.initSys C).mat =
      embed (liftQ (A.liftCW C))
        (cutTo (workIn (A.toTPKindAlg.advIn C A.aliveW)) (A.toTPKindAlg.initSys C).mat) := by
  classical
  rw [← cutTo_embed (A.liftCW_mem_equal C)]
  ext i j
  simp only [cutTo]
  split_ifs with h
  · obtain ⟨a, -, rfl⟩ := A.exists_liftQ C h.1
    obtain ⟨b, -, rfl⟩ := A.exists_liftQ C h.2
    rw [embed_apply_of_injective (liftQ_injective (A.liftCW_injective C)), initSys_liftQ]
  · rfl

/-- The real part of the trace of a placed matrix. -/
theorem _root_.GordieHowe.Quantum.re_trace_embed {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
    {e : κ → ι} (he : Function.Injective e) (σ : Matrix κ κ ℂ) :
    (embed e σ).trace.re = σ.trace.re := by
  have := embed_diag_of_injective he σ (fun _ => 1)
  simp only [one_mul] at this
  simpa [Matrix.trace, Complex.re_sum] using this

variable {A} in
/-- **Within the budget, the run of the aborting completion's form is the trace-preserving form's
run placed along the lift.** -/
theorem WithinBudget.run_abortAlg (hB : A.WithinBudget) (H : X → Y) :
    (A.abortAlg.toTPKindAlg.fullCircBoth C).run H (A.abortAlg.toTPKindAlg.initSys C).mat =
      embed (liftQ (A.liftCW C))
        ((A.toTPKindAlg.fullCircBoth C).run H (A.toTPKindAlg.initSys C).mat) := by
  obtain ⟨-, hT⟩ := (A.sim_fullCircBoth C).run H _ _ (A.invariant_counterInv.cutTo_initSys C)
    (A.cutTo_initSys_lift C)
  set run₁ := (A.toTPKindAlg.fullCircBoth C).run H (A.toTPKindAlg.initSys C).mat
  set run₂ := (A.abortAlg.toTPKindAlg.fullCircBoth C).run H (A.abortAlg.toTPKindAlg.initSys C).mat
  have htr₁ : run₁.trace = 1 := by
    rw [(A.stepsTP_toTPKindAlg.allTP_fullCircBoth C).trace_run H,
      (A.toTPKindAlg.initSys C).trace_eq_one]
  have htr₂ : run₂.trace = 1 := by
    rw [(A.abortAlg.stepsTP_toTPKindAlg.allTP_fullCircBoth C).trace_run H,
      (A.abortAlg.toTPKindAlg.initSys C).trace_eq_one]
  have hmodel : (A.toKindAlg.fullCircBoth C).run H (A.toKindAlg.initSys C).mat =
      cutTo (workIn (A.aliveC C)) run₁ := by
    rw [(A.intertwined_fullCircBoth C).run H, A.cutTo_initSys C]
    rfl
  have htrm : ((A.toKindAlg.fullCircBoth C).run H (A.toKindAlg.initSys C).mat).trace = 1 := by
    have h := congrArg Matrix.trace
      (hB.final_composeBothOut_eq C (fun v => A.toKindAlg.out v.adv.workspace) H)
    rw [KindAlg.final_composeBothOut, KindAlg.final_composeBothOut, KindAlg.trace_withAnc,
      KindAlg.trace_withAnc] at h
    rw [h]
    exact htr₁
  have h₁ : cutTo (workIn (A.aliveC C)) run₁ = run₁ :=
    cutTo_eq_self_of_trace (posSemidef_run H _ (A.toTPKindAlg.initSys C).posSemidef)
      (by rw [← hmodel, htrm, htr₁])
  have h₁' : cutTo (workIn (A.toTPKindAlg.advIn C A.aliveW)) run₁ = run₁ := h₁
  rw [h₁'] at hT
  have h₂ : cutTo (workIn (A.abortAlg.toTPKindAlg.advIn C A.equalW)) run₂ = run₂ :=
    cutTo_eq_self_of_trace (posSemidef_run H _ (A.abortAlg.toTPKindAlg.initSys C).posSemidef)
      (by rw [hT, re_trace_embed (liftQ_injective (A.liftCW_injective C)), htr₁, htr₂])
  rw [← h₂, hT]

variable {A} in
/-- **The aborting completion does not change an adversary within its budget: final state.** For
an adversary within its budget, the model's run of its aborting completion has the final state of
the model's run of the adversary, placed along the lift that sets the completion's counter to the
adversary's. -/
theorem WithinBudget.final_compose_abortAlg (hB : A.WithinBudget) (H : X → Y) :
    (A.abortAlg.compose C).final H = embed (liftR (A.liftCW C)) ((A.compose C).final H) := by
  have e₂ : (A.abortAlg.compose C).final H = withAnc KindAlg.x₀
      ((A.abortAlg.toTPKindAlg.fullCircBoth C).run H (A.abortAlg.toTPKindAlg.initSys C).mat) :=
    (A.withinBudget_abortAlg.final_compose_eq C H).trans
      (KindAlg.final_composeBothOut C _ (fun v => A.abortAlg.toTPKindAlg.out v.adv.workspace) H)
  have e₁ : (A.compose C).final H = withAnc KindAlg.x₀
      ((A.toTPKindAlg.fullCircBoth C).run H (A.toTPKindAlg.initSys C).mat) :=
    (hB.final_compose_eq C H).trans
      (KindAlg.final_composeBothOut C _ (fun v => A.toTPKindAlg.out v.adv.workspace) H)
  rw [e₂, e₁, hB.run_abortAlg C H, withAnc_embed (A.liftCW_injective C)]

variable {A} in
/-- **The aborting completion does not change an adversary within its budget: output law.** -/
theorem WithinBudget.outLaw_compose_abortAlg (hB : A.WithinBudget) (H : X → Y) :
    (A.abortAlg.compose C).outLaw H = (A.compose C).outLaw H := by
  classical
  have hf := hB.final_compose_abortAlg C H
  have hinj := liftR_injective (X := X) (Y := Y) (A.liftCW_injective C)
  ext o
  rcases o with _ | o
  · rw [Alg.outLaw_none, Alg.outLaw_none, hf, re_trace_embed hinj]
  · rw [Alg.outLaw, Alg.outLaw]
    refine (map_basisLaw_apply_some _ _ _ _ o).trans
      (Eq.trans ?_ (map_basisLaw_apply_some _ _ _ _ o).symm)
    have hite : ∀ (c : Prop) [Decidable c] (r : ℝ),
        (if c then ENNReal.ofReal r else 0) = ENNReal.ofReal ((if c then 1 else 0) * r) := by
      intro c _ r
      split_ifs <;> simp
    have hd : ∀ (B : Alg X Y O) (p : QueryReg B.V 1 X Y), 0 ≤ (B.final H p p).re := fun B p =>
      (Complex.nonneg_iff.1 ((B.posSemidef_stage H B.depth).diag_nonneg (i := p))).1
    have hsum : ∀ {ι : Type} [Fintype ι] (f : ι → ℝ), (∀ i, 0 ≤ f i) →
        ∑ i, ENNReal.ofReal (f i) = ENNReal.ofReal (∑ i, f i) :=
      fun f hf => (ENNReal.ofReal_sum_of_nonneg fun i _ => hf i).symm
    have hind : ∀ (c : Prop) [Decidable c], 0 ≤ (if c then (1 : ℝ) else 0) := fun c _ => by
      split_ifs <;> norm_num
    simp only [hite]
    refine (hsum _ fun p => mul_nonneg (hind _) (hd (A.abortAlg.compose C) p)).trans
      ((congrArg ENNReal.ofReal ?_).trans
        (hsum _ fun p => mul_nonneg (hind _) (hd (A.compose C) p)).symm)
    rw [hf]
    exact embed_diag_of_injective hinj _ _

end Simulation

end AdaptiveIAlg

end GordieHowe.Quantum
