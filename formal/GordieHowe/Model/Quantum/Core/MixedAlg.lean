-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Core.Dilation
public import GordieHowe.Model.Quantum.Pure.Algorithm

@[expose] public section

/-!
# General quantum oracle algorithms and their unitary dilation

A general quantum oracle algorithm may prepare a mixed initial state (classical randomness),
apply arbitrary quantum operations between its queries (channels, measurements whose outcomes it
keeps and consults later, discarding of registers), and end with a general measurement. This file
defines such algorithms (`MixedAlg`) and proves that each one has the same output law as a
unitary oracle algorithm in the model of `GordieHowe/Model/Quantum/Pure/Algorithm.lean` (`MixedAlg.dilate`), with
the same query depth and the same oracle steps. This is the fact AHU19 (pp. 8–9) cite as
"well-known": "any quantum oracle algorithm A^O(z) can be transformed into a unitary quantum
oracle algorithm with constant factor computational overhead and the same query number and query
depth" (the overhead is not modelled).

## The model

Heidler and Unruh, "Formalizing the One-Way to Hiding Theorem" (CPP 2025; cited as HU25),
Definition 6.3 (p. 248), quoted against the Lean:

- "Let ρ_init be the initial (mixed) state and H the oracle with unitary U^H_query. Let
  E^H_query be the oracle query applied as a Kraus map, i.e. E^H_query(ρ) =
  U^H_query · ρ · (U^H_query)*."
  `MixedAlg.init z : MState ι` (`GordieHowe/Model/Quantum/Core/Channel.lean`); the oracle is a basis permutation
  `π` of `ι` as in `OracleAlg`, applied as `MState.permute π`, which is `ρ ↦ UρU*` for
  `U = permOp π`. With `π = queryPerm f` or `queryPermOf f` (`GordieHowe/Model/Quantum/Core/Oracle.lean`) these are
  AHU19's parallel queries.

- "The mixed adversary A of query depth d is given by d + 1 Kraus maps {E^A_i}_{i ∈ {0,…,d}}
  such that the adversary run can be represented by
  A(ρ_init) = (E^A_d ∘ E^H_query ∘ E^A_{d−1} ∘ ⋯ ∘ E^A_1 ∘ E^H_query ∘ E^A_0)(ρ_init)."
  `MixedAlg.step z k : KrausChannel R ι ι`, `k = 0, …, d`; `MixedAlg.final π z` is the run on input `z`.
  The Kraus maps are padded with zero operators to a common finite index type `R`, which does not
  change them. As in `OracleAlg`, the maps may depend on the input `z`.

- HU25 (p. 248, section 6.3): "In the statement of the O2H, the adversary always outputs a single
  bit in the end", obtained by measuring the final state. Here the output is the outcome of a
  general measurement `MixedAlg.meas z : KrausChannel M ι ι` with outcomes in a finite type `M`
  (`MixedAlg.outLaw`); a projective measurement and a POVM are special cases
  (`GordieHowe/Model/Quantum/Core/Channel.lean`).

An intermediate measurement whose outcome the algorithm keeps is a Kraus map that writes the
outcome into a register of `ι`, so it is one of the `step`s. Classical randomness is a mixed
initial state or a Kraus map. The computational basis `ι` is arbitrary.

## The dilation

`MixedAlg.dilate` is an `OracleAlg` on the basis `ι × Anc ι d R M`: the ancilla holds a
purifying copy of `ι`, one fresh register `R` for each step and a fresh register `M` for the
measurement outcome. Its initial state purifies `init z` (`purify`), its step `k` is the
Stinespring unitary of `step z k` on the `k`-th register (`stinespring`), and its last step is
followed by the Stinespring unitary of the measurement on the register `M`. Its oracle is
`π × id`, the oracle of the general algorithm acting on the system. By induction the state of
the dilation just before each oracle step purifies the state of the general algorithm there
(`reduce_pre_dilate`), and the outcome register at the end carries the outcome law of the
measurement (`born_final_dilate`).
-/

open Finset
open scoped BigOperators

namespace GordieHowe.Quantum

/-- **A general quantum oracle algorithm of query depth `d`** (HU25 Definition 6.3, p. 248, with
a final measurement) with inputs in `Z` and computational basis `ι`: for each input, an initial
density matrix, `d + 1` Kraus maps applied alternately with `d` oracle steps, and a general
measurement with outcomes in `M`. -/
structure MixedAlg (Z ι : Type*) [Fintype ι] [DecidableEq ι] (d : ℕ) (R M : Type*) [Fintype R]
    [Fintype M] where
  /-- The initial state on input `z`. -/
  init : Z → MState ι
  /-- The Kraus maps on input `z`; `step z k` is applied after the `k`-th oracle step
  (`step z 0` first). -/
  step : Z → Fin (d + 1) → KrausChannel R ι ι
  /-- The final measurement on input `z`. -/
  meas : Z → KrausChannel M ι ι

namespace MixedAlg

variable {Z ι R M : Type*} [Fintype ι] [DecidableEq ι] [Fintype R] [Fintype M] {d : ℕ}
  (G : MixedAlg Z ι d R M)

/-- The Kraus map on input `z` indexed by `ℕ`, applied to a density matrix; the identity after
`step z d`. -/
def applyAt (z : Z) (k : ℕ) (ρ : MState ι) : MState ι :=
  if h : k < d + 1 then (G.step z ⟨k, h⟩).applyMState ρ else ρ

/-- The run of `G` on input `z` with oracle `π`: `stage π z k` is the state after `step z k`,
just before the `k`-th oracle step (counting from `0`). -/
def stage (π : Equiv.Perm ι) (z : Z) : ℕ → MState ι
  | 0 => G.applyAt z 0 (G.init z)
  | k + 1 => G.applyAt z (k + 1) ((stage π z k).permute π)

/-- The state just before oracle step `i`. -/
def pre (π : Equiv.Perm ι) (z : Z) (i : Fin d) : MState ι :=
  G.stage π z i

/-- The final state, after `step z d`. -/
def final (π : Equiv.Perm ι) (z : Z) : MState ι :=
  G.stage π z d

/-- **The output law of `G` on input `z` with oracle `π`**: the outcome law of the final
measurement on the final state. -/
def outLaw (π : Equiv.Perm ι) (z : Z) : PMF M :=
  (G.meas z).outcomeLaw (G.final π z)

/-- The probability that the output of `G` on input `z` with oracle `π` lies in `E`. -/
noncomputable def acceptProb (E : Set M) (π : Equiv.Perm ι) (z : Z) : ℝ :=
  ∑ m, E.indicator ((G.meas z).outcomeProb (G.final π z)) m

/-- The probability that the following algorithm gives an outcome in `B`: pick `i` uniformly
among the `d` oracle steps, run `G` on input `z` with oracle `π` until just before step `i`, and
measure in the computational basis. The mixed-state form of `OracleAlg.guessProb`. -/
noncomputable def guessProb (B : Set ι) (π : Equiv.Perm ι) (z : Z) : ℝ :=
  𝔼 i, (G.pre π z i).probIn B

/-! ### The dilation -/

/-- The ancilla of the dilation: a purifying copy of `ι`, a register `R` for each of the `d + 1`
steps, and a register `M` for the measurement outcome. -/
abbrev Anc (ι : Type*) (d : ℕ) (R M : Type*) := ι × ((Fin (d + 1) → R) × M)

omit [Fintype ι] [DecidableEq ι] [Fintype R] [Fintype M] in
/-- The ancilla split into the register of step `k` and the rest. -/
def stepSplit (k : Fin (d + 1)) :
    Anc ι d R M ≃ R × (ι × (({ j // j ≠ k } → R) × M)) :=
  (Equiv.prodCongr (Equiv.refl ι) ((Equiv.funSplitAt k R).prodCongr (Equiv.refl M))).trans
    { toFun := fun x => (x.2.1.1, (x.1, (x.2.1.2, x.2.2)))
      invFun := fun y => (y.2.1, ((y.1, y.2.2.1), y.2.2.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

omit [Fintype ι] [DecidableEq ι] [Fintype R] [Fintype M] in
@[simp]
theorem stepSplit_apply_fst (k : Fin (d + 1)) (a : Anc ι d R M) : (stepSplit k a).1 = a.2.1 k :=
  rfl

omit [Fintype ι] [DecidableEq ι] [Fintype R] [Fintype M] in
/-- Resetting the register of step `k` to `r`. -/
theorem stepSplit_symm_reset (k : Fin (d + 1)) (r : R) (a : Anc ι d R M) :
    (stepSplit k).symm (r, (stepSplit k a).2) = (a.1, (Function.update a.2.1 k r, a.2.2)) := by
  obtain ⟨p, g, m⟩ := a
  simp only [stepSplit, Equiv.symm_trans_apply, Equiv.coe_fn_symm_mk, Equiv.prodCongr_symm,
    Equiv.prodCongr_apply, Equiv.refl_symm, Equiv.coe_refl, Prod.map, id, Equiv.trans_apply,
    Equiv.coe_fn_mk, Prod.mk.injEq, true_and, and_true]
  funext j
  by_cases h : j = k
  · subst h
    simp [Equiv.funSplitAt, Equiv.piSplitAt]
  · simp [Equiv.funSplitAt, Equiv.piSplitAt, h]

omit [Fintype ι] [DecidableEq ι] [Fintype R] [Fintype M] in
/-- The ancilla split into the measurement register and the rest. -/
def measSplit : Anc ι d R M ≃ M × (ι × (Fin (d + 1) → R)) where
  toFun a := (a.2.2, (a.1, a.2.1))
  invFun x := (x.2.1, (x.2.2, x.1))
  left_inv _ := rfl
  right_inv _ := rfl

omit [Fintype ι] [DecidableEq ι] [Fintype R] [Fintype M] in
@[simp]
theorem measSplit_apply_fst (a : Anc ι d R M) : (measSplit a).1 = a.2.2 :=
  rfl

/-- The oracle of the dilation: `π` on the system, the identity on the ancilla. -/
def liftPerm {A : Type*} (π : Equiv.Perm ι) : Equiv.Perm (ι × A) :=
  π.prodCongr (Equiv.refl A)

variable [Nonempty R] [Nonempty M]

/-- The ancilla basis states whose step registers from `n` on and whose measurement register are
in their initial basis states (`Classical.arbitrary`). -/
def Clean (n : ℕ) (a : Anc ι d R M) : Prop :=
  (∀ j : Fin (d + 1), n ≤ j → a.2.1 j = Classical.arbitrary R) ∧
    a.2.2 = Classical.arbitrary M

omit [Fintype ι] [DecidableEq ι] [Fintype R] [Fintype M] in
theorem Clean.mono {n : ℕ} {a : Anc ι d R M} (h : Clean n a) : Clean (n + 1) a :=
  ⟨fun j hj => h.1 j (Nat.le_of_succ_le hj), h.2⟩

/-- A vector on `ι × Anc ι d R M` that vanishes outside the clean ancilla states. -/
def CleanVec (n : ℕ) (ψ : QState (ι × Anc ι d R M)) : Prop :=
  ∀ i a, ¬ Clean n a → ψ (i, a) = 0

omit [DecidableEq ι] in
theorem CleanVec.mono {n : ℕ} {ψ : QState (ι × Anc ι d R M)} (h : CleanVec n ψ) :
    CleanVec (n + 1) ψ :=
  fun i a ha => h i a fun hc => ha hc.mono

omit [DecidableEq ι] in
/-- The oracle of the dilation keeps the vector clean. -/
theorem CleanVec.permOp {n : ℕ} {ψ : QState (ι × Anc ι d R M)} (h : CleanVec n ψ)
    (π : Equiv.Perm ι) : CleanVec n (Quantum.permOp (liftPerm π) ψ) :=
  fun i a ha => by simpa [liftPerm, Equiv.prodCongr_symm] using h (π.symm i) a ha

omit [DecidableEq ι] in
/-- A clean vector is fresh in the register of step `k ≥ n`. -/
theorem CleanVec.fresh {n : ℕ} {ψ : QState (ι × Anc ι d R M)} (h : CleanVec n ψ)
    {k : Fin (d + 1)} (hk : n ≤ k) : Fresh (stepSplit k) (Classical.arbitrary R) ψ :=
  fun i a ha => h i a fun hc => ha (by simpa using hc.1 k hk)

omit [DecidableEq ι] in
/-- A vector clean from `n` on is fresh in the measurement register. -/
theorem CleanVec.freshMeas {n : ℕ} {ψ : QState (ι × Anc ι d R M)} (h : CleanVec n ψ) :
    Fresh measSplit (Classical.arbitrary M) ψ :=
  fun i a ha => h i a fun hc => ha (by simpa using hc.2)

/-- The unitary of step `k` of the dilation on input `z`, indexed by `ℕ`: the Stinespring
unitary of `step z k` on the register of step `k`; the identity after step `d`. -/
noncomputable def dilStep (z : Z) (k : ℕ) :
    QState (ι × Anc ι d R M) ≃ₗᵢ[ℂ] QState (ι × Anc ι d R M) :=
  if h : k < d + 1 then stinespring (stepSplit ⟨k, h⟩) (Classical.arbitrary R) (G.step z ⟨k, h⟩)
  else LinearIsometryEquiv.refl ℂ _

/-- The Stinespring unitary of the final measurement on the measurement register. -/
noncomputable def dilMeas (z : Z) : QState (ι × Anc ι d R M) ≃ₗᵢ[ℂ] QState (ι × Anc ι d R M) :=
  stinespring measSplit (Classical.arbitrary M) (G.meas z)

open Classical in
/-- The initial state of the dilation: a purification of `init z` with all registers of the
ancilla in their initial basis states. -/
noncomputable def dilInit (z : Z) : QState (ι × Anc ι d R M) :=
  appendKet (purify (G.init z)) ((fun _ => Classical.arbitrary R), Classical.arbitrary M)

open Classical in
theorem cleanVec_dilInit (z : Z) : CleanVec 0 (G.dilInit z) := by
  intro i a ha
  have hne : a.2 ≠ ((fun _ => Classical.arbitrary R), Classical.arbitrary M) := fun h =>
    ha ⟨fun j _ => by rw [h], by rw [h]⟩
  simp [dilInit, hne]

open Classical in
theorem reduce_dilInit (z : Z) : reduce (G.dilInit z) = (G.init z).mat := by
  rw [dilInit, reduce_appendKet, reduce_purify]

open Classical in
theorem norm_dilInit (z : Z) : ‖G.dilInit z‖ = 1 := by
  rw [dilInit, norm_appendKet, norm_purify]

/-- **One step of the dilation**: on a vector that is clean from `n` on and purifies `ρ`, the
unitary of step `n` gives a vector clean from `n + 1` on that purifies `applyAt z n ρ`. -/
theorem dilStep_spec (z : Z) {n : ℕ} {ψ : QState (ι × Anc ι d R M)} (hψ : CleanVec n ψ) :
    CleanVec (n + 1) (G.dilStep z n ψ) ∧
      ∀ ρ : MState ι, reduce ψ = ρ.mat → reduce (G.dilStep z n ψ) = (G.applyAt z n ρ).mat := by
  by_cases h : n < d + 1
  · have hf := hψ.fresh (k := ⟨n, h⟩) le_rfl
    simp only [dilStep, applyAt, h, dite_true, stinespring_apply_of_fresh _ hf]
    refine ⟨fun i a ha => krausAct_eq_zero_of _ (P := fun a => ¬ Clean (n + 1) a)
      (fun i a ha => hψ i a fun hc => ha hc.mono) (fun a ha hc => ha ?_) i ha, fun ρ hρ => ?_⟩
    · rw [stepSplit_symm_reset] at hc
      refine ⟨fun j hj => ?_, hc.2⟩
      have hne : j ≠ ⟨n, h⟩ := fun hjk => by
        rw [hjk] at hj
        exact Nat.not_succ_le_self n hj
      have := hc.1 j hj
      simp only at this
      rwa [Function.update_of_ne hne] at this
    · rw [KrausChannel.applyMState_mat, reduce_krausAct _ hf, hρ]
  · simp only [dilStep, applyAt, h, dite_false, LinearIsometryEquiv.coe_refl, id]
    exact ⟨hψ.mono, fun ρ hρ => hρ⟩

/-- The run of the dilation before the final measurement, with oracle `π × id`. -/
noncomputable def dilRun (π : Equiv.Perm ι) (z : Z) : ℕ → QState (ι × Anc ι d R M) :=
  hybrid (G.dilStep z) (fun _ => permOp (liftPerm π)) (G.dilInit z)

/-- **The run of the dilation purifies the run of `G`**: after step `k` the state of the dilation
is clean from `k + 1` on and its reduced density matrix is the state of `G`. -/
theorem dilRun_spec (π : Equiv.Perm ι) (z : Z) (k : ℕ) :
    CleanVec (k + 1) (G.dilRun π z k) ∧ reduce (G.dilRun π z k) = (G.stage π z k).mat := by
  induction k with
  | zero =>
    obtain ⟨h1, h2⟩ := G.dilStep_spec z (G.cleanVec_dilInit z)
    exact ⟨h1, h2 _ (G.reduce_dilInit z)⟩
  | succ k ih =>
    obtain ⟨h1, h2⟩ := G.dilStep_spec z (ih.1.permOp π)
    refine ⟨h1, ?_⟩
    rw [dilRun, hybrid_succ, ← dilRun]
    refine h2 _ ?_
    rw [liftPerm, reduce_permOp_prodCongr, ih.2]
    rfl

theorem norm_dilRun (π : Equiv.Perm ι) (z : Z) (k : ℕ) : ‖G.dilRun π z k‖ = 1 := by
  rw [dilRun, norm_hybrid, G.norm_dilInit]

/-- **The dilation of `G`**, a unitary oracle algorithm with the same input type and query depth
on the basis `ι × Anc ι d R M`, whose output bit is `1` when the measurement register holds an
outcome in `E z`. Its oracle is `liftPerm π` when `G`'s is `π`. -/
noncomputable def dilate (E : Z → Set M) : OracleAlg Z (ι × Anc ι d R M) d where
  init := G.dilInit
  norm_init := G.norm_dilInit
  step z k := if (k : ℕ) = d then (G.dilStep z k).trans (G.dilMeas z) else G.dilStep z k
  accept z := {p | p.2.2.2 ∈ E z}

/-- The dilation agrees with the run before the final measurement up to step `d - 1`. -/
theorem stage_dilate_of_lt (E : Z → Set M) (π : Equiv.Perm ι) (z : Z) {k : ℕ} (hk : k < d) :
    (G.dilate E).stage (liftPerm π) z k = G.dilRun π z k := by
  refine hybrid_congr_le _ _ k fun i hi => ?_
  rw [OracleAlg.stepAt_of_lt _ (by omega)]
  simp [dilate, show i ≠ d by omega]

/-- The final state of the dilation is the run before the final measurement, followed by the
Stinespring unitary of the measurement. -/
theorem final_dilate (E : Z → Set M) (π : Equiv.Perm ι) (z : Z) :
    (G.dilate E).final (liftPerm π) z = G.dilMeas z (G.dilRun π z d) := by
  have hstep : (G.dilate E).stepAt z d = (G.dilStep z d).trans (G.dilMeas z) := by
    rw [OracleAlg.stepAt_of_lt _ (Nat.lt_succ_self d)]
    simp [dilate]
  cases d with
  | zero =>
    simp only [OracleAlg.final, OracleAlg.stage, hybrid_zero, dilRun]
    rw [hstep]
    rfl
  | succ k =>
    simp only [OracleAlg.final, OracleAlg.stage, hybrid_succ]
    rw [← OracleAlg.stage, G.stage_dilate_of_lt E π z (Nat.lt_succ_self k), hstep, dilRun,
      hybrid_succ, ← dilRun]
    rfl

/-- **The states of the dilation before the oracle steps purify those of `G`.** -/
theorem reduce_pre_dilate (E : Z → Set M) (π : Equiv.Perm ι) (z : Z) (i : Fin d) :
    reduce ((G.dilate E).pre (liftPerm π) z i) = (G.pre π z i).mat := by
  rw [OracleAlg.pre, G.stage_dilate_of_lt E π z i.2]
  exact (G.dilRun_spec π z i).2

/-- **The measurement register of the dilation carries the output law of `G`**: measuring the
final state of the dilation and reading the measurement register gives `G.outLaw π z`. -/
theorem born_final_dilate (E : Z → Set M) (π : Equiv.Perm ι) (z : Z) :
    (born ((G.dilate E).final (liftPerm π) z) ((G.dilate E).norm_final _ z)).map
      (fun p => p.2.2.2) = G.outLaw π z := by
  have hf := (G.dilRun_spec π z d).1.freshMeas
  ext m
  rw [born_map_apply, outLaw, KrausChannel.outcomeLaw_apply, KrausChannel.outcomeProb, final_dilate, dilMeas,
    stinespring_apply_of_fresh _ hf]
  congr 1
  rw [MixedAlg.final, ← (G.dilRun_spec π z d).2, ← prob_krausAct_fiber _ hf m]
  rfl

/-- **The acceptance probability of the dilation is that of `G`.** -/
theorem acceptProb_dilate (E : Z → Set M) (π : Equiv.Perm ι) (z : Z) :
    (G.dilate E).acceptProb (liftPerm π) z = G.acceptProb (E z) π z := by
  classical
  have hf := (G.dilRun_spec π z d).1.freshMeas
  have hpre : (G.dilate E).accept z =
      (fun p : ι × Anc ι d R M => (measSplit (ι := ι) (d := d) (R := R) (M := M) p.2).1) ⁻¹' E z :=
    rfl
  rw [OracleAlg.acceptProb, hpre, prob_preimage, acceptProb]
  simp only [Set.indicator_apply]
  rw [← Finset.sum_filter]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [final_dilate, dilMeas, stinespring_apply_of_fresh _ hf, prob_krausAct_fiber _ hf,
    (G.dilRun_spec π z d).2]
  rfl

/-- **The guessing probability of the dilation is that of `G`**, for a set of basis states of the
system. -/
theorem guessProb_dilate (E : Z → Set M) (B : Set ι) (π : Equiv.Perm ι) (z : Z) :
    (G.dilate E).guessProb {p | p.1 ∈ B} (liftPerm π) z = G.guessProb B π z := by
  refine Finset.expect_congr rfl fun i _ => ?_
  have hn := (G.dilate E).norm_pre (liftPerm π) z i
  rw [← probIn_reduceMState _ hn]
  congr 1
  exact MState.ext (G.reduce_pre_dilate E π z i)

end MixedAlg

end GordieHowe.Quantum
