-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Core.MixedAlg
public import GordieHowe.Model.Quantum.O2H.Basic

@[expose] public section

/-!
# Relabelled oracle algorithms and one-way to hiding for general algorithms

Tools for the dilation of `GordieHowe/Model/Quantum/Core/MixedAlg.lean`: relabelling the basis of an oracle
algorithm, and the ancilla of a dilation moved into the work register. The bridge from the model
(`GordieHowe/Model/Quantum/Pure/Bridge.lean`) and the general form of O2H use them.

- `O2HSetting.o2h_mixed`: AHU19 Theorem 3 for a general algorithm of query depth `d`, the form in
  which AHU19 state it ("not necessarily unitary"), derived from `O2HSetting.o2h` applied to the
  dilation.

It rests on relabelling the basis of the dilation, `(W × Q) × A ≃ (W × A) × Q`, so that the
ancilla joins the work register: `OracleAlg.relabel` and `OracleAlg.stage_relabel`.
-/

open Finset
open scoped BigOperators

namespace GordieHowe.Quantum

/-! ### Relabelled oracle algorithms -/

@[simp]
theorem relabel_symm_relabel {ι κ : Type*} [Fintype ι] [Fintype κ] (σ : ι ≃ κ) (v : QState ι) :
    relabel σ.symm (relabel σ v) = v := by
  ext i
  simp

namespace OracleAlg

variable {Z ι κ : Type*} [Fintype ι] [Fintype κ] {d : ℕ} (A : OracleAlg Z ι d) (σ : ι ≃ κ)

/-- `A` on a relabelled basis: the initial state and the unitaries are conjugated by
`relabel σ`, and the outcome `j` is accepted when `σ.symm j` is. -/
noncomputable def relabel : OracleAlg Z κ d where
  init z := Quantum.relabel σ (A.init z)
  norm_init z := by rw [LinearIsometryEquiv.norm_map, A.norm_init]
  step z k := ((Quantum.relabel σ).symm.trans (A.step z k)).trans (Quantum.relabel σ)
  accept z := σ.symm ⁻¹' A.accept z

/-- Two basis permutations intertwined by `σ` give unitaries intertwined by `relabel σ`. -/
theorem permOp_relabel {π : Equiv.Perm ι} {π' : Equiv.Perm κ} (h : ∀ i, π' (σ i) = σ (π i))
    (v : QState ι) : permOp π' (Quantum.relabel σ v) = Quantum.relabel σ (permOp π v) := by
  have hj : ∀ j, π'.symm j = σ (π.symm (σ.symm j)) := fun j => by
    rw [Equiv.symm_apply_eq, h, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  ext j
  simp only [permOp_apply, relabel_apply, hj, Equiv.symm_apply_apply]

/-- The run of the relabelled algorithm is the relabelled run, for oracles intertwined by `σ`. -/
theorem stage_relabel {π : Equiv.Perm ι} {π' : Equiv.Perm κ} (h : ∀ i, π' (σ i) = σ (π i))
    (z : Z) (k : ℕ) : (A.relabel σ).stage π' z k = Quantum.relabel σ (A.stage π z k) := by
  have hstep : ∀ n (v : QState ι), (A.relabel σ).stepAt z n (Quantum.relabel σ v) =
      Quantum.relabel σ (A.stepAt z n v) := fun n v => by
    by_cases hn : n < d + 1
    · simp [stepAt, hn, relabel, relabel_symm_relabel]
    · simp [stepAt, hn]
  induction k with
  | zero => exact hstep 0 _
  | succ k ih =>
    rw [stage, hybrid_succ, ← stage, ih, permOp_relabel σ h, hstep, stage, hybrid_succ, ← stage]

/-- The relabelled algorithm accepts with the same probability. -/
theorem acceptProb_relabel {π : Equiv.Perm ι} {π' : Equiv.Perm κ} (h : ∀ i, π' (σ i) = σ (π i))
    (z : Z) : (A.relabel σ).acceptProb π' z = A.acceptProb π z := by
  rw [acceptProb, final, A.stage_relabel σ h, prob_relabel]
  simp [relabel, acceptProb, final]

/-- The guessing probability of the relabelled algorithm for a set `B` is that of `A` for its
preimage. -/
theorem guessProb_relabel {π : Equiv.Perm ι} {π' : Equiv.Perm κ} (h : ∀ i, π' (σ i) = σ (π i))
    (B : Set κ) (z : Z) : (A.relabel σ).guessProb B π' z = A.guessProb (σ ⁻¹' B) π z := by
  refine Finset.expect_congr rfl fun i _ => ?_
  rw [pre, A.stage_relabel σ h, prob_relabel, pre]

end OracleAlg

/-! ### Moving the ancilla into the work register -/

/-- The relabelling `((w, q), a) ↦ ((w, a), q)` that moves an ancilla `A` into the work register
of a query basis. -/
def ancillaToWork (W A : Type*) (n : ℕ) (X Y : Type*) :
    QueryReg W n X Y × A ≃ QueryReg (W × A) n X Y where
  toFun p := ((p.1.1, p.2), p.1.2)
  invFun r := ((r.1.1, r.2), r.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The oracle on the system, lifted to the ancilla, is the oracle of the enlarged work register
for the function that ignores the ancilla. -/
theorem queryPermOf_ancillaToWork {W A X Y : Type*} {n : ℕ} [AddGroup Y] (f : W → X → Y)
    (p : QueryReg W n X Y × A) :
    queryPermOf (fun w : W × A => f w.1) (ancillaToWork W A n X Y p) =
      ancillaToWork W A n X Y (MixedAlg.liftPerm (queryPermOf f) p) :=
  rfl

/-! ### One-way to hiding for general algorithms -/

namespace O2HSetting

variable {Ω Z X Y W : Type*} [Fintype Ω] [Fintype W] [DecidableEq W] [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y] [AddGroup Y] {n d : ℕ} {R M : Type*} [Fintype R] [Fintype M]
  (s : O2HSetting Ω Z W X Y)

/-- The setting with the work register enlarged by an ancilla `A` that the oracles and the set
ignore. -/
def withAncilla (A : Type*) : O2HSetting Ω Z (W × A) X Y where
  μ := s.μ
  S ω w := s.S ω w.1
  G ω w := s.G ω w.1
  H ω w := s.H ω w.1
  z := s.z
  agree ω w := s.agree ω w.1

variable (G : MixedAlg Z (QueryReg W n X Y) d R M) (E : Z → Set M)

/-- `P_left = Pr[b = 1 : b ← A^H(z)]` for a general algorithm whose output bit is `1` on the
outcomes in `E z`. -/
noncomputable def pLeftMixed : ℝ :=
  ∑ ω, (s.μ ω).toReal * G.acceptProb (E (s.z ω)) (queryPermOf (s.H ω)) (s.z ω)

/-- `P_right = Pr[b = 1 : b ← A^G(z)]` for a general algorithm. -/
noncomputable def pRightMixed : ℝ :=
  ∑ ω, (s.μ ω).toReal * G.acceptProb (E (s.z ω)) (queryPermOf (s.G ω)) (s.z ω)

/-- `P_guess = Pr[S ∩ T ≠ ∅ : T ← B^F(z)]` for a general algorithm (`O2HSetting.pGuess`). -/
noncomputable def pGuessMixed (F : Ω → W → X → Y) : ℝ :=
  ∑ ω, (s.μ ω).toReal * G.guessProb (queriedOf (s.S ω)) (queryPermOf (F ω)) (s.z ω)

variable [Nonempty R] [Nonempty M]

/-- The dilation of `G` with the ancilla moved into the work register. -/
noncomputable def dilAlg : OracleAlg Z (QueryReg (W × MixedAlg.Anc (QueryReg W n X Y) d R M) n X Y) d :=
  (G.dilate E).relabel (ancillaToWork W _ n X Y)

theorem pLeft_dilAlg :
    (s.withAncilla (MixedAlg.Anc (QueryReg W n X Y) d R M)).pLeft (dilAlg G E) =
      s.pLeftMixed G E :=
  Finset.sum_congr rfl fun ω _ => congrArg _
    ((OracleAlg.acceptProb_relabel _ _ (queryPermOf_ancillaToWork (s.H ω)) _).trans
      (MixedAlg.acceptProb_dilate _ _ _ _))

theorem pRight_dilAlg :
    (s.withAncilla (MixedAlg.Anc (QueryReg W n X Y) d R M)).pRight (dilAlg G E) =
      s.pRightMixed G E :=
  Finset.sum_congr rfl fun ω _ => congrArg _
    ((OracleAlg.acceptProb_relabel _ _ (queryPermOf_ancillaToWork (s.G ω)) _).trans
      (MixedAlg.acceptProb_dilate _ _ _ _))

theorem pGuess_dilAlg (F : Ω → W → X → Y) :
    (s.withAncilla (MixedAlg.Anc (QueryReg W n X Y) d R M)).pGuess (dilAlg G E)
        (fun ω w => F ω w.1) = s.pGuessMixed G F := by
  refine Finset.sum_congr rfl fun ω _ => congrArg _ ?_
  rw [dilAlg, OracleAlg.guessProb_relabel _ _ (queryPermOf_ancillaToWork (F ω)),
    show ancillaToWork W (MixedAlg.Anc (QueryReg W n X Y) d R M) n X Y ⁻¹'
      queriedOf ((s.withAncilla _).S ω) = {p | p.1 ∈ queriedOf (s.S ω)} from rfl]
  exact MixedAlg.guessProb_dilate G E _ _ _

omit [Nonempty R] [Nonempty M] in
/-- A bound for the dilation gives the bound for `G`: the three probabilities of the dilation
are those of `G`. -/
theorem of_dilAlg {P : ℝ → ℝ → ℝ → Prop} (hP0 : P 0 0 0)
    (h : ∀ [Nonempty R] [Nonempty M],
      P ((s.withAncilla (MixedAlg.Anc (QueryReg W n X Y) d R M)).pLeft (dilAlg G E))
        ((s.withAncilla (MixedAlg.Anc (QueryReg W n X Y) d R M)).pRight (dilAlg G E))
        ((s.withAncilla (MixedAlg.Anc (QueryReg W n X Y) d R M)).pGuess (dilAlg G E)
          (s.withAncilla _).H)) :
    P (s.pLeftMixed G E) (s.pRightMixed G E) (s.pGuessMixed G s.H) := by
  by_cases hΩ : Nonempty Ω
  · obtain ⟨ω⟩ := hΩ
    have := (G.init (s.z ω)).nonempty
    have := (G.step (s.z ω) 0).nonempty
    have := (G.meas (s.z ω)).nonempty
    have := @h _ _
    rwa [pLeft_dilAlg, pRight_dilAlg, show (s.withAncilla _).H = fun ω w => s.H ω w.1 from rfl,
      pGuess_dilAlg] at this
  · rw [not_nonempty_iff] at hΩ
    simpa [pLeftMixed, pRightMixed, pGuessMixed] using hP0

omit [Nonempty R] [Nonempty M] in
/-- **AHU19 Theorem 3** (pp. 11–12) for general algorithms: "Let A be quantum oracle algorithm
with query depth d (not necessarily unitary). … Then |P_left − P_right| ≤ 2d √P_guess."
Derived from `o2h` applied to the unitary dilation of `G` (`MixedAlg.dilate`). -/
theorem o2h_mixed :
    GordieHowe.advantage (s.pLeftMixed G E) (s.pRightMixed G E) ≤ 2 * d * √(s.pGuessMixed G s.H) :=
  s.of_dilAlg G E (P := fun a b c => GordieHowe.advantage a b ≤ 2 * d * √c) (by simp)
    fun {_ _} => (s.withAncilla _).o2h _

omit [Nonempty R] [Nonempty M] in
/-- **AHU19 Theorem 3** (pp. 11–12), square-root form, for general algorithms:
"|√P_left − √P_right| ≤ 2d √P_guess". -/
theorem o2h_sqrt_mixed :
    |√(s.pLeftMixed G E) - √(s.pRightMixed G E)| ≤ 2 * d * √(s.pGuessMixed G s.H) :=
  s.of_dilAlg G E (P := fun a b c => |√a - √b| ≤ 2 * d * √c) (by simp)
    fun {_ _} => (s.withAncilla _).o2h_sqrt _

end O2HSetting

end GordieHowe.Quantum
