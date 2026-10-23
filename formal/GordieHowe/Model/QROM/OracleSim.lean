-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.QROM.DensityRun

@[expose] public section

/-!
# Quantum oracle simulators

The interface `S` of an online extractor in the quantum random-oracle model (DFMS22 Definition
3.1, p. 10): a stateful quantum oracle. It holds a register of its own, prepared in a fixed state,
and answers each query of an adversary by an isometry on the query register and its own register;
the adversary's work register is not touched. The extractor reads the simulator's register after
the run.

- `OracleSim X Y`: the simulator register `Reg t` for runs of `t` queries, its initial state, and
  the kernel of the query isometry on `QueryReg Unit 1 X Y × Reg t`.
- `OracleSim.query`: the query on the registers of an adversary with work register `W`, the kernel
  tensored with the identity on `W`.
- `OracleSim.state`, `OracleSim.law`: the run of a `t`-query algorithm with its queries answered by
  the simulator, and the Born weights of its output and the simulator's register.
- `compressed e`: CMS19's compressed oracle (`simQuery`, section 3.6), whose run is `simState`
  (`state_compressed`) and whose law, read through `slotsDB`, is `simLaw` (`law_compressed`).
-/

open Finset

namespace GordieHowe.QROM

open GordieHowe.Quantum

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- **A quantum oracle simulator** (the interface `S` of an online extractor, DFMS22 Definition
3.1, p. 10): a register `Reg t` for runs of `t` queries, prepared in the unit vector `init t`, and
an isometry on the query register and the simulator's register, given by its kernel `kernel t`,
that answers each query. -/
structure OracleSim (X Y : Type) [Fintype X] [Fintype Y] where
  /-- The simulator's register for runs of `t` queries. -/
  Reg : ℕ → Type
  [instFintype : ∀ t, Fintype (Reg t)]
  [instDecidableEq : ∀ t, DecidableEq (Reg t)]
  /-- The initial state of the simulator's register. -/
  init : ∀ t, QState (Reg t)
  /-- The initial state is a unit vector. -/
  norm_init : ∀ t, ‖init t‖ = 1
  /-- The kernel of the query on the query register and the simulator's register. -/
  kernel : ∀ t, QueryReg Unit 1 X Y × Reg t → QueryReg Unit 1 X Y × Reg t → ℂ
  /-- The query is an isometry. -/
  norm_kernelOp : ∀ t v, ‖kernelOp (kernel t) v‖ = ‖v‖

attribute [instance] OracleSim.instFintype OracleSim.instDecidableEq

namespace OracleSim

variable (S : OracleSim X Y)

/-- **The registers of an adversary with work register `W` and the simulator's**, with the work
register split off. -/
def split (W : Type) (t : ℕ) : QueryReg W 1 X Y × S.Reg t ≃ (QueryReg Unit 1 X Y × S.Reg t) × W :=
  ctrlSplit (QueryAlg.queryAncSplit (Equiv.punitProd W).symm)

/-- **The simulated query on the registers of an adversary with work register `W`**: the
simulator's query on the query register and its own register, the identity on `W`. -/
noncomputable def query (W : Type) [Fintype W] [DecidableEq W] (t : ℕ)
    (v : QState (QueryReg W 1 X Y × S.Reg t)) : QState (QueryReg W 1 X Y × S.Reg t) :=
  relabel (S.split W t).symm (kernelOp (liftKernel (S.kernel t)) (relabel (S.split W t) v))

variable {O : Type} {t : ℕ} (𝒜 : QueryAlg X Y t O)

/-- The adversary's initial state and the simulator's. -/
noncomputable def initState : QState (QueryReg 𝒜.W 1 X Y × S.Reg t) :=
  WithLp.toLp 2 fun b => 𝒜.init b.1 * S.init t b.2

/-- The adversary's unitary `step k`, the identity on the simulator's register. -/
noncomputable def stepOp (k : ℕ) :
    QState (QueryReg 𝒜.W 1 X Y × S.Reg t) ≃ₗᵢ[ℂ] QState (QueryReg 𝒜.W 1 X Y × S.Reg t) :=
  controlled fun _ => (𝒜.toOracleAlg ∅).stepAt () k

/-- The state after the adversary's `step k`, before its next query. -/
noncomputable def stage (k : ℕ) : QState (QueryReg 𝒜.W 1 X Y × S.Reg t) :=
  Nat.rec (S.stepOp 𝒜 0 (S.initState 𝒜)) (fun k v => S.stepOp 𝒜 (k + 1) (S.query 𝒜.W t v)) k

/-- **The run of `𝒜` with its queries answered by the simulator**: `A_t S ⋯ A_1 S A_0` on the
initial states. -/
noncomputable def state : QState (QueryReg 𝒜.W 1 X Y × S.Reg t) :=
  S.stage 𝒜 t

/-- **The outcome of the simulated run**: the Born weights of measuring the output register and the
simulator's register in the computational basis, as the output and the register's value. -/
noncomputable def law : MeasureTheory.OuterMeasure (O × S.Reg t) :=
  MeasureTheory.OuterMeasure.map (fun b => (𝒜.out b.1.1, b.2)) (bornWeight (S.state 𝒜))

end OracleSim

/-! ### The compressed oracle -/

section Compressed

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] {m : ℕ} {B : Type}
  (e : BitStr I J ≃ B)

/-- **CMS19's compressed oracle as an oracle simulator** (section 3.6, p. 17): the register of `t`
database slots, prepared in the empty database `|∅_t⟩`, and the simulated query `simQuery`. -/
noncomputable def compressed : OracleSim (Bits m) (BitStr I J) where
  Reg t := Slots I J m t
  init t := ket (dbSlots e t (∅ : DB (Bits m) B))
  norm_init t := by simp
  kernel t := simQueryKernel e Unit t
  norm_kernelOp t v := by
    rw [← simQuery_eq_kernelOp]
    exact norm_simQuery e v

variable {W : Type} [Fintype W] [DecidableEq W] {t : ℕ}

/-- **The compressed oracle's query is `simQuery`** on the registers of every adversary
(`relabel_simQuery`). -/
theorem query_compressed (v : QState (SimRegister W I J m t)) :
    (compressed (m := m) e).query W t v = simQuery e W t v := by
  have h := relabel_simQuery e (Equiv.punitProd W).symm v
  unfold OracleSim.query
  change relabel (simAncSplit (Equiv.punitProd W).symm).symm
    (kernelOp (liftKernel (simQueryKernel e Unit t))
      (relabel (simAncSplit (Equiv.punitProd W).symm) v)) = _
  rw [← h]
  ext p
  simp

variable {O : Type} (A : QueryAlg (Bits m) (BitStr I J) t O)

/-- **The run with the compressed oracle is `Sim*(A)`** (`simState`). -/
theorem state_compressed : (compressed (m := m) e).state A = simState e A := by
  have hinit : (compressed (m := m) e).initState A = simInit e A := by
    ext b
    simp [OracleSim.initState, simInit, compressed, EuclideanSpace.single_apply, eq_comm]
  have hstage : ∀ k, (compressed (m := m) e).stage A k = simStage e A k := by
    intro k
    induction k with
    | zero =>
      change (compressed e).stepOp A 0 ((compressed e).initState A) = simStep A 0 (simInit e A)
      rw [hinit]
      rfl
    | succ k ih =>
      change (compressed e).stepOp A (k + 1) ((compressed e).query A.W t
        ((compressed e).stage A k)) = simStep A (k + 1) (simQuery e A.W t (simStage e A k))
      rw [ih, query_compressed]
      rfl
  exact hstage t

/-- **The law of the compressed oracle's run, its slots read as a database, is `simLaw`.** -/
theorem law_compressed :
    MeasureTheory.OuterMeasure.map (fun p => (p.1, slotsDB e p.2)) ((compressed (m := m) e).law A) =
      simLaw e A := by
  rw [OracleSim.law, MeasureTheory.OuterMeasure.map_map, state_compressed]
  rfl

end Compressed

end GordieHowe.QROM
