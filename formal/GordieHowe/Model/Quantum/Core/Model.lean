-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Core.Oracle
public import GordieHowe.Model.Quantum.Core.Channel
public import Mathlib.Probability.Distributions.Uniform

@[expose] public section

/-!
# The quantum model: mixed adversaries

The one model in which every security definition and headline of the QROM layer is stated.
The core is a mixed adversary in the sense of Heidler and Unruh,
"Formalizing the One-Way to Hiding Theorem" (CPP 2025; cited as HU25; Isabelle AFP
`Oneway2Hiding`, git b813b79fe3e1, `run_mixed_adv`), Definition 6.3 (p. 248), in finite
dimension. Everything else in this file is a construction on the core with a proved equivalence.

## The core: `Alg`

HU25 Definition 6.3 (p. 248), quoted against the Lean:

- "Let ρ_init be the initial (mixed) state and H the oracle with unitary U^H_query."
  `Alg.init : MState (QueryReg V 1 X Y)` (`GordieHowe/Model/Quantum/Core/Channel.lean`), a density matrix on the
  work register `V` and one pair of query registers `X`, `Y`. The query unitary is HU25's
  (p. 248) "U : |x, y⟩ ↦ |x, y + H(x)⟩ where + is a group operation (in typical settings: XOR on
  bitstrings)", the form of CMS19 (section 3.2, p. 14, "O_f … acts as |x, y⟩ ↦ |x, y ⊕ f(x)⟩")
  and AHU19 (p. 8); it is the basis permutation `queryPerm H` on `QueryReg V 1 X Y`
  (`GordieHowe/Model/Quantum/Core/Oracle.lean`). `Y` is an additive group; for bit strings `+` is XOR.

- "Let E^H_query be the oracle query applied as a Kraus map, i.e.
  E^H_query(ρ) = U^H_query · ρ · (U^H_query)*."
  For the basis permutation `π = queryPerm H`, `UρU*` is `ρ.submatrix π.symm π.symm`
  (`(UρU*) i j = ρ (π⁻¹ i) (π⁻¹ j)`).

- "The mixed adversary A of query depth d is given by d + 1 Kraus maps {E^A_i}_{i∈{0,…,d}} such
  that the adversary run can be represented by
  A(ρ_init) = (E^A_d ∘ E^H_query ∘ E^A_{d−1} ∘ ⋯ ∘ E^A_1 ∘ E^H_query ∘ E^A_0)(ρ_init)
  where "∘" is the functional composition of the Kraus maps."
  `Alg.depth` is `d` and `Alg.step i : KrausMap R …` is `E^A_i`; `Alg.final H` is `A(ρ_init)`.
  The Kraus maps are padded with zero operators to one finite index type `R`, which does not
  change them. A Kraus map satisfies HU25's normalization condition in the subprobability form
  (section 2.3, p. 245, "∑ E_i* E_i = I (or ≤ I if we allow subprobability distributions …)"):
  `∑ r, (op r)ᴴ * op r ≤ 1`, so an adversary may fail to terminate, and `A(ρ_init)` is a
  subdensity operator (trace at most `1`).

- The output. HU25 measure the final state ("the adversary always outputs a single bit in the
  end", section 6.3, p. 248). Here the output is read from the measurement of the work register
  in the computational basis, as in CMS19 (section 3.2, p. 14, "the outcome of measuring the
  register S of A^f in the computational basis"): an outcome `(v, q)` gives the output `out v`.
  A general measurement is a Kraus map before it, so it is part of `E^A_d`. The missing mass
  `1 - tr A(ρ_init)` is non-termination: `Alg.outLaw H : PMF (Option O)` gives it to `none`, so
  non-termination is never an output.

The model is finite-dimensional: the work register is a finite type, and so are the query
registers, as in AHU19 (pp. 8–9) and CMS19 (section 3.2, p. 14). This is the only departure from
HU25, whose registers may be infinite-dimensional. Nothing is claimed about infinite-dimensional
algorithms.

`Alg.realLaw e` is the joint law of the output and the random oracle in the quantum random-oracle
model: the oracle uniform on `X → Y` (CMS19 p. 14), returned read through `e : Y ≃ B`.

## Constructions on the core

- **Auxiliary input and query counts** belong to the adversary classes built on the core
  (`QueryBoundedAdversary`, `GordieHowe/Model/Quantum/Interactive/QueryBounded.lean`): auxiliary input drawn
  independently of the oracle (DFMS19, p. 4, footnote 8), quantum auxiliary input as part of
  `ρ_init`; oracle-dependent preprocessing is outside the model, as in CMS19 (p. 14).
- **Interactive adversaries** with a classical challenger are defined by translation into one
  core algorithm (`IAlg.compose`, `GordieHowe/Model/Quantum/Interactive/Basic.lean`), and the reprogrammed oracle is a
  sub-circuit with a clean ancilla (`reprogQuery_eq_controlled`, `GordieHowe/Model/Quantum/Core/Reprogram.lean`).

The equivalences with the literature's forms are proved in `GordieHowe/Model/Quantum/Core/Constructions.lean`
(parallel run, padding, folding finite auxiliary input into `ρ_init`) and
`GordieHowe/Model/Quantum/Interactive/PureGame.lean` (deferred measurement of the requests); every core algorithm
has a unitary query algorithm with the same output law (`Alg.outLaw_toQueryAlgCoh`,
`GordieHowe/Model/QROM/CoherentBridgeCore.lean`).
-/

open Finset Matrix
open scoped BigOperators ENNReal MatrixOrder Kronecker ComplexOrder

namespace GordieHowe.Quantum

/-! ### The core -/

/-- **A mixed adversary** (HU25 Definition 6.3, p. 248, in finite dimension): a finite work
register `V`, an initial mixed state `ρ_init` on `V` and one pair of query registers, `depth + 1`
Kraus maps `E^A_0, …, E^A_depth` applied alternately with `depth` queries, and an output read from
the computational-basis measurement of the work register. The Kraus maps are trace-non-increasing
(HU25 p. 245), so the adversary may fail to terminate. -/
structure Alg (X Y O : Type) [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] where
  /-- The work register. -/
  V : Type
  [instFintypeV : Fintype V]
  [instDecidableEqV : DecidableEq V]
  /-- The query depth `d`. -/
  depth : ℕ
  /-- The index type of the Kraus operators. -/
  R : Type
  [instFintypeR : Fintype R]
  /-- The initial state `ρ_init`. -/
  init : MState (QueryReg V 1 X Y)
  /-- The Kraus maps; `step i` is `E^A_i`, applied after the `i`-th query (`step 0` first). -/
  step : Fin (depth + 1) → KrausMap R (QueryReg V 1 X Y) (QueryReg V 1 X Y)
  /-- The output read from the computational-basis outcome of the work register. -/
  out : V → O

attribute [instance] Alg.instFintypeV Alg.instDecidableEqV Alg.instFintypeR

namespace Alg

variable {X Y O : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  (A : Alg X Y O)

variable [AddGroup Y]

/-- **The run of `A` with oracle `H`**: `stage H k` is the state after `E^A_k`,
`(E^A_k ∘ E^H_query ∘ ⋯ ∘ E^H_query ∘ E^A_0)(ρ_init)` (`KrausMap.run`). The query
`E^H_query(ρ) = UρU*` with `U = permOp (queryPerm H)` is `ρ.submatrix π.symm π.symm` for
`π = queryPerm H`. -/
def stage (H : X → Y) (k : ℕ) : Matrix (QueryReg A.V 1 X Y) (QueryReg A.V 1 X Y) ℂ :=
  KrausMap.run A.step (queryPerm H) A.init.mat k

theorem posSemidef_stage (H : X → Y) (k : ℕ) : (A.stage H k).PosSemidef :=
  KrausMap.posSemidef_run _ _ A.init.posSemidef k

theorem re_trace_stage_le_one (H : X → Y) (k : ℕ) : (A.stage H k).trace.re ≤ 1 := by
  refine (KrausMap.re_trace_run_le _ _ A.init.posSemidef k).trans ?_
  rw [A.init.trace_eq_one, Complex.one_re]

/-- **The final state `A(ρ_init)`** (HU25 Definition 6.3) with oracle `H`, a subdensity
operator. -/
def final (H : X → Y) : Matrix (QueryReg A.V 1 X Y) (QueryReg A.V 1 X Y) ℂ :=
  A.stage H A.depth

/-- **The output law of `A` with oracle `H`**: measure the final state in the computational basis
and read the output `out v` from an outcome `(v, q)`; `none` is non-termination, with the missing
mass `1 - re (tr A(ρ_init))` (`basisLaw`). -/
noncomputable def outLaw (H : X → Y) : PMF (Option O) :=
  (basisLaw (A.final H) (A.posSemidef_stage H _) (A.re_trace_stage_le_one H _)).map
    (Option.map fun i => A.out i.1)

/-- **The law of the output and the oracle in the quantum random-oracle model** (CMS19 p. 14,
"we study A^h for h ← U(m, n)"): `H` uniform on `X → Y`, the output of `A^H`, and `H` read
through `e`. -/
noncomputable def realLaw [Nonempty Y] {B : Type} (e : Y ≃ B) : PMF (Outcome (Option O) X B) :=
  (PMF.uniformOfFintype (X → Y)).bind fun H => (A.outLaw H).map fun o => ⟨o, e ∘ H⟩

/-- **The probability of an event of the output and the oracle** in the random-oracle model: the
average over the oracle of the diagonal mass of the final state on the outcomes whose output
satisfies the event. -/
theorem toOuterMeasure_realLaw_out [Nonempty Y] {B : Type} (e : Y ≃ B)
    (P : O → (X → B) → Prop) :
    (A.realLaw e).toOuterMeasure {p | ∃ v, p.out = some v ∧ P v p.oracle} =
      ∑' H, PMF.uniformOfFintype (X → Y) H *
        ∑ i, Set.indicator {i | P (A.out i.1) (e ∘ H)}
          (fun i => ENNReal.ofReal (A.final H i i).re) i := by
  rw [Alg.realLaw, PMF.toOuterMeasure_bind_apply]
  refine tsum_congr fun H => ?_
  congr 1
  rw [PMF.toOuterMeasure_map_apply, Alg.outLaw, PMF.toOuterMeasure_map_apply,
    PMF.toOuterMeasure_apply, tsum_fintype, Fintype.sum_option]
  simp only [Set.indicator, Set.mem_preimage, Set.mem_setOf_eq, Option.map_none, reduceCtorEq,
    false_and, exists_false, if_false, zero_add, Option.map_some, Option.some.injEq,
    exists_eq_left']
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hc hp hp
  · rfl
  · obtain ⟨v, hv, hpv⟩ := hc
    have hv' : A.out i.1 = v := Option.some_inj.1 hv
    exact absurd (show P (A.out i.1) (e ∘ H) by rw [hv']; exact hpv) hp
  · exact absurd ⟨_, rfl, hp⟩ hc
  · rfl

end Alg

end GordieHowe.Quantum
