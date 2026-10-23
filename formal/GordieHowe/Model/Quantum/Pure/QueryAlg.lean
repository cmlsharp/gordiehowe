-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Pure.Algorithm
public import GordieHowe.Model.Quantum.Core.Born

@[expose] public section

/-!
# Query algorithms with a classical output

A `t`-query quantum oracle algorithm with a classical output (`QueryAlg`), in the model of
`GordieHowe/Model/Quantum/Pure/Algorithm.lean` (AHU19, pp. 8–9) with one query register: an initial unit vector,
`t + 1` unitaries alternating with `t` oracle steps `U_f`, and a final measurement of the work
register in the computational basis, read through an output map. This is the adversary of the
soundness layer (`GordieHowe/Model/QROM/Lifting.lean`).

CMS19 (Chiesa–Manohar–Spooner, "Succinct Arguments in the Quantum Random Oracle Model", ePrint
2019/834, version of January 14, 2020), section 3.2, p. 14, quoted against the Lean:

- "Let f : {0,1}^m → {0,1}^n be a function. The standard way to model oracle access to f in
  the quantum setting is via a unitary operator O_f that acts as |x, y⟩ ↦ |x, y ⊕ f(x)⟩ for all
  x ∈ {0,1}^m and y ∈ {0,1}^n. We label the input and output registers X and Y, respectively."
  `O_f` is `permOp (queryPerm f)` on `QueryReg W 1 X Y` (`GordieHowe/Model/Quantum/Core/Oracle.lean`): one pair of
  registers `X`, `Y`, and `⊕` is the addition of `Y`. For `Y = I → J → ZMod 2` this is XOR.

- "A t-query quantum oracle algorithm A is specified via m, n ∈ N, t unitary operators
  A_1, …, A_t and an initial state |φ_0⟩ on four registers X, Y, S, T. The register X is on m
  qubits and is for queries to the oracle; the register Y is on n qubits and is for answers from
  the oracle; the register S is for the output of A; and the register T is for scratch space of
  A. The initial state |φ_0⟩ and unitary operators A_i need not be efficiently computable."
  `QueryAlg X Y t O`: the registers `S` and `T` together are the work register `W`, a finite
  type chosen by the algorithm; the computational basis is `QueryReg W 1 X Y = W × (Fin 1 → X ×
  Y)`. The unitaries are `step 1, …, step t`; `step 0` is applied to `init` first, so `|φ_0⟩` is
  `step 0 init` (as in `OracleAlg`, AHU19's form, where a unitary precedes the first query).

- "We write A^f to denote A_t O_f A_{t−1} O_f ⋯ A_1 O_f |φ_0⟩, the final state of the adversary
  before measurement. (We implicitly extend O_f to act as the identity on S, T.)"
  `A.final f`, the final state of `A.toOracleAlg E` with oracle `permOp (queryPerm f)` (it does
  not depend on `E`).

- "We write A^f to denote the random variable which is the outcome of measuring the register S
  of A^f in the computational basis. This is the output of A when accessing the oracle f."
  `A.outLaw f`: the work register is measured in the computational basis and the outcome `w` is
  read as the output `A.out w`. The output map is the register `S`: measuring `W = S × T` and
  forgetting `T` gives the law of measuring `S` alone (`prob_preimage`). The output type `O`
  need not be finite; `A.out` has finitely many values.

- "A random oracle is a function h : {0,1}^m → {0,1}^n sampled from U(m, n), the uniform
  distribution over functions from {0,1}^m to {0,1}^n. … In the quantum random oracle model
  [BDFLSZ11], we study A^h for h ← U(m, n)."
  `A.realLaw e`: the joint law of the output of `A^h` and the oracle, `h ← U(m, n)` uniform on
  `X → Y`; the oracle is returned read through an equivalence `e : Y ≃ B` (the soundness layer
  reads oracle answers as bytes).

Role. `QueryAlg` is a proof tool. The model is the mixed adversary of `GordieHowe/Model/Quantum/Core/Model.lean`
(HU25 Definition 6.3 in finite dimension, with parallel queries and auxiliary input as
constructions on it). Every core algorithm has a `QueryAlg` with the same query depth and the same
output law under every oracle (`Alg.outLaw_toQueryAlgCoh`, `GordieHowe/Model/QROM/CoherentBridgeCore.lean`): a halting flag
makes its trace-non-increasing Kraus maps trace-preserving, and the dilation of
`GordieHowe/Model/Quantum/Core/MixedAlg.lean` (purification, Stinespring, Naimark) makes it unitary. The results
proved for `QueryAlg` (CMS19's compressed oracle, database extraction) reach
the model through that bridge.

Query count. `A` makes exactly `t` queries. An algorithm with fewer queries is padded: before an
extra query its unitary moves the query input into the work register and puts the answer
register into the uniform superposition, which every `U_f` fixes (`GordieHowe/Model/Quantum/Pure/Algorithm.lean`).
-/

open Finset
open scoped BigOperators ENNReal

namespace GordieHowe.Quantum

/-- **A `t`-query quantum oracle algorithm with output in `O`** (CMS19 section 3.2, p. 14, in
the model of AHU19 pp. 8–9 with one query register): a work register `W`, an initial unit
vector, `t + 1` unitaries applied alternately with `t` oracle steps, and the output read from
the computational-basis measurement of the work register. -/
structure QueryAlg (X Y : Type) [Fintype X] [Fintype Y] (t : ℕ) (O : Type) where
  /-- The work register: CMS19's output register `S` and scratch register `T`. -/
  W : Type
  [instFintype : Fintype W]
  [instDecidableEq : DecidableEq W]
  /-- The initial state. -/
  init : QState (QueryReg W 1 X Y)
  norm_init : ‖init‖ = 1
  /-- The unitaries; `step k` is applied after the `k`-th oracle step (`step 0` first). -/
  step : Fin (t + 1) → QState (QueryReg W 1 X Y) ≃ₗᵢ[ℂ] QState (QueryReg W 1 X Y)
  /-- The output read from a computational-basis outcome of the work register. -/
  out : W → O

attribute [instance] QueryAlg.instFintype QueryAlg.instDecidableEq

namespace QueryAlg

variable {X Y O : Type} [Fintype X] [Fintype Y] {t : ℕ} (A : QueryAlg X Y t O)

/-- `A` as an AHU19 oracle algorithm (`OracleAlg`) with no input and query depth `t`, whose
output bit is `1` on the outcomes with output in `E`. -/
def toOracleAlg (E : Set O) : OracleAlg Unit (QueryReg A.W 1 X Y) t where
  init _ := A.init
  norm_init _ := A.norm_init
  step _ := A.step
  accept _ := {r | A.out r.1 ∈ E}

variable [AddGroup Y]

/-- **`A^f`, the final state with oracle `f`** (CMS19 p. 14):
`A_t O_f A_{t−1} O_f ⋯ A_1 O_f |φ_0⟩` with `O_f = permOp (queryPerm f)`. -/
noncomputable def final (f : X → Y) : QState (QueryReg A.W 1 X Y) :=
  (A.toOracleAlg ∅).final (queryPerm f) ()

@[simp]
theorem norm_final (f : X → Y) : ‖A.final f‖ = 1 :=
  (A.toOracleAlg ∅).norm_final _ _

/-- **The output of `A` with oracle `f`** (CMS19 p. 14): the law of `A.out w` for the outcome
`w` of measuring the work register of `A^f` in the computational basis. -/
noncomputable def outLaw (f : X → Y) : PMF O :=
  (born (A.final f) (A.norm_final f)).map fun r => A.out r.1

variable [DecidableEq X] [Nonempty Y] {B : Type}

/-- **The law of the output and the oracle in the quantum random-oracle model** (CMS19 p. 14,
"we study A^h for h ← U(m, n)"): `h` uniform on `X → Y`, the output of `A^h`, and `h` read
through `e`. -/
noncomputable def realLaw (e : Y ≃ B) : PMF (Outcome O X B) :=
  (PMF.uniformOfFintype (X → Y)).bind fun f => (A.outLaw f).map fun o => ⟨o, e ∘ f⟩

end QueryAlg

namespace QueryAlg

variable {X Y O O' : Type} [Fintype X] [Fintype Y] {t : ℕ} (A : QueryAlg X Y t O)

/-- `A` with its output read through `g`. -/
def mapOut (g : O → O') : QueryAlg X Y t O' where
  W := A.W
  init := A.init
  norm_init := A.norm_init
  step := A.step
  out := g ∘ A.out

variable [AddGroup Y]

theorem outLaw_mapOut (g : O → O') (f : X → Y) : (A.mapOut g).outLaw f = (A.outLaw f).map g := by
  rw [outLaw, outLaw, PMF.map_comp]
  rfl

theorem realLaw_mapOut [DecidableEq X] [Nonempty Y] {B : Type} (g : O → O') (e : Y ≃ B) :
    (A.mapOut g).realLaw e = (A.realLaw e).map (Outcome.mapOut g) := by
  simp only [realLaw, outLaw_mapOut, PMF.map_bind, PMF.map_comp]
  rfl

end QueryAlg

end GordieHowe.Quantum
