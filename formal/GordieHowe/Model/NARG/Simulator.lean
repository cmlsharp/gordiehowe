-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Probability.Distributions.Uniform
public import GordieHowe.Model.NARG.OracleProg

@[expose] public section

/-!
# The zero-knowledge simulator of a non-interactive argument

A simulator of a non-interactive argument with an oracle `X → Y` (the paper's `def:narg-zk`,
Unruh 2017 Definition 6, p. 14): from the oracle in force, a statement and uniform coins, a proof
and an assignment list that reprograms the oracle (`Quantum.Assignment`, `Function.reprogram` in
`GordieHowe/Model/QROM/NIZK.lean`). The honest prover is `GordieHowe.NARG.Prover`.
-/

namespace GordieHowe

/-- **An assignment** `x := y` of an assignment list (Unruh 2017, ePrint 2017/398, section 2,
p. 7): the oracle is updated to return `output` on `input`. -/
@[ext]
structure Quantum.Assignment (X Y : Type*) where
  /-- The reprogrammed input. -/
  input : X
  /-- The value returned on `input`. -/
  output : Y

namespace NARG

variable {X Y Stmt Proof SimCoins : Type*}

/-- **The output of a simulator** (Unruh 2017 Definition 6, p. 14): a proof and an assignment
list that reprograms the oracle in force (`Function.reprogram`). -/
structure SimOutput (X Y Proof : Type*) where
  /-- The simulated proof. -/
  proof : Proof
  /-- The assignments appended to the oracle in force. -/
  assignments : List (Quantum.Assignment X Y)

/-- **A simulator as a function of the oracle** (the classical random-oracle semantics of a
program simulator, `Simulator.toFn`): from the oracle in force, a statement and coins drawn uniformly
from the finite type `SimCoins` (`SimulatorFn.coins`), a proof and an assignment list that reprograms the oracle (`Function.reprogram`). It does not
see the witness and is not invoked on oracle queries.

Every definition of this type must document, in a "Running time" paragraph, what the procedure
computes and why it runs in polynomial time, bounding the number of oracle points it reads, the
length of its assignment list and the size of its coins (`scripts/CostLint.lean`). -/
structure SimulatorFn (X Y Stmt Proof SimCoins : Type*) where
  /-- The proof and the assignment list computed with oracle `H` on statement `x` and coins
  `c`. -/
  run : (X → Y) → Stmt → SimCoins → SimOutput X Y Proof
  /-- The coins are drawn uniformly (`SimulatorFn.coins`), so there is at least one. -/
  coins_nonempty : Nonempty SimCoins

/-- **The distribution of a simulator's coins**: uniform on the finite type `SimCoins`. -/
noncomputable abbrev SimulatorFn.coins (S : SimulatorFn X Y Stmt Proof SimCoins) [Fintype SimCoins] :
    PMF SimCoins :=
  haveI := S.coins_nonempty
  PMF.uniformOfFintype SimCoins

/-- A simulator's coins are uniform. -/
theorem SimulatorFn.coins_eq_uniform (S : SimulatorFn X Y Stmt Proof SimCoins) [Fintype SimCoins]
    [Nonempty SimCoins] : S.coins = PMF.uniformOfFintype SimCoins :=
  rfl

/-- The simulator on statements read through the map `fx`: on `x` it simulates `fx x`.

Running time: one run of `S` and one evaluation of `fx`, the decoding of the statement register; the
oracle points read, the assignment list and the coins are those of `S`. This running time is argued
here, not proved in Lean. -/
def SimulatorFn.comap {Stmt' : Type*} (S : SimulatorFn X Y Stmt Proof SimCoins) (fx : Stmt' → Stmt) :
    SimulatorFn X Y Stmt' Proof SimCoins where
  run H x c := S.run H (fx x) c
  coins_nonempty := S.coins_nonempty

/-- **A zero-knowledge simulator** (Unruh 2017 Definition 6, p. 14): on a statement and coins
drawn uniformly from the finite type `SimCoins` (`Simulator.coins`), a classical oracle program
making at most `q` queries to the oracle in force (`OracleProg.QueriesLE`) that returns a proof and
an assignment list reprogramming that oracle (`Function.reprogram`). It does not see the witness.

Every definition of this type must document, in a "Running time" paragraph, what the program
computes and why it runs in polynomial time (`scripts/CostLint.lean`). -/
structure Simulator (X Y Stmt Proof SimCoins : Type*) where
  /-- The program. -/
  prog : Stmt → SimCoins → OracleProg X Y (SimOutput X Y Proof)
  /-- The coins are drawn uniformly (`Simulator.coins`), so there is at least one. -/
  coins_nonempty : Nonempty SimCoins
  /-- The number of queries. -/
  q : ℕ
  /-- Every run makes at most `q` queries. -/
  prog_queries : ∀ x c, (prog x c).QueriesLE q

namespace Simulator

/-- **The distribution of a simulator's coins**: uniform on the finite type `SimCoins`. -/
noncomputable abbrev coins (S : Simulator X Y Stmt Proof SimCoins) [Fintype SimCoins] :
    PMF SimCoins :=
  haveI := S.coins_nonempty
  PMF.uniformOfFintype SimCoins

/-- **The semantics of the classical random-oracle model**: the program run against the oracle in
force (`OracleProg.run`).

Running time: one run of the program, `S.q` oracle points. This running time is argued here, not
proved in Lean. -/
def toFn (S : Simulator X Y Stmt Proof SimCoins) : SimulatorFn X Y Stmt Proof SimCoins where
  run H x c := (S.prog x c).run H
  coins_nonempty := S.coins_nonempty

@[simp] theorem toFn_run (S : Simulator X Y Stmt Proof SimCoins) (H : X → Y) (x : Stmt)
    (c : SimCoins) : S.toFn.run H x c = (S.prog x c).run H := rfl

/-- The simulator program on statements read through the map `fx`: on `x` it runs the program
on `fx x`.

Running time: one run of `S` and one evaluation of `fx`, the decoding of the statement register; the
queries, the assignment list and the coins are those of `S`. This running time is argued here, not
proved in Lean. -/
def comap {Stmt' : Type*} (S : Simulator X Y Stmt Proof SimCoins) (fx : Stmt' → Stmt) :
    Simulator X Y Stmt' Proof SimCoins where
  prog x c := S.prog (fx x) c
  coins_nonempty := S.coins_nonempty
  q := S.q
  prog_queries x c := S.prog_queries (fx x) c

@[simp] theorem q_comap {Stmt' : Type*} (S : Simulator X Y Stmt Proof SimCoins)
    (fx : Stmt' → Stmt) : (S.comap fx).q = S.q := rfl

@[simp] theorem toFn_comap {Stmt' : Type*} (S : Simulator X Y Stmt Proof SimCoins)
    (fx : Stmt' → Stmt) : (S.comap fx).toFn = S.toFn.comap fx := rfl

/-- **The simulator with its proof mapped by `f`**: the same queries and assignments, then `f` of
the proof.

Running time: that of `S`, then one evaluation of `f`. This running time is argued here, not proved
in Lean. -/
def mapOutput {Proof' : Type*} (S : Simulator X Y Stmt Proof SimCoins) (f : Proof → Proof') :
    Simulator X Y Stmt Proof' SimCoins where
  prog x c := (S.prog x c).mapOutput fun r => ⟨f r.proof, r.assignments⟩
  coins_nonempty := S.coins_nonempty
  q := S.q
  prog_queries x c := (S.prog_queries x c).mapOutput _

@[simp] theorem toFn_mapOutput_run {Proof' : Type*} (S : Simulator X Y Stmt Proof SimCoins)
    (f : Proof → Proof') (H : X → Y) (x : Stmt) (c : SimCoins) :
    (S.mapOutput f).toFn.run H x c = ⟨f (S.toFn.run H x c).proof, (S.toFn.run H x c).assignments⟩ :=
  OracleProg.run_mapOutput _ _ _

@[simp] theorem mapOutput_comap {Proof' Stmt' : Type*} (S : Simulator X Y Stmt Proof SimCoins)
    (f : Proof → Proof') (fx : Stmt' → Stmt) : (S.comap fx).mapOutput f = (S.mapOutput f).comap fx :=
  rfl

end Simulator

end NARG

end GordieHowe
