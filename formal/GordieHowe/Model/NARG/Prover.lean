-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import GordieHowe.Model.NARG.OracleProg

@[expose] public section

/-!
# The honest prover of a non-interactive argument

The prover of a non-interactive argument with an oracle `X → Y` (the paper's `def:narg`, DFMS22
section 3.1) is a classical oracle program (`GordieHowe.OracleProg`, a tree of queries ending in
a proof, in the style of VCVio's `OracleComp`) on a statement, a witness and coins, with a query
count that is a property of the program (`OracleProg.QueriesLE`).

- `Prover`: the program form, the one object the notions of both oracle models quantify over.
- `ProverFn`: a prover as a function of the oracle. `Prover.toFn` is the semantics of the
  classical random-oracle model: the program run against a function (`OracleProg.run`). In the
  quantum random-oracle model the same program is run query by query in the experiment
  (`GordieHowe.QROM.realChallenger`).

The verifier is `GordieHowe.NARG.Verifier` (`GordieHowe/Model/NARG/Verifier.lean`); the notions of
the argument are in `GordieHowe/Model/NARG/QROM.lean` and `GordieHowe/Model/NARG/ROM.lean`.
-/

namespace GordieHowe.NARG

variable {X Y Stmt Wit Proof Coins : Type*}

/-- **A prover as a function of the oracle**: a proof from the oracle, a statement, a witness and
coins drawn from `coins`. The classical random-oracle semantics of a program prover
(`Prover.toFn`); the generic game lemmas of the classical model are stated for it. -/
structure ProverFn (X Y Stmt Wit Proof Coins : Type*) where
  /-- The proof computed with oracle `H` on statement `x`, witness `w` and coins `c`. -/
  prove : (X → Y) → Stmt → Wit → Coins → Proof
  /-- The distribution of the prover's coins. -/
  coins : PMF Coins

/-- The prover on statements and witnesses read through the maps `fx` and `fw`: on `(x, w)` it
proves `fx x` with the witness `fw w`. -/
def ProverFn.comap {Stmt' Wit' : Type*} (P : ProverFn X Y Stmt Wit Proof Coins) (fx : Stmt' → Stmt)
    (fw : Wit' → Wit) : ProverFn X Y Stmt' Wit' Proof Coins where
  prove H x w c := P.prove H (fx x) (fw w) c
  coins := P.coins

/-- **The honest prover of a non-interactive argument**: on a statement, a witness and coins drawn
from `coins`, a classical oracle program with queries in `X` and answers in `Y` that returns the
proof and makes at most `q` queries (`OracleProg.QueriesLE`). -/
structure Prover (X Y Stmt Wit Proof Coins : Type*) where
  /-- The program. -/
  prog : Stmt → Wit → Coins → OracleProg X Y Proof
  /-- The distribution of the coins. -/
  coins : PMF Coins
  /-- The number of queries. -/
  q : ℕ
  /-- Every run makes at most `q` queries. -/
  prog_queries : ∀ x w c, (prog x w c).QueriesLE q

namespace Prover

/-- **The semantics of the classical random-oracle model**: the program run against the oracle
`H` (`OracleProg.run`). -/
def toFn (P : Prover X Y Stmt Wit Proof Coins) : ProverFn X Y Stmt Wit Proof Coins where
  prove H x w c := (P.prog x w c).run H
  coins := P.coins

@[simp] theorem toFn_prove (P : Prover X Y Stmt Wit Proof Coins) (H : X → Y) (x : Stmt) (w : Wit)
    (c : Coins) : P.toFn.prove H x w c = (P.prog x w c).run H := rfl

@[simp] theorem toFn_coins (P : Prover X Y Stmt Wit Proof Coins) : P.toFn.coins = P.coins := rfl

/-- The prover program on statements and witnesses read through the maps `fx` and `fw`: on
`(x, w)` it runs the program on `fx x` with the witness `fw w`. -/
def comap {Stmt' Wit' : Type*} (P : Prover X Y Stmt Wit Proof Coins) (fx : Stmt' → Stmt)
    (fw : Wit' → Wit) : Prover X Y Stmt' Wit' Proof Coins where
  prog x w c := P.prog (fx x) (fw w) c
  coins := P.coins
  q := P.q
  prog_queries x w c := P.prog_queries (fx x) (fw w) c

@[simp] theorem q_comap {Stmt' Wit' : Type*} (P : Prover X Y Stmt Wit Proof Coins)
    (fx : Stmt' → Stmt) (fw : Wit' → Wit) : (P.comap fx fw).q = P.q := rfl

@[simp] theorem toFn_comap {Stmt' Wit' : Type*} (P : Prover X Y Stmt Wit Proof Coins)
    (fx : Stmt' → Stmt) (fw : Wit' → Wit) : (P.comap fx fw).toFn = P.toFn.comap fx fw := rfl

/-- **The prover with its oracle read through `f` and `g`**: queries `a` become `f a`, answers
`b` are read as `g b` (`OracleProg.mapQuery`). -/
def mapQuery {X' Y' : Type*} (P : Prover X Y Stmt Wit Proof Coins) (f : X → X') (g : Y' → Y) :
    Prover X' Y' Stmt Wit Proof Coins where
  prog x w c := (P.prog x w c).mapQuery f g
  coins := P.coins
  q := P.q
  prog_queries x w c h := (OracleProg.length_trace_mapQuery f g h _).trans_le
    (P.prog_queries x w c _)

/-- **The prover with its proof mapped by `f`**: the same queries, then `f` of the proof (the
serialization of a proof into the proof-query register of a zero-knowledge game). -/
def mapOutput {Proof' : Type*} (P : Prover X Y Stmt Wit Proof Coins) (f : Proof → Proof') :
    Prover X Y Stmt Wit Proof' Coins where
  prog x w c := (P.prog x w c).mapOutput f
  coins := P.coins
  q := P.q
  prog_queries x w c := (P.prog_queries x w c).mapOutput f

@[simp] theorem toFn_mapOutput_prove {Proof' : Type*} (P : Prover X Y Stmt Wit Proof Coins)
    (f : Proof → Proof') (H : X → Y) (x : Stmt) (w : Wit) (c : Coins) :
    (P.mapOutput f).toFn.prove H x w c = f (P.toFn.prove H x w c) :=
  OracleProg.run_mapOutput _ _ _

@[simp] theorem coins_mapOutput {Proof' : Type*} (P : Prover X Y Stmt Wit Proof Coins)
    (f : Proof → Proof') : (P.mapOutput f).coins = P.coins := rfl

@[simp] theorem mapOutput_comap {Proof' Stmt' Wit' : Type*} (P : Prover X Y Stmt Wit Proof Coins)
    (f : Proof → Proof') (fx : Stmt' → Stmt) (fw : Wit' → Wit) :
    (P.comap fx fw).mapOutput f = (P.mapOutput f).comap fx fw := rfl

end Prover

end GordieHowe.NARG
