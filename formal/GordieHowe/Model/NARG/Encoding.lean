-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.QROM.NIZK

@[expose] public section

/-!
# Encoding the oracle of a program

The honest parties of a non-interactive argument are programs with queries in `A` and answers in
`B` (`GordieHowe.NARG.Prover`, `GordieHowe.NARG.Simulator`). In the quantum random-oracle model the
oracle has inputs in a register `X` (bit strings) and outputs in a group `Y`, and the same program
runs with each query written into `X` and each answer read from `Y`.

- `OracleEncoding A B X Y`: an injective encoding of the queries and an equivalence of the
  answers.
- `Prover.encode`, `Simulator.encode`: the program with its queries encoded and its answers decoded
  (`OracleProg.mapQuery`); the simulator's assignments are encoded the same way.
- `OracleEncoding.decode`: the oracle `A → B` read off an oracle `X → Y`;
  `OracleEncoding.decode_reprogram`: reprogramming by encoded assignments is reprogramming the
  decoded oracle.
-/

namespace GordieHowe.NARG

/-- **An encoding of an oracle `A → B` into an oracle `X → Y`**: the queries written into `X` by
an injective map, the answers read from `Y` by an equivalence. -/
structure OracleEncoding (A B X Y : Type*) where
  /-- The encoding of a query. -/
  query : A → X
  /-- Distinct queries have distinct encodings. -/
  query_injective : Function.Injective query
  /-- The answers. -/
  answer : Y ≃ B

namespace OracleEncoding

variable {A B X Y : Type*} (enc : OracleEncoding A B X Y)

/-- **The oracle read off `H`**: the answer of `H` at the encoded query, decoded. -/
def decode (H : X → Y) : A → B :=
  enc.answer ∘ H ∘ enc.query

/-- An assignment encoded: its input encoded, its output read back into `Y`. -/
def assignment (a : Quantum.Assignment A B) : Quantum.Assignment X Y :=
  ⟨enc.query a.input, enc.answer.symm a.output⟩

/-- **Reprogramming by encoded assignments is reprogramming the decoded oracle.** -/
theorem decode_reprogram [DecidableEq A] [DecidableEq X] (H : X → Y)
    (ass : List (Quantum.Assignment A B)) :
    enc.decode (H.reprogram (ass.map enc.assignment)) = (enc.decode H).reprogram ass := by
  induction ass using List.reverseRecOn generalizing H with
  | nil => rfl
  | append_singleton l c ih =>
    funext a
    simp only [List.map_append, List.map_cons, List.map_nil, QROM.reprogram_append] at ih ⊢
    rw [← ih]
    simp only [decode, Function.comp_apply, Function.reprogram, List.foldl_cons, List.foldl_nil,
      assignment]
    by_cases hac : a = c.input
    · subst hac
      simp
    · rw [Function.update_of_ne (fun e => hac (enc.query_injective e)), Function.update_of_ne hac]
      rfl

end OracleEncoding

variable {A B X Y Stmt Wit Proof Coins SimCoins : Type*} (enc : OracleEncoding A B X Y)

/-- **The prover run against an encoded oracle**: each query encoded, each answer decoded
(`OracleProg.mapQuery`). -/
def Prover.encode (P : Prover A B Stmt Wit Proof Coins) : Prover X Y Stmt Wit Proof Coins :=
  P.mapQuery enc.query enc.answer

/-- **The simulator run against an encoded oracle**: each query encoded, each answer decoded, and
its assignments encoded.

Running time: that of `S`, with one encoding per query and per assignment. This running time is
argued here, not proved in Lean. -/
def Simulator.encode (S : Simulator A B Stmt Proof SimCoins) : Simulator X Y Stmt Proof SimCoins where
  prog x c := ((S.prog x c).bind fun r =>
    .pure ⟨r.proof, r.assignments.map enc.assignment⟩).mapQuery enc.query enc.answer
  coins_nonempty := S.coins_nonempty
  q := S.q
  prog_queries x c h := by
    rw [OracleProg.length_trace_mapQuery, OracleProg.trace_bind, OracleProg.trace_pure,
      List.append_nil]
    exact S.prog_queries x c _

@[simp] theorem Prover.toFn_encode_prove (P : Prover A B Stmt Wit Proof Coins) (H : X → Y)
    (x : Stmt) (w : Wit) (c : Coins) :
    (P.encode enc).toFn.prove H x w c = P.toFn.prove (enc.decode H) x w c :=
  OracleProg.run_mapQuery _ _ _ _

@[simp] theorem Prover.coins_encode (P : Prover A B Stmt Wit Proof Coins) :
    (P.encode enc).coins = P.coins := rfl

@[simp] theorem Simulator.toFn_encode_run (S : Simulator A B Stmt Proof SimCoins) (H : X → Y)
    (x : Stmt) (c : SimCoins) :
    (S.encode enc).toFn.run H x c =
      ⟨(S.toFn.run (enc.decode H) x c).proof,
        (S.toFn.run (enc.decode H) x c).assignments.map enc.assignment⟩ := by
  simp only [Simulator.toFn_run, Simulator.encode, OracleProg.run_mapQuery, OracleProg.run_bind,
    OracleProg.run_pure]
  rfl

@[simp] theorem Prover.encode_comap {Stmt' Wit' : Type*} (P : Prover A B Stmt Wit Proof Coins)
    (fx : Stmt' → Stmt) (fw : Wit' → Wit) : (P.comap fx fw).encode enc = (P.encode enc).comap fx fw :=
  rfl

@[simp] theorem Simulator.encode_comap {Stmt' : Type*} (S : Simulator A B Stmt Proof SimCoins)
    (fx : Stmt' → Stmt) : (S.comap fx).encode enc = (S.encode enc).comap fx :=
  rfl

end GordieHowe.NARG
