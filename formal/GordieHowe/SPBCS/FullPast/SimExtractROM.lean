-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.FullPast.SimExtractGame
public import GordieHowe.SPBCS.FullPast.Verifier
public import GordieHowe.SPBCS.Extraction.KnowledgeError
public import GordieHowe.Model.QROM.QueryBits
public import GordieHowe.Model.QROM.QueryCount
public import GordieHowe.Model.ROM.Model
public import GordieHowe.SPBCS.Merkle.TreeProg

@[expose] public section

/-!
# Simulation-sound extractability in the classical random-oracle model

Weak simulation-sound extractability with straight-line extraction (Unruh 2017, ePrint 2017/398,
Definition 14, p. 21, eq. (6), weak variant: the adversary's statement is none of its simulation
proof queries), against classical adversaries: the game at the series–parallel base model (`GordieHowe.SPBCS.FullPast`).

**The adversary** (`SEProg`): a classical interactive algorithm as a tree; at each node it queries
the oracle in force at a point, sends a statement to the simulation oracle, or outputs a claim (a
statement and a proof). `QueryBound p tq`: on every branch at most `tq` oracle queries; proof queries are
not counted.

**The game** (`SEProg.compose`). The base oracle `h` is uniform. A query of the adversary is answered by
the oracle in force, `h` reprogrammed by the simulator's assignments so far; proof query number
`i < Q` runs the simulator program on the queried statement with coins `c i` against the oracle
in force, returns its proof and appends its assignments; later proof queries are refused. The whole run
is a classical program against the base oracle (`SEProg.compose`), followed by the verifier's queries on
the output under the final oracle (`GordieHowe.SPBCS.romGame`), so its query table is a database of base
answers (`GordieHowe.SPBCS.gameLog`): the adversary's, the simulator's and the verifier's queries,
each recorded with the base answer; simulator-programmed values do not enter it.

The objects: `SEProg`, `SEProg.QueryBound`, `SEProg.Result`, `SEProg.inForce` (with
`run_inForce`, `trace_inForce`), `SEProg.compose` (with `length_trace_compose`); at the model,
`ROMAdversary` and `baseAlg`. The game, its result, its win event and its query table at the spBCS
compiler are `GordieHowe.SPBCS.romGame`, `romResult`, `WinsROM` and `gameLog`
(`GordieHowe/SPBCS/SimExtractROM.lean`).

**The theorem** is the spBCS compiler's (`GordieHowe.SPBCS.simulation_sound_extractability_rom_joint`, CY24
Definition 5.1.1 joint form, `GordieHowe/SPBCS/SimExtractROM.lean`): its extractor reads the query
table of this game through the translation of the database, and is straight-line with no queries.
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm Quantum GordieHowe.QROM
open scoped NNReal ENNReal

variable {k kN kS L e : ℕ}

/-! ### Classical interactive adversaries and the composed run -/

/-- **A classical interactive adversary** of the simulation-extraction game, as a tree: query the
oracle in force at a point, send a proof query to the simulation oracle (the reply is a proof, or
`none` once the proof queries are exhausted), or output. -/
inductive SEProg (A B Req Resp C : Type) where
  /-- Output. -/
  | done (c : C)
  /-- Query the oracle in force at `a`. -/
  | query (a : A) (k : B → SEProg A B Req Resp C)
  /-- Send the proof query `r`. -/
  | request (r : Req) (k : Option Resp → SEProg A B Req Resp C)

namespace SEProg

variable {A B Req Resp C : Type}

/-- **At most `n` oracle queries on every branch** (proof queries are not counted). -/
inductive QueryBound : SEProg A B Req Resp C → ℕ → Prop
  | done (c : C) (n : ℕ) : QueryBound (.done c) n
  | query (a : A) (k : B → SEProg A B Req Resp C) (n : ℕ) :
      (∀ b, QueryBound (k b) n) → QueryBound (.query a k) (n + 1)
  | request (r : Req) (k : Option Resp → SEProg A B Req Resp C) (n : ℕ) :
      (∀ o, QueryBound (k o) n) → QueryBound (.request r k) n

/-- The result of a composed run: the adversary's output, the assignments in force and the
statements sent to the simulator. -/
structure Result (A B Req C : Type) where
  /-- The adversary's output. -/
  out : C
  /-- The assignments in force at the end. -/
  ass : List (Assignment A B)
  /-- The statements sent to the simulator. -/
  queried : List Req

variable [DecidableEq A] {SC : Type} (Sim : Req → SC → OracleProg A B (NARG.SimOutput A B Resp))
  {Q : ℕ} (c : Fin Q → SC)

/-- A program run against the oracle `h` reprogrammed by `ass`, as a program against `h`. -/
def inForce (ass : List (Assignment A B)) {R : Type} (p : OracleProg A B R) : OracleProg A B R :=
  OracleProg.translate id (fun a b => (lastAssign ass a).getD b) p

theorem run_inForce (ass : List (Assignment A B)) {R : Type} (p : OracleProg A B R) (h : A → B) :
    (inForce ass p).run h = p.run (h.reprogram ass) := by
  rw [inForce, OracleProg.run_translate]
  congr 1
  funext a
  exact (reprogram_apply_eq_lastAssign h ass a).symm

theorem trace_inForce (ass : List (Assignment A B)) {R : Type} (p : OracleProg A B R) (h : A → B) :
    (inForce ass p).trace h = p.trace (h.reprogram ass) := by
  rw [inForce, OracleProg.trace_translate, List.map_id]
  congr 1
  funext a
  exact (reprogram_apply_eq_lastAssign h ass a).symm

/-- **The composed run** of the adversary with the simulation oracle, as a classical program
against the base oracle: a query is answered by the oracle in force; proof query number `i < Q` runs
the simulator with coins `c i` against the oracle in force and appends its assignments. -/
def compose : SEProg A B Req Resp C → List (Assignment A B) → ℕ → List Req →
    OracleProg A B (Result A B Req C)
  | .done o, ass, _, qs => .pure ⟨o, ass, qs⟩
  | .query a k, ass, i, qs => .query a fun b => compose (k ((lastAssign ass a).getD b)) ass i qs
  | .request r k, ass, i, qs =>
    if hi : i < Q then
      (inForce ass (Sim r (c ⟨i, hi⟩))).bind fun so =>
        compose (k (some so.proof)) (ass ++ so.assignments) (i + 1) (qs ++ [r])
    else compose (k none) ass i qs

/-- **The composed run makes at most `n + Q · q` queries**: `n` of the adversary and `q` per
answered proof query. -/
theorem length_trace_compose {q : ℕ} (hq : ∀ r s G, ((Sim r s).trace G).length ≤ q) :
    ∀ (p : SEProg A B Req Resp C) (n : ℕ), p.QueryBound n → ∀ ass i qs (h : A → B), i ≤ Q →
      ((compose Sim c p ass i qs).trace h).length ≤ n + (Q - i) * q := by
  intro p n hp
  induction hp with
  | done o n => intro ass i qs h _; simp [compose]
  | query a k n _ ih =>
    intro ass i qs h hi
    simp only [compose, OracleProg.trace_query, List.length_cons]
    have := ih ((lastAssign ass a).getD (h a)) ass i qs h hi
    omega
  | request r k n _ ih =>
    intro ass i qs h hi
    unfold compose
    split_ifs with hi'
    · rw [OracleProg.trace_bind, List.length_append, trace_inForce]
      have h1 := hq r (c ⟨i, hi'⟩) (h.reprogram ass)
      set so := (inForce ass (Sim r (c ⟨i, hi'⟩))).run h
      have h2 := ih (some so.proof) (ass ++ so.assignments) (i + 1) (qs ++ [r]) h hi'
      have : (Q - i) * q = q + (Q - (i + 1)) * q := by
        rw [show Q - i = (Q - (i + 1)) + 1 by omega, Nat.add_mul, one_mul, Nat.add_comm]
      omega
    · exact ih none ass i qs h hi

end SEProg

namespace Base

variable {ι : Type} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] {t : SPTerm ι} {X : Type}
  (M : Base P t X k kN kS L e) (B : ℕ) [∀ j i, Fintype ((M.comp j).MessageWrite i)]

/-! ### The game -/

variable {V : X → FullTr P t → Bool} (Qs : ∀ x, M.IOPQueries V x)
  {E₀ : (j : ι) → (M.comp j).Encoder} (VE : M.ViewEncoder E₀ Qs) {Pub : Type} (pub : X → Pub)
  (S : CausalJointSimulator VE.MV Pub) (T : M.Preimages) {X' : Type} (fx : X' → X)

/-- The trivial algorithm the game is appended to. -/
def baseAlg : ROM.Alg (Query k kN kS L) (Out k e) Unit 0 :=
  ⟨fun _ => .xof (fun _ => 0) fun _ => 0, fun _ => ()⟩

end Base

namespace FullPast

open Base

variable {ι : Type} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] {t : SPTerm ι} {X : Type}
  (M : FullPast P t X k kN kS L e) (B : ℕ) [∀ j i, Fintype ((M.comp j).MessageWrite i)]

/-! ### The game -/

variable {V : X → FullTr P t → Bool} (Qs : ∀ x, M.IOPQueries V x)
  {E₀ : (j : ι) → (M.comp j).Encoder} (VE : M.ViewEncoder E₀ Qs) {Pub : Type} (pub : X → Pub)
  (S : CausalJointSimulator VE.MV Pub) (T : M.Preimages) {X' : Type} (fx : X' → X)

/-- A classical adversary of the game: proof queries in `X'`, replies the simulator's proofs, output a
claim. -/
abbrev ROMAdversary (X' : Type) : Type :=
  SEProg (Query k kN kS L) (Out k e) X' (M.Response B) (Claim X M.NIProof)

end FullPast

end GordieHowe.SPBCS
