-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Pure.Game
public import GordieHowe.Model.Quantum.Pure.Budget
public import GordieHowe.Foundations.ToMathlib.PMFTV
public import GordieHowe.Foundations.Probability.Advantage
public import Mathlib.Tactic.DeriveFintype
public import GordieHowe.Model.NARG.Prover
public import GordieHowe.Model.NARG.Simulator

@[expose] public section

/-!
# Zero knowledge of a non-interactive argument in the quantum random-oracle model

A non-interactive argument with oracle `H : X → Y` has statements `Stmt`, witnesses `Wit`,
proofs `Proof` and a relation `rel`. Its honest prover (`GordieHowe.NARG.ProverFn`) computes a proof from the
oracle, a statement, a witness and coins. A simulator (`Simulator`) computes a proof and an
assignment list from the oracle in force, a statement and uniform coins; the assignment list
reprograms the oracle (`reprogram`).

The zero-knowledge experiment is the game of `GordieHowe/Model/Quantum/Pure/Game.lean` with proof queries
`⟨x, w⟩ : ProofQuery Stmt Wit` and responses in `Option Proof`:

- **Real** (`realEnv`): the tape is a uniform oracle `H` and independent prover coins for each
  of the first `Q` proof queries. Proof query `(x, w)` is answered by `P.prove H x w` with that proof query's coins if
  `rel x w`, and by `none` (`⊥`) otherwise. The oracle never changes.
- **Simulated** (`simEnv`): the tape is a uniform initial oracle and independent simulator
  coins for each proof query. A valid proof query `(x, w)` runs `S.run H' x` on the oracle `H'` in force,
  answers with its proof, and replaces the oracle by `H'.reprogram ass`; an invalid one is
  answered by `none` and leaves the oracle unchanged.

`advantage` is the difference of the two acceptance probabilities.

## The definition

Unruh 2017 ("Post-quantum security of Fiat-Shamir", ASIACRYPT 2017, ePrint 2017/398),
Definition 6, p. 14: "For the following definition, a simulator is a classical stateful
algorithm S. Upon invocation, S(1^η, x) returns a proof π. Additionally, S may reprogram the
random oracle. That is, S may choose an assignment-list ass, and H will then be replaced by
H(ass). Definition 6 (Zero-knowledge) Given a simulator S, the oracle S′(x, w) runs S(1^η, x)
and returns the latter's output. Given a prover P, the oracle P′(x, w) runs P(1^η, x, w) and
returns the latter's output. A non-interactive proof system (P, V) is zero-knowledge iff there
is a quantum-polynomial-time simulator S such that for every quantum-polynomial-time oracle
algorithm A there is a negligible µ such that for all η, |Pr[b = 1 : H ←$ Fun(ℓ^in_η, ℓ^out_η),
b ← A^{H,P′}(1^η)] − Pr[b = 1 : H ←$ Fun(ℓ^in_η, ℓ^out_η), b ← A^{H,S′}(1^η)]| ≤ µ(η). (1) Here
we quantify only over A that never query (x, w) ∉ R from the P′ or S′-oracle."

`ZeroKnowledgeAfterAdaptive rel P S ε` makes it concrete: for every query bound `t`, every
distinguisher with `m` slots of `n` parallel queries or one proof query each and a budget
(`Distinguisher.Budget`) of `q` query slots with `n * q ≤ t`, against an environment answering `Q`
proof queries, and every final unitary that depends on the whole oracle in force, has advantage at
most `ε t Q` against the simulator `S`. Its knobs:

- K1, number of proofs: many, `Q` proof queries (proof queries beyond the `Q`-th are answered by `⊥` in
  both games).
- K2, statement choice and schedule: adaptive. The distinguisher's unitaries prepare the request
  register after its earlier queries and responses, and its kind register decides at each slot,
  in superposition, whether to make a proof query or a hash query (`GordieHowe/Model/Quantum/Pure/Game.lean`).
- K3, oracle access before a proof: at most `t` quantum queries in all, counting each query slot
  as `n` queries. The count is per branch: a budget (`Distinguisher.Budget`) of `q` query slots
  with `n * q ≤ t`, each branch choosing at run time at which of its slots it queries (Unruh 2017,
  p. 10, oracle algorithms).
- K4, distinguisher after the proof: after the last slot the distinguisher also applies a unitary
  that depends on the whole oracle in force, with no query bound.
- K5, oracle access type: quantum, parallel superposition queries.
- K6, what the simulator may do: program by an assignment list over the oracle in force. It is
  not invoked on queries.
- K7, simulator order: `∃ S ∀ t`, as in Unruh 2017 Definition 6 (`∃ S ∀ A`): one simulator
  for every query bound; only the error depends on `t`.

Recorded choices:

- **The simulator reads the oracle in force.** CY24 Definition 7.1.8 (p. 74) writes
  `(π, µ) ← S^f(x)` and CMS19 section 3.3 (p. 15) writes `(µ, π) ← S^h(x)`: the simulator has
  oracle access. Unruh 2017 Definition 6 does not say whether `S` reads `H`. Here `S.run` receives
  the whole function, which covers oracle access with any number of classical queries.
- **The simulator is stateless apart from the oracle.** Unruh's `S` is stateful. Here `S.run`
  sees the oracle in force, which holds its earlier assignments, its own fresh coins and the
  statement. A simulator of this form is a stateful simulator, so the property here implies
  Unruh's form.
- **Invalid proof queries are answered by `⊥` in both games** (Unruh 2015 Definition 2, p. 6:
  "If (x, w) ∉ R, return ⊥"; FKMV12 Definition 4 and BPW12 Definition 1 likewise). Unruh 2017
  instead quantifies only over distinguishers that never make an invalid proof query. Every such
  distinguisher is a distinguisher here, with the same responses, so the property here implies
  that form.
- **The responses carry no `η`.** The statement is concrete: the error is the function `ε` of
  the query bound and the number of proof queries, for fixed types.

## Simulators and running time

A simulator is a `Simulator`, and every definition of that type must have a docstring with a
"Running time" paragraph (enforced by `scripts/CostLint.lean`) that bounds the number of oracle
points it reads, the length of its assignment list and the size of its coins. Zero knowledge is
stated with a named simulator: an unrestricted simulator could find a witness by brute force and run
the honest prover. -/

open Finset
open scoped BigOperators

namespace GordieHowe

namespace QROM

variable {X Y Stmt Wit Proof Coins SimCoins : Type*}

/-- Reprogramming by an assignment list: `H.reprogram [(x₁ := y₁), …, (xₖ := yₖ)]` is
`H(x₁ := y₁)…(xₖ := yₖ)`, so later assignments take precedence. Unruh 2017 (ePrint 2017/398),
section 2, p. 7: "We call a list ass = (x1 := y1, . . . , xn := yn) an assignment-list. We then
write H(ass) for H(x1 := y1)(x2 := y2) . . . (xn := yn). (That is, H is updated to return yi on
input xi, with assignments occurring later in ass taking precedence.)" -/
def _root_.Function.reprogram (H : X → Y) [DecidableEq X] (ass : List (Quantum.Assignment X Y)) : X → Y :=
  ass.foldl (fun h a => Function.update h a.input a.output) H

section Reprogram

variable [DecidableEq X]

/-- Reprogramming by a concatenation is reprogramming by the first list, then by the second. -/
theorem reprogram_append (H : X → Y) (a b : List (Quantum.Assignment X Y)) :
    H.reprogram (a ++ b) = (H.reprogram a).reprogram b := by
  simp [Function.reprogram, List.foldl_append]

/-- Reprogramming leaves the inputs without an assignment unchanged. -/
theorem reprogram_apply_of_forall_ne (H : X → Y) {ass : List (Quantum.Assignment X Y)} {x : X}
    (h : ∀ a ∈ ass, a.input ≠ x) : H.reprogram ass x = H x := by
  induction ass using List.reverseRecOn generalizing H with
  | nil => rfl
  | append_singleton l a ih =>
    rw [Function.reprogram, List.foldl_append, List.foldl_cons, List.foldl_nil, ← Function.reprogram,
      Function.update_of_ne (h a (by simp)).symm, ih H fun b hb => h b (by simp [hb])]

/-- The value of a reprogrammed function at `x` depends only on the value of the original
function at `x`. -/
theorem reprogram_apply_congr {H H' : X → Y} (ass : List (Quantum.Assignment X Y)) {x : X} (h : H x = H' x) :
    H.reprogram ass x = H'.reprogram ass x := by
  induction ass using List.reverseRecOn with
  | nil => exact h
  | append_singleton l a ih =>
    simp only [Function.reprogram, List.foldl_append, List.foldl_cons, List.foldl_nil] at ih ⊢
    by_cases hx : x = a.input
    · subst hx
      simp
    · rw [Function.update_of_ne hx, Function.update_of_ne hx, ih]

/-- Adding a function that vanishes at the assigned inputs commutes with reprogramming. -/
theorem reprogram_add [AddGroup Y] (H D : X → Y) {ass : List (Quantum.Assignment X Y)}
    (h : ∀ a ∈ ass, D a.input = 0) : (H + D).reprogram ass = H.reprogram ass + D := by
  induction ass using List.reverseRecOn with
  | nil => rfl
  | append_singleton l a ih =>
    simp only [Function.reprogram, List.foldl_append, List.foldl_cons, List.foldl_nil] at ih ⊢
    rw [ih fun b hb => h b (by simp [hb])]
    funext x
    by_cases hx : x = a.input
    · subst hx
      simp [h a (by simp)]
    · simp [Function.update_of_ne hx]

end Reprogram

/-! ### Assignment lists with distinct inputs -/

section Distinct

variable [DecidableEq X]

/-- The assignment with its input mapped by `f`. -/
def _root_.GordieHowe.Quantum.Assignment.mapInput {X' : Type*} (f : X → X') (a : Quantum.Assignment X Y) :
    Quantum.Assignment X' Y :=
  ⟨f a.input, a.output⟩

/-- The assignment with its output mapped by `f`. -/
def _root_.GordieHowe.Quantum.Assignment.mapOutput {Y' : Type*} (f : Y → Y') (a : Quantum.Assignment X Y) :
    Quantum.Assignment X Y' :=
  ⟨a.input, f a.output⟩

/-- With distinct inputs, a reprogrammed function takes the assigned value at each input. -/
theorem reprogram_apply_of_mem (F : X → Y) {ass : List (Quantum.Assignment X Y)}
    (hnd : (ass.map Quantum.Assignment.input).Nodup) {a : Quantum.Assignment X Y} (ha : a ∈ ass) :
    F.reprogram ass a.input = a.output := by
  induction ass using List.reverseRecOn with
  | nil => simp at ha
  | append_singleton l b ih =>
    simp only [Function.reprogram, List.foldl_append, List.foldl_cons, List.foldl_nil] at ih ⊢
    rw [List.map_append, List.nodup_append] at hnd
    rcases List.mem_append.1 ha with hl | hb
    · have hne : a.input ≠ b.input := fun e => by
        have := hnd.2.2 a.input (List.mem_map.2 ⟨a, hl, rfl⟩) b.input (by simp)
        exact this e
      rw [Function.update_of_ne hne, ih hnd.1 hl]
    · obtain rfl : a = b := by simpa using hb
      simp

/-- **Counting reprogrammed functions.** For an assignment list with distinct inputs, the
functions `F` with `F.reprogram ass = g` are those that agree with `g` off the inputs, if `g` takes
the assigned values at the inputs, and none otherwise. -/
theorem card_reprogram_eq [Fintype X] [Fintype Y] [DecidableEq Y] (ass : List (Quantum.Assignment X Y))
    (hnd : (ass.map Quantum.Assignment.input).Nodup) (g : X → Y) :
    (Finset.univ.filter fun F : X → Y => F.reprogram ass = g).card =
      if ∀ a ∈ ass, g a.input = a.output then Fintype.card Y ^ ass.length else 0 := by
  classical
  set K := (ass.map Quantum.Assignment.input).toFinset
  have hiff : ∀ F : X → Y, F.reprogram ass = g ↔
      (∀ a ∈ ass, g a.input = a.output) ∧ ∀ x ∉ K, F x = g x := by
    intro F
    constructor
    · rintro rfl
      refine ⟨fun a ha => reprogram_apply_of_mem F hnd ha, fun x hx => ?_⟩
      refine (reprogram_apply_of_forall_ne F fun a ha e => hx ?_).symm
      exact List.mem_toFinset.2 (List.mem_map.2 ⟨a, ha, e⟩)
    · rintro ⟨hg, hF⟩
      funext x
      by_cases hx : x ∈ K
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hx)
        rw [reprogram_apply_of_mem F hnd ha, hg a ha]
      · rw [reprogram_apply_of_forall_ne F fun a ha e =>
          hx (List.mem_toFinset.2 (List.mem_map.2 ⟨a, ha, e⟩)), hF x hx]
  split_ifs with hg
  · rw [Finset.filter_congr fun F _ => (hiff F).trans (and_iff_right hg), ← Fintype.card_subtype]
    have hK : K.card = ass.length := by
      rw [List.toFinset_card_of_nodup hnd, List.length_map]
    rw [← hK, ← Fintype.card_coe K, ← Fintype.card_fun]
    refine Fintype.card_congr
      { toFun := fun F x => F.1 x
        invFun := fun h => ⟨fun x => if hx : x ∈ K then h ⟨x, hx⟩ else g x, fun x hx => by simp [hx]⟩
        left_inv := fun F => Subtype.ext (funext fun x => by
          by_cases hx : x ∈ K
          · simp [hx]
          · simp [hx, F.2 x hx])
        right_inv := fun h => funext fun x => by simp }
  · rw [Finset.filter_congr fun F _ => (hiff F).trans (iff_false_intro fun h => hg h.1)]
    simp

variable {X' : Type*} [DecidableEq X']

/-- Reprogramming at the images of an injective map, read at an image point, is reprogramming the
pulled-back function. -/
theorem reprogram_map_apply {f : X → X'} (hf : Function.Injective f) (G : X' → Y)
    (ass : List (Quantum.Assignment X Y)) (a : X) :
    G.reprogram (ass.map (Quantum.Assignment.mapInput f)) (f a) = (G ∘ f).reprogram ass a := by
  induction ass using List.reverseRecOn with
  | nil => rfl
  | append_singleton l c ih =>
    simp only [List.map_append, List.map_cons, List.map_nil, Function.reprogram, List.foldl_append,
      List.foldl_cons, List.foldl_nil, Quantum.Assignment.mapInput] at ih ⊢
    by_cases hac : a = c.input
    · subst hac
      simp
    · rw [Function.update_of_ne (fun e => hac (hf e)), Function.update_of_ne hac, ih]

/-- Reprogramming at the images of a map leaves the points off its range unchanged. -/
theorem reprogram_map_apply_of_notMem {f : X → X'} (G : X' → Y) (ass : List (Quantum.Assignment X Y))
    {b : X'} (hb : b ∉ Set.range f) : G.reprogram (ass.map (Quantum.Assignment.mapInput f)) b = G b :=
  reprogram_apply_of_forall_ne G fun p hp e => by
    obtain ⟨q, -, rfl⟩ := List.mem_map.1 hp
    exact hb ⟨q.input, e⟩

end Distinct

/-- **A proof query** of the zero-knowledge game: a statement and a witness for it. -/
structure ProofQuery (Stmt Wit : Type*) where
  /-- The statement to prove. -/
  stmt : Stmt
  /-- The witness offered for it. -/
  wit : Wit
  deriving DecidableEq, Fintype

variable [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]

/-- The tape of `Q` proof queries: a uniform oracle and independent coins for each proof query, drawn
from `μ`. -/
noncomputable def tapeDist (Q : ℕ) [Fintype Coins] (μ : PMF Coins) :
    PMF ((X → Y) × (Fin Q → Coins)) :=
  (PMF.uniformOfFintype (X → Y)).bind fun H => (PMF.pi fun _ : Fin Q => μ).map fun c => (H, c)

variable (rel : Stmt → Wit → Prop) [DecidableRel rel]

/-- The real environment for `Q` proof queries: proof query number `i` with `(x, w)` is answered by
`P.prove H x w` with the coins of proof query `i` if `rel x w`, and by `none` otherwise. The oracle
is the uniform `H` of the tape throughout. -/
noncomputable def realEnv [Fintype Coins] (P : NARG.ProverFn X Y Stmt Wit Proof Coins) (Q : ℕ) :
    Quantum.Env ((X → Y) × (Fin Q → Coins)) (ProofQuery Stmt Wit) Proof X Y Q where
  μ := tapeDist Q P.coins
  oracle₀ ω := ω.1
  respond ω i req H :=
    ⟨if rel req.stmt req.wit then some (P.prove H req.stmt req.wit (ω.2 i)) else none, H⟩

/-- The simulated environment for `Q` proof queries: the oracle starts as the uniform `H` of the
tape; proof query `i` with `(x, w)` and `rel x w` runs `S.run H' x` with the coins of proof query `i` on
the oracle `H'` in force, answers with its proof and replaces the oracle by
`H'.reprogram ass`. An invalid proof query is answered by `none` and leaves the oracle unchanged. -/
noncomputable def simEnv [Fintype SimCoins] (S : NARG.SimulatorFn X Y Stmt Proof SimCoins) (Q : ℕ) :
    Quantum.Env ((X → Y) × (Fin Q → SimCoins)) (ProofQuery Stmt Wit) Proof X Y Q where
  μ := tapeDist Q S.coins
  oracle₀ ω := ω.1
  respond ω i req H :=
    if rel req.stmt req.wit then
      let r := S.run H req.stmt (ω.2 i)
      ⟨some r.proof, H.reprogram r.assignments⟩
    else ⟨none, H⟩

variable [AddGroup Y] [Fintype Stmt] [DecidableEq Stmt] [Fintype Wit] [DecidableEq Wit]
  [Fintype Proof] [DecidableEq Proof] [Fintype Coins] [Fintype SimCoins]
  {W : Type} [Fintype W] {n m Q : ℕ}

/-- The advantage of a distinguisher `D` with final unitary `post`: the difference of its
acceptance probabilities in the real and the simulated game, as a `GordieHowe.advantage`. -/
noncomputable def advantage (P : NARG.ProverFn X Y Stmt Wit Proof Coins)
    (S : NARG.SimulatorFn X Y Stmt Proof SimCoins) (D : Quantum.Distinguisher W X Y (ProofQuery Stmt Wit) Proof n m)
    (post : (X → Y) → Quantum.QState (Quantum.DReg W n X Y (ProofQuery Stmt Wit) Proof) ≃ₗᵢ[ℂ]
      Quantum.QState (Quantum.DReg W n X Y (ProofQuery Stmt Wit) Proof)) : ℝ :=
  GordieHowe.advantage (D.acceptProb (realEnv rel P Q) post) (D.acceptProb (simEnv rel S Q) post)

/-- **Zero knowledge, unbounded after the last slot, against distinguishers with a query budget**
(Unruh 2017 Definition 6, p. 14, whose adversaries are oracle
algorithms choosing at run time which oracle to call, p. 10). For every query bound `t`, every
distinguisher with `m` slots of `n` parallel queries or one proof query and a budget of `q` query
slots (`Distinguisher.Budget`: on every branch at most `q` slots are queries, at slots the branch
chooses at run time) with `n * q ≤ t`, against environments answering `Q` proof queries, and every
final unitary `post` that depends on the whole oracle in force at the end, has advantage at most
`ε t Q` against the simulator `S`. Request slots are not counted; after the last slot the
distinguisher is unbounded. -/
def ZeroKnowledgeAfterAdaptive (P : NARG.ProverFn X Y Stmt Wit Proof Coins)
    (S : NARG.SimulatorFn X Y Stmt Proof SimCoins) (ε : ℕ → ℕ → ℝ) : Prop :=
  ∀ (t : ℕ) (W : Type) [Fintype W] (n m Q q : ℕ)
    (D : Quantum.Distinguisher W X Y (ProofQuery Stmt Wit) Proof n m)
    (post : (X → Y) → Quantum.QState (Quantum.DReg W n X Y (ProofQuery Stmt Wit) Proof) ≃ₗᵢ[ℂ]
      Quantum.QState (Quantum.DReg W n X Y (ProofQuery Stmt Wit) Proof)) (_ : D.Budget q),
    n * q ≤ t → QROM.advantage (Q := Q) rel P S D post ≤ ε t Q

/-- A larger error bound. -/
theorem ZeroKnowledgeAfterAdaptive.mono {P : NARG.ProverFn X Y Stmt Wit Proof Coins}
    {S : NARG.SimulatorFn X Y Stmt Proof SimCoins} {ε ε' : ℕ → ℕ → ℝ}
    (h : ZeroKnowledgeAfterAdaptive rel P S ε) (hε : ∀ t Q, ε t Q ≤ ε' t Q) :
    ZeroKnowledgeAfterAdaptive rel P S ε' :=
  fun t W _ n m Q q D post bud hD => (h t W n m Q q D post bud hD).trans (hε t Q)

end QROM

end GordieHowe

/-- Injective query and answer encodings preserve distinctions between assignments. -/
theorem GordieHowe.Quantum.Assignment.map_injective {A A' B B' : Type*} {f : A → A'} {g : B → B'}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective fun a : GordieHowe.Quantum.Assignment A B =>
      (⟨f a.input, g a.output⟩ : GordieHowe.Quantum.Assignment A' B') := by
  intro a b h
  simp only [GordieHowe.Quantum.Assignment.mk.injEq] at h
  exact GordieHowe.Quantum.Assignment.ext (hf h.1) (hg h.2)
