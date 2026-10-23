-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Keccak.Gadgets.Trace

@[expose] public section

/-!
# A batch of Keccak-f chains (`lib/circuits/keccak/keccak_batch.h`)

The skip argument proves a batch of `np` Keccak-f[1600] permutations and nothing else
(`KeccakBatch`, `keccak_batch.h` at `e5daf0a`). Permutation `p` either reads a committed input
state, when `p` is one of the hooked starts (`start()`, lines 120-130), or the previous
permutation's output, shared inside the trace (`chain()`, lines 132-137). The circuit around the
batch supplies each hooked input and consumes the outputs; padding, absorption and squeezing are
circuit gadgets (`GordieHowe.KeccakSponge`).

* `Shape np a`: the `a + 1` hooked starts `start 0 < start 1 < ⋯ < start a`, with
  `start 0 = 0` (the link's `start_perms`, `keccak_skip_circuit_link.h` lines 21-24, checked at
  lines 70-72).
* States (`startState`, `endState`). The link's state inputs are the input of permutation `0`
  (state `0`), the output of every round (state `t + 1` for round `t`), then the input of
  permutation `start j` for `j ≥ 1` (state `24 np + j`) (`state_inputs`, lines 25-29;
  `KeccakBatch::allocate_pads`, `keccak_batch.h` lines 220-225). Permutation `p` reads state
  `startState p`: its own committed state when it is a hooked start other than `0`, else state
  `24 p`, the previous output. Its output is state `endState p = 24 (p + 1)`.
* `stateMap`: round `t` reads `startState (t / 24)` when `t mod 24 = 0` and state `t` otherwise,
  and writes state `t + 1` (`KeccakSkipLink::build`, `keccak_skip_link.h` lines 136-143 at
  `e5daf0a`).
* `Holds sh start fin`: every output is Keccak-f of its input, and an unhooked permutation's input
  is the previous output. `holds_of_rounds` derives it from the round relations along `stateMap` on
  a Boolean trace; `trace` is the honest trace of given inputs, which satisfies the round relations
  (`trace_rounds`).
-/

namespace GordieHowe.KeccakBatch

open GordieHowe.Bits GordieHowe.Keccak GordieHowe.KeccakTrace

/-! ### The shape -/

/-- **The shape of a batch** of `np` permutations with `a + 1` hooked starts: permutation
`start j` reads the `j`-th committed input state; every other permutation reads the previous
output. The starts increase strictly from `start 0 = 0` (`start_perms`,
`keccak_skip_circuit_link.h` lines 21-24 and 70-72). -/
structure Shape (np a : ℕ) where
  start : Fin (a + 1) → Fin np
  start_zero : (start 0 : ℕ) = 0
  strictMono : StrictMono start

namespace Shape

variable {np a : ℕ} (sh : Shape np a)

/-- Permutation `p` reads a committed input state. -/
def Hooked (p : Fin np) : Prop := ∃ j, sh.start j = p

instance (p : Fin np) : Decidable (sh.Hooked p) := inferInstanceAs (Decidable (∃ _, _))

/-- The committed input of a hooked permutation. -/
def hookIdx {p : Fin np} (h : sh.Hooked p) : Fin (a + 1) := Fin.find _ h

theorem start_hookIdx {p : Fin np} (h : sh.Hooked p) : sh.start (sh.hookIdx h) = p :=
  Fin.find_spec h

/-- A hooked permutation other than `0` has a committed input other than the first. -/
theorem hookIdx_pos {p : Fin np} (h : sh.Hooked p) (hp : (p : ℕ) ≠ 0) :
    0 < (sh.hookIdx h : ℕ) := by
  refine Nat.pos_of_ne_zero fun h0 => hp ?_
  rw [← sh.start_hookIdx h, show sh.hookIdx h = 0 from Fin.ext h0]
  exact sh.start_zero

/-- **The prefix shape**: permutations `0, …, a` hooked, every later one chained. -/
def pre (np a : ℕ) (h : a < np) : Shape np a where
  start j := ⟨j, by omega⟩
  start_zero := rfl
  strictMono _ _ hij := hij

theorem pre_hooked_iff {np a : ℕ} {h : a < np} {p : Fin np} :
    (pre np a h).Hooked p ↔ (p : ℕ) ≤ a :=
  ⟨fun ⟨j, hj⟩ => by rw [← hj]; exact Nat.lt_succ_iff.mp j.isLt,
    fun hp => ⟨⟨p, by omega⟩, rfl⟩⟩

end Shape

/-! ### States -/

variable {np a : ℕ}

/-- **The input state of permutation `p`**: state `24 np + j` for the hooked start `p = start j`,
`j ≥ 1`; state `24 p` otherwise (the input of permutation `0`, or the previous output). -/
def startState (sh : Shape np a) (p : Fin np) : Fin (24 * np + 1 + a) :=
  if h : sh.Hooked p ∧ (p : ℕ) ≠ 0 then
    ⟨24 * np + sh.hookIdx h.1, by have := (sh.hookIdx h.1).isLt; omega⟩
  else ⟨24 * p, by have := p.isLt; omega⟩

/-- The output state of permutation `p`, state `24 (p + 1)`. -/
def endState (p : Fin np) : Fin (24 * np + 1 + a) := ⟨24 * (p + 1), by have := p.isLt; omega⟩

theorem startState_of_hooked (sh : Shape np a) {p : Fin np} (h : sh.Hooked p) (hp : (p : ℕ) ≠ 0) :
    startState sh p = ⟨24 * np + sh.hookIdx h, by have := (sh.hookIdx h).isLt; omega⟩ := by
  rw [startState, dif_pos ⟨h, hp⟩]

theorem startState_of_not_hooked (sh : Shape np a) {p : Fin np} (h : ¬ (sh.Hooked p ∧ (p : ℕ) ≠ 0)) :
    startState sh p = ⟨24 * p, by have := p.isLt; omega⟩ := by
  rw [startState, dif_neg h]

/-- **An unhooked permutation reads the previous output.** -/
theorem startState_succ (sh : Shape np a) {p : ℕ} (hp : p + 1 < np) (h : ¬ sh.Hooked ⟨p + 1, hp⟩) :
    startState sh ⟨p + 1, hp⟩ = endState ⟨p, by omega⟩ :=
  startState_of_not_hooked sh fun h' => h h'.1

/-- **The batch's state map** (`KeccakSkipLink::build`, `keccak_skip_link.h` lines 136-143 at
`e5daf0a`): round `t` reads the input state of permutation `t / 24` when it starts that
permutation, state `t` otherwise, and writes state `t + 1`. -/
def stateMap (sh : Shape np a) : StateMap (24 * np) (24 * np + 1 + a) where
  inp t := if (t : ℕ) % 24 = 0 then startState sh ⟨t / 24, by omega⟩ else ⟨t, by omega⟩
  out t := ⟨t + 1, by omega⟩

/-- **The 25 states of permutation `p`**: its input state, then states `24 p + 1, …, 24 p + 24`,
the outputs of its rounds. -/
def block {K : Type*} (sh : Shape np a) (states : Fin (24 * np + 1 + a) → State K) (p : Fin np)
    (i : Fin 25) : State K :=
  if (i : ℕ) = 0 then states (startState sh p) else states ⟨24 * p + i, by omega⟩

section Block

variable {K : Type*} (sh : Shape np a) (states : Fin (24 * np + 1 + a) → State K)

theorem block_zero (p : Fin np) : block sh states p 0 = states (startState sh p) :=
  if_pos rfl

theorem block_last (p : Fin np) : block sh states p (Fin.last 24) = states (endState p) := by
  rw [block, if_neg (by simp)]
  exact congrArg states (Fin.ext (by simp only [endState, Fin.val_last]; ring))

variable {sh states}

/-- **The batch's rounds are the permutations' relations**: along `stateMap sh`, every
permutation block satisfies its 24 round relations. -/
theorem permRelation_block [Field K] (h : (stateMap sh).Rounds roundIndex states) (p : Fin np) :
    PermRelation (block sh states p) := by
  intro i
  have hp := p.isLt
  have hi := i.isLt
  have hr := h ⟨24 * p + i, by omega⟩
  have e0 : roundIndex (np := np) ⟨24 * p + i, by omega⟩ = i :=
    Fin.ext (by simp only [roundIndex]; omega)
  have e1 : states ((stateMap sh).inp ⟨24 * p + i, by omega⟩) = block sh states p i.castSucc := by
    simp only [stateMap, block, Fin.val_castSucc]
    by_cases hi0 : (i : ℕ) = 0
    · rw [if_pos (by omega), if_pos hi0]
      exact congrArg _ (congrArg _ (Fin.ext (by simp only; omega)))
    · rw [if_neg (by omega), if_neg hi0]
  have e2 : states ((stateMap sh).out ⟨24 * p + i, by omega⟩) = block sh states p i.succ := by
    simp only [stateMap, block, Fin.val_succ]
    rw [if_neg (by omega)]
    exact congrArg states (Fin.ext (by simp only; omega))
  rw [e0, e1, e2] at hr
  exact hr

end Block

/-! ### The relation -/

section Relation

variable {K : Type*} [Field K]

/-- Keccak-f[1600] on a state of field bits: 24 rounds, round `r` with constant `r`. -/
-- spec-side
def keccakF (A : State K) : State K := iterRounds A 24

theorem keccakF_allBool [DecidableEq K] {A : State K} (hA : ∀ x y, AllBool (A x y)) (x y : Fin 5) :
    AllBool (keccakF A x y) :=
  iterRounds_allBool hA 24 x y

/-- Keccak-f carries an encoding of `s` to an encoding of the vendored `f1600 s`. -/
theorem Encodes.keccakF [DecidableEq K] [CharP K 2] {A : State K} {s : Array UInt64}
    (h : Shake256.Encodes A s) : Shake256.Encodes (KeccakBatch.keccakF A) (SLHDSA.Concrete.Keccak.f1600 s) :=
  encodes_iterRounds h

/-- On a Boolean first state, a permutation's relations make its last state Keccak-f of its
first. -/
theorem PermRelation.last_eq [DecidableEq K] [CharP K 2] {S : Fin 25 → State K}
    (h : PermRelation S) (h0 : ∀ x y, AllBool (S 0 x y)) : S (Fin.last 24) = keccakF (S 0) := by
  have hr := (permRelation_iff h0).mp h
  have key : ∀ i : Fin 25, S i = iterRounds (S 0) i := by
    intro i
    induction i using Fin.induction with
    | zero => rfl
    | succ t ih =>
      rw [hr t, ih, Fin.val_succ, iterRounds]
      congr 1
      exact Fin.ext (Nat.mod_eq_of_lt t.isLt).symm
  exact key (Fin.last 24)

/-- The input states of the permutations of a trace. -/
def startOf (sh : Shape np a) (states : Fin (24 * np + 1 + a) → State K) (p : Fin np) : State K :=
  states (startState sh p)

/-- The output states of the permutations of a trace. -/
def endOf (states : Fin (24 * np + 1 + a) → State K) (p : Fin np) : State K :=
  states (endState p)

/-- **The batch relation** on the permutations' inputs `start` and outputs `fin`: every output
is Keccak-f of its input, and an unhooked permutation's input is the previous output. -/
structure Holds (sh : Shape np a) (start fin : Fin np → State K) : Prop where
  perm : ∀ p, fin p = keccakF (start p)
  chain : ∀ (p : ℕ) (hp : p + 1 < np), ¬ sh.Hooked ⟨p + 1, hp⟩ →
    start ⟨p + 1, hp⟩ = fin ⟨p, by omega⟩

/-- **The round relations give the batch relation.** On a Boolean trace, the round relations
along `stateMap sh` make every output Keccak-f of its input; the chaining is the shared state
index (`startState_succ`). -/
theorem holds_of_rounds [DecidableEq K] [CharP K 2] {sh : Shape np a}
    {states : Fin (24 * np + 1 + a) → State K} (hbool : ∀ t x y, AllBool (states t x y))
    (h : (stateMap sh).Rounds roundIndex states) : Holds sh (startOf sh states) (endOf states) where
  perm p := by
    have hl := PermRelation.last_eq (permRelation_block h p) (by rw [block_zero]; exact hbool _)
    rwa [block_last, block_zero] at hl
  chain p hp hh := congrArg states (startState_succ sh hp hh)

end Relation

/-! ### The honest trace -/

section Trace

variable {K : Type*} [Field K] (sh : Shape np a)

/-- **The honest trace** of permutation inputs `starts` (`KeccakSkipTrace::generate`,
`keccak_skip_link.h` at `e5daf0a`): state `0` is `starts 0`, state `24 p + i` for `1 ≤ i ≤ 24`
is `i` rounds of `starts p`, and state `24 np + j` is `starts (start j)` (state `0` is the case
`j = 0`). -/
-- spec-side
def trace (starts : Fin np → State K) (t : Fin (24 * np + 1 + a)) : State K :=
  if h : 0 < (t : ℕ) ∧ (t : ℕ) ≤ 24 * np then
    iterRounds (starts ⟨((t : ℕ) - 1) / 24, by omega⟩) (((t : ℕ) - 1) % 24 + 1)
  else starts (sh.start ⟨(t : ℕ) - 24 * np, by have := t.isLt; omega⟩)

/-- The inputs chain: an unhooked permutation's input is Keccak-f of the previous one. -/
def Chained (starts : Fin np → State K) : Prop :=
  ∀ (p : ℕ) (hp : p + 1 < np), ¬ sh.Hooked ⟨p + 1, hp⟩ →
    starts ⟨p + 1, hp⟩ = keccakF (starts ⟨p, by omega⟩)

variable {sh} {starts : Fin np → State K}

theorem trace_round (p : Fin np) (i : ℕ) (hi : i < 24) :
    trace sh starts ⟨24 * p + i + 1, by have := p.isLt; omega⟩ = iterRounds (starts p) (i + 1) := by
  have hp := p.isLt
  rw [trace, dif_pos ⟨by simp only; omega, by simp only; omega⟩]
  congr 2
  · exact Fin.ext (by simp only; omega)
  · simp only; omega

theorem trace_endState (p : Fin np) : trace sh starts (endState p) = keccakF (starts p) := by
  have e : (endState p : Fin (24 * np + 1 + a)) = ⟨24 * p + 23 + 1, by have := p.isLt; omega⟩ :=
    Fin.ext (by simp only [endState]; ring)
  rw [e, trace_round p 23 (by omega)]
  rfl

theorem trace_startState (hc : Chained sh starts) (p : Fin np) :
    trace sh starts (startState sh p) = starts p := by
  obtain ⟨pv, hp⟩ := p
  by_cases h : sh.Hooked ⟨pv, hp⟩ ∧ pv ≠ 0
  · have hj := sh.hookIdx_pos h.1 h.2
    have hjl := (sh.hookIdx h.1).isLt
    rw [startState_of_hooked sh h.1 h.2, trace, dif_neg (by simp only; omega)]
    have e : (⟨24 * np + (sh.hookIdx h.1 : ℕ) - 24 * np, by omega⟩ : Fin (a + 1)) = sh.hookIdx h.1 :=
      Fin.ext (by simp only; omega)
    rw [e, sh.start_hookIdx]
  · rw [startState_of_not_hooked sh h]
    cases pv with
    | zero =>
      rw [trace, dif_neg (by simp only; omega)]
      exact congrArg starts (Fin.ext (by simp only [Nat.mul_zero, Nat.zero_sub]; exact sh.start_zero))
    | succ q =>
      have hnh : ¬ sh.Hooked ⟨q + 1, hp⟩ := fun hh => h ⟨hh, by omega⟩
      have e : (⟨24 * (q + 1), by omega⟩ : Fin (24 * np + 1 + a)) =
          ⟨24 * (⟨q, by omega⟩ : Fin np) + 23 + 1, by omega⟩ := Fin.ext (by simp only; omega)
      rw [e, trace_round _ 23 (by omega), hc q hp hnh]
      rfl

/-- The honest trace of Boolean inputs is Boolean. -/
theorem trace_allBool [DecidableEq K] (hs : ∀ p x y, AllBool (starts p x y))
    (t : Fin (24 * np + 1 + a)) (x y : Fin 5) : AllBool (trace sh starts t x y) := by
  unfold trace
  split_ifs
  · exact iterRounds_allBool (hs _) _ x y
  · exact hs _ x y

/-- **The honest trace satisfies the round relations** along `stateMap sh`, on Boolean chained
inputs. -/
theorem trace_rounds [DecidableEq K] [CharP K 2] (hs : ∀ p x y, AllBool (starts p x y))
    (hc : Chained sh starts) : (stateMap sh).Rounds roundIndex (trace sh starts) := by
  intro t
  have ht := t.isLt
  refine (roundRelation_iff (trace_allBool hs _)).mpr ?_
  have hinp : trace sh starts ((stateMap sh).inp t) =
      iterRounds (starts ⟨(t : ℕ) / 24, by omega⟩) ((t : ℕ) % 24) := by
    simp only [stateMap]
    by_cases h0 : (t : ℕ) % 24 = 0
    · rw [if_pos h0, trace_startState hc, h0]
      rfl
    · rw [if_neg h0]
      have e : (⟨t, by omega⟩ : Fin (24 * np + 1 + a)) =
          ⟨24 * (⟨(t : ℕ) / 24, by omega⟩ : Fin np) + ((t : ℕ) % 24 - 1) + 1, by omega⟩ :=
        Fin.ext (by simp only; omega)
      rw [e, trace_round _ _ (by omega), show (t : ℕ) % 24 - 1 + 1 = (t : ℕ) % 24 by omega]
  have hout : trace sh starts ((stateMap sh).out t) =
      iterRounds (starts ⟨(t : ℕ) / 24, by omega⟩) ((t : ℕ) % 24 + 1) := by
    have e : ((stateMap sh).out t : Fin (24 * np + 1 + a)) =
        ⟨24 * (⟨(t : ℕ) / 24, by omega⟩ : Fin np) + (t : ℕ) % 24 + 1, by omega⟩ :=
      Fin.ext (by simp only [stateMap]; omega)
    rw [e, trace_round _ _ (by omega)]
  rw [hinp, hout, iterRounds]
  congr 1
  exact Fin.ext (by simp only [roundIndex]; omega)

theorem endOf_trace : endOf (trace sh starts) = fun p => keccakF (starts p) :=
  funext trace_endState

end Trace

end GordieHowe.KeccakBatch
