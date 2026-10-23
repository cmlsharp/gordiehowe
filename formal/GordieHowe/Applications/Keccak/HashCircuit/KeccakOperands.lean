-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.ToMathlib.LagrangeEval
public import GordieHowe.Applications.Keccak.Gadgets.Trace
public import GordieHowe.Applications.Keccak.HashCircuit.Packed.Opening

@[expose] public section

/-!
# The Keccak operand map (batched-Keccak alternative)

This file defines the Keccak operand map `keccakOperands m` over a state map `m`
(`KeccakTrace.StateMap`: round `t` relates state `m.inp t` to state `m.out t`), the affine map
from the committed packed bits to the skip's operand arrays, and shows that the skip relation on
it is the round relation along `m` (`holds_iff`). A batch of Keccak-f chains is
`KeccakBatch.stateMap sh`.

Source: `lib/sumcheck/keccak_skip_link.h` and `lib/sumcheck/keccak_skip_circuit_link.h` on
main; `KeccakSkipCircuitLink::constraints` calls `skip.prove(trace->operands(), …)`.

* Committed words (`Forms`, `keccak_skip_link.h` lines 106-110, 143-144). `S · 100` words of
  sixteen lane bits: state `t`, lane `(x, y)`, chunk `c` is word
  `t · 100 + (5x + y) · 4 + c` (`wordIdx`), lane bit `16c + j` its bit `j` (`stateOf`).
* Operand groups (`KeccakSkipTrace::operands`, `keccak_skip_link.h` lines 80-96; `boolean_skip.h`).
  `KeccakSkipTrace::operands` lists round `t`'s 25 lanes as word `t · 25 + 5x + y`, with
  `a = ~B[x+1][y]`, `b = B[x+2][y]`, `c = state[t][x][y] ^ B[x][y] ^ iota`; `split` cuts word `W`
  into groups `W · (64 / w) + chunk`, chunk `c` holding bits `c·w … c·w + w − 1`; `prove` pads the
  group list with `Word{}` to a power of two (`boolean_skip.h` lines 97-102). Here `w = 16`
  (`64 / w = 4`), so bit `z` of round `t`, lane `(x, y)` is at group
  `(t · 25 + 5x + y) · 4 + z / 16`, position `z mod 16` (`groupOf`, `place`), and the three operands
  are `opA`, `opB`, `opC` of `KeccakTrace` on states `m.inp t` and `m.out t` (`opVals`), the C++'s
  `input_state(t)` and `state[t]` (`KeccakSkipTrace::operands`). The padding is data: groups not of
  the form `groupOf t i` carry zero operands (`keccakOperands_apply_pad`). The width is fixed: group
  and position arithmetic uses `w = 16` literally.
-/

namespace GordieHowe.HashCircuit.KeccakOperands
open IOP

open GordieHowe.Bits GordieHowe.Keccak GordieHowe.KeccakTrace GordieHowe.PackedClaim Sumcheck.UnivariateSkip Packed.Opening Matrix

variable {K : Type} [Field K] {rounds S n : ℕ}

theorem fin16_lt (j : Fin (2 ^ 4)) : (j : ℕ) < 16 := j.isLt

/-! ## Committed words and states -/

/-- The committed word index type of `S` states: `S · 100` words. -/
abbrev Word (S : ℕ) := Fin (S * 100)

/-- The committed word of state `t`, lane `(x, y)`, chunk `c`:
`t · 100 + (5x + y) · 4 + c`. -/
def wordIdx (t : Fin S) (x y : Fin 5) (c : Fin 4) : Word S :=
  ⟨t * 100 + (5 * x + y) * 4 + c, by
    have := t.isLt; have := x.isLt; have := y.isLt; have := c.isLt; omega⟩

/-- State `t` of the committed bits `v`: bit `z` of lane `(x, y)` is bit `z mod 16` of
word `wordIdx t x y (z / 16)`. -/
def stateOf (v : Word S → Fin (2 ^ 4) → K) (t : Fin S) : State K :=
  fun x y z => v (wordIdx t x y ⟨z / 16, by have := z.isLt; omega⟩)
    ⟨z % 16, by show _ < 16; omega⟩

/-- The 100 committed words of state `t`. -/
def stateWords (words : Word S → K) (t : Fin S) : Fin 5 → Fin 5 → Fin 4 → K :=
  fun x y c => words (wordIdx t x y c)

theorem stateOf_add (v v' : Word S → Fin (2 ^ 4) → K) (t : Fin S) :
    stateOf (v + v') t = stateOf v t + stateOf v' t := rfl

theorem stateOf_smul (e : K) (v : Word S → Fin (2 ^ 4) → K) (t : Fin S) :
    stateOf (e • v) t = e • stateOf v t := rfl

/-! ## The operand map -/

variable (m : StateMap rounds S)

/-- The C++ round constant index of round `t`, `t mod 24` (`keccak_skip_link.h` line 93). -/
def cppRound (t : Fin rounds) : Fin 24 := ⟨t % 24, Nat.mod_lt _ (by decide)⟩

/-- The operand group of round `t`, lane `(x, y)`, bit `z`: `word · (64 / w) + z / w`
with `w = 16` and `word = t · 25 + 5x + y`. -/
def groupOf (t : Fin rounds) (i : Idx) : ℕ := ((t : ℕ) * 25 + 5 * (i.1 : ℕ) + i.2.1) * 4 + i.2.2 / 16

theorem groupOf_lt (t : Fin rounds) (i : Idx) : groupOf t i < rounds * 100 := by
  have := t.isLt; have := i.1.isLt; have := i.2.1.isLt; have := i.2.2.isLt
  simp only [groupOf]
  omega

theorem groupOf_inj {t t' : Fin rounds} {i i' : Idx} (h : groupOf t i = groupOf t' i')
    (hz : (i.2.2 : ℕ) % 16 = i'.2.2 % 16) : t = t' ∧ i = i' := by
  have := i.1.isLt; have := i.2.1.isLt; have := i.2.2.isLt
  have := i'.1.isLt; have := i'.2.1.isLt; have := i'.2.2.isLt
  simp only [groupOf] at h
  refine ⟨Fin.ext (by omega), Prod.ext (Fin.ext (by omega)) (Prod.ext (Fin.ext (by omega))
    (Fin.ext (by omega)))⟩

/-- Per-round bit values `A t i` placed into the padded group arrays: bit `i = (x, y, z)`
of round `t` at group `groupOf t i`, position `z mod 16`; every other entry is zero. -/
def place (A : Fin rounds → Idx → K) (g : Fin (2 ^ n)) (p : Fin 16) : K :=
  ∑ t, ∑ i : Idx, if (g : ℕ) = groupOf t i ∧ (p : ℕ) = i.2.2 % 16 then A t i else 0

theorem place_apply_groupOf (A : Fin rounds → Idx → K) {t : Fin rounds} {i : Idx}
    {g : Fin (2 ^ n)} {p : Fin 16} (hg : (g : ℕ) = groupOf t i) (hp : (p : ℕ) = i.2.2 % 16) :
    place A g p = A t i := by
  rw [place, Finset.sum_eq_single t, Finset.sum_eq_single i, ite_eq_left ⟨hg, hp⟩]
  · intro i' _ hi'
    rw [ite_eq_right]
    rintro ⟨h1, h2⟩
    exact hi' (groupOf_inj (h1.symm.trans hg) (h2.symm.trans hp)).2
  · simp
  · intro t' _ ht'
    refine Finset.sum_eq_zero fun i' _ => ite_eq_right ?_
    rintro ⟨h1, h2⟩
    exact ht' (groupOf_inj (h1.symm.trans hg) (h2.symm.trans hp)).1
  · simp

theorem place_eq_zero (A : Fin rounds → Idx → K) {g : Fin (2 ^ n)} {p : Fin 16}
    (h : ∀ (t : Fin rounds) (i : Idx), ¬((g : ℕ) = groupOf t i ∧ (p : ℕ) = i.2.2 % 16)) : place A g p = 0 :=
  Finset.sum_eq_zero fun t _ => Finset.sum_eq_zero fun i _ => ite_eq_right (h t i)

theorem place_add (A A' : Fin rounds → Idx → K) :
    place (n := n) (A + A') = place A + place A' := by
  funext g p
  simp only [place, Pi.add_apply, ite_add_zero, Finset.sum_add_distrib]

theorem place_smul (e : K) (A : Fin rounds → Idx → K) :
    place (n := n) (e • A) = e • place A := by
  funext g p
  simp only [place, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_ite, mul_zero]

/-- The operands of round `t` at bit `i` (`keccak_skip_link.h` lines 89-93): `opA`, `opB`
and `opC` of `KeccakTrace` on states `t` and `t + 1`. -/
def opVals (v : Word S → Fin (2 ^ 4) → K) : Fin 3 → Fin rounds → Idx → K :=
  ![fun t => opA (flat (stateOf v (m.inp t))), fun t => opB (flat (stateOf v (m.inp t))),
    fun t => opC (cppRound t) (flat (stateOf v (m.inp t))) (flat (stateOf v (m.out t)))]

/-- The linear part of `opVals`: the operands without the `NOT` and `iota` constants. -/
def linVals (v : Word S → Fin (2 ^ 4) → K) : Fin 3 → Fin rounds → Idx → K :=
  ![fun t => shiftMat 1 *ᵥ linB (flat (stateOf v (m.inp t))),
    fun t => shiftMat 2 *ᵥ linB (flat (stateOf v (m.inp t))),
    fun t => flat (stateOf v (m.out t)) + linB (flat (stateOf v (m.inp t)))]

theorem linVals_add (v v' : Word S → Fin (2 ^ 4) → K) (o : Fin 3) :
    linVals m (v + v') o = linVals m v o + linVals m v' o := by
  funext t
  fin_cases o <;>
    simp [linVals, stateOf_add, flat_add, linB_add, Matrix.mulVec_add, add_add_add_comm]

theorem linVals_smul (e : K) (v : Word S → Fin (2 ^ 4) → K) (o : Fin 3) :
    linVals m (e • v) o = e • linVals m v o := by
  funext t
  fin_cases o <;> simp [linVals, stateOf_smul, flat_smul, linB_smul, Matrix.mulVec_smul, smul_add]

theorem opVals_add (v v' : Word S → Fin (2 ^ 4) → K) (o : Fin 3) :
    opVals m (v' + v) o = linVals m v' o + opVals m v o := by
  funext t i
  fin_cases o <;>
    simp [opVals, linVals, opA, opB, opC, stateOf_add, flat_add, linB_add, Matrix.mulVec_add] <;>
    ring

/-- The linear part of `keccakOperands`. -/
def keccakLinear :
    (Word S → Fin (2 ^ 4) → K) →ₗ[K] (Fin 3 → Fin (2 ^ n) → Fin 16 → K) where
  toFun v o := place (linVals m v o)
  map_add' v v' := by
    funext o
    simp only [linVals_add, place_add, Pi.add_apply]
  map_smul' e v := by
    funext o
    simp only [linVals_smul, place_smul, Pi.smul_apply, RingHom.id_apply]

/-- **The Keccak operand map.** The committed bits `v` (word `wordIdx t x y c`, bit `j`
is bit `16c + j` of lane `(x, y)` of state `t`) go to the operand arrays: operand `o`
of group `g`, position `p` is `opVals m v o t i` if `(g, p) = (groupOf t i, z mod 16)`,
and `0` otherwise. -/
def keccakOperands :
    (Word S → Fin (2 ^ 4) → K) →ᵃ[K] (Fin 3 → Fin (2 ^ n) → Fin 16 → K) where
  toFun v o := place (opVals m v o)
  linear := keccakLinear m
  map_vadd' v v' := by
    funext o
    simp only [vadd_eq_add, Pi.add_apply, opVals_add, place_add]
    rfl

/-- **Placement.** At group `word · 4 + z / 16`, `word = t · 25 + 5x + y`, position
`z mod 16`, operand `o` is `opA`, `opB` or `opC` of states `t`, `t + 1` at `(x, y, z)`. -/
theorem keccakOperands_apply_groupOf (v : Word S → Fin (2 ^ 4) → K) (o : Fin 3)
    {t : Fin rounds} {i : Idx} {g : Fin (2 ^ n)} {p : Fin 16} (hg : (g : ℕ) = groupOf t i)
    (hp : (p : ℕ) = i.2.2 % 16) :
    keccakOperands (K := K) (n := n) m v o g p = opVals m v o t i :=
  place_apply_groupOf _ hg hp

/-- **Padding.** Entries not of the form `(groupOf t i, z mod 16)`, in particular every
group from `rounds · 100` on, are zero. -/
theorem keccakOperands_apply_pad (v : Word S → Fin (2 ^ 4) → K) (o : Fin 3)
    {g : Fin (2 ^ n)} {p : Fin 16} (h : ∀ (t : Fin rounds) (i : Idx), ¬((g : ℕ) = groupOf t i ∧ (p : ℕ) = i.2.2 % 16)) :
    keccakOperands (K := K) (n := n) m v o g p = 0 :=
  place_eq_zero _ h

/-! ## The skip relation is the round relation -/

/-- **The skip relation is the trace's round relations.** For groups fitting the domain
(`hn`, a parameter condition), all `A · B + C = 0` hold for `keccakOperands v` exactly when the
states of `v` satisfy the round relations `RoundRelation (t mod 24)` for every round.
No hypothesis on `v`: the padding groups hold identically. -/
theorem holds_iff (hn : rounds * 100 ≤ 2 ^ n) (v : Word S → Fin (2 ^ 4) → K) :
    (toOperands (keccakOperands (K := K) (n := n) m v)).Holds ↔ m.Rounds cppRound (stateOf v) := by
  constructor
  · intro h t i
    have hr := h ⟨groupOf t i, (groupOf_lt t i).trans_le hn⟩ ⟨i.2.2 % 16, by omega⟩
    have e := fun o => keccakOperands_apply_groupOf (K := K) (n := n) m v o (t := t) (i := i)
      (g := ⟨groupOf t i, (groupOf_lt t i).trans_le hn⟩) (p := ⟨i.2.2 % 16, by omega⟩) rfl rfl
    simp only [Operands.residual, toOperands, e] at hr
    exact hr
  · intro h g p
    by_cases hc : ∃ (t : Fin rounds) (i : Idx), (g : ℕ) = groupOf t i ∧ (p : ℕ) = i.2.2 % 16
    · obtain ⟨t, i, hg, hp⟩ := hc
      simp only [Operands.residual, toOperands, keccakOperands_apply_groupOf m v _ hg hp]
      exact h t i
    · have hc' : ∀ (t : Fin rounds) (i : Idx), ¬((g : ℕ) = groupOf t i ∧ (p : ℕ) = i.2.2 % 16) :=
        fun t i h' => hc ⟨t, i, h'⟩
      simp only [Operands.residual, toOperands, keccakOperands_apply_pad m v _ hc', mul_zero,
        add_zero]

end GordieHowe.HashCircuit.KeccakOperands
