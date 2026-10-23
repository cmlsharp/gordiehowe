-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Library.Keccak
public import GordieHowe.Applications.MLDSA44.Native.ROMParams.Frontend.Basic

@[expose] public section

/-!
# GordieHowe frontend: `MLDSA44.Native.ROMParams`, the Keccak trace's data

The facts about the program's three SHAKE256 calls of domain `H` that are decided over its tables,
separated from the proofs (`GordieHowe/Applications/MLDSA44/Native/ROMParams/Frontend/Hash.lean`) because deciding them takes a few
minutes. The trace has ten Keccak-f permutations (`240` round predicates): permutation `0` is `μ`'s
absorb (`h2c.mu.blocks.r0 … r23`, predicates `18 … 41`), permutations `1 … 7` are `c̃'`'s seven
absorbs (`h2c.c_tilde.r0 … r167`, predicates `48 … 215`), permutations `8` and `9` the
SampleInBall stream's absorb and squeeze (`h2c.sib.r0 … r47`, predicates `216 … 263`). The file
holds the round table (`roundPred`, `outVal`, `linRef`, `roundSrc`, `rcLeaf`), the index maps of
the linear part (`keccakMaps`), the rounds' shapes (`roundShapes`) and the constant states.
-/

namespace GordieHowe.MLDSA44.Native.ROMParams

open Generated.MLDSA44.Native.ROMParams.Program
open GordieHowe.Bits GordieHowe.Keccak GordieHowe.KeccakTrace

/-- **The predicate of round `t` of permutation `p`**: `18 + t` for `μ`'s absorb, `48 + 24 (p − 1)
+ t` for the later ones (`c̃'`'s rounds, then the stream's). -/
def roundPred (p : Fin 10) (t : Fin 24) : ℕ := if (p : ℕ) = 0 then 18 + t else 48 + 24 * (p - 1) + t

theorem roundPred_ge (p : Fin 10) (t : Fin 24) : 18 ≤ roundPred p t := by
  unfold roundPred
  split <;> omega

theorem roundPred_le (p : Fin 10) (t : Fin 24) : roundPred p t ≤ 270 := by
  unfold roundPred
  have := p.isLt
  have := t.isLt
  split <;> omega

/-- **The output value of round `t` of permutation `p`**: `73 + 2 t` for `μ`'s absorb; for round
`s = 24 (p − 1) + t` of the later ones `123 + 2 s`, plus one past `c̃'`'s output view (the
stream's rounds). -/
def outVal (p t : ℕ) : ℕ :=
  if p = 0 then 73 + 2 * t else 123 + 2 * (24 * (p - 1) + t) + (if 8 ≤ p then 1 else 0)

/-- **The shared expression of round `t`'s linear part**: `14 + 2 t` for `μ`'s absorb; `69 + 2 s +
(p − 1)` for round `s = 24 (p − 1) + t` of the later ones (each permutation after the first of a
call reads one more shared expression, its input). -/
def linRef (p : Fin 10) (t : Fin 24) : ℕ :=
  if (p : ℕ) = 0 then 14 + 2 * t else 69 + 2 * (24 * (p - 1) + t) + (p - 1)

/-- **State `t` of permutation `p`**: the input of round `t` (`t < 24`), the output of round
`t − 1` (`t ≥ 1`). Every permutation reads its input from the shared expression two before its
first linear part (`ref 12`, `67`, `116`, …, `410`, `459`). -/
def roundSrc (p : Fin 10) (t : Fin 25) : RealizedProgram.StateSrc :=
  if (t : ℕ) = 0 then .ref (linRef p 0 - 2) else .leaf (outVal p (t - 1))

/-- **The value of round `t`'s constant** (the `ι` states). -/
def rcLeaf (t : Fin 24) : ℕ :=
  [12, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 19, 33, 18,
    34].getD t 0

/-- **The index maps of the linear part** (`KeccakMaps`), by `decide`. -/
theorem keccakMaps : RealizedProgram.KeccakMaps idx18 idx19 idx20 idx21 idx22 idx23 idx24 idx25 := by
  decide +kernel

/-- **The program facts of domain `H`'s Keccak trace** (`MldsaHBase` and): the shapes of the `240` rounds (with the index maps of the program at the ROM parameters), their table facts, and the constant states. Each program instantiates it by `decide`. -/
class MldsaHHashData (program : RealizedProgram) : Prop extends MldsaHBase program where
  /-- **The shapes of the `240` rounds** (generated data: reading predicate `263` of the table
  unfolds `List.getD` that deep). -/
  roundShapes : ∀ p : Fin 10, ∀ t : Fin 24, (program.predicate (roundPred p t)).body.roundShape? = some ⟨1, outVal p t, linRef p t, rcLeaf t, 11, 13, idx24, idx25⟩ ∧ (program.expr (linRef p t)).linShape? = some ⟨roundSrc p t.castSucc, linRef p t - 1, idx19, idx20, idx21, idx22, idx23⟩ ∧ (program.expr (linRef p t - 1)).colShape? = some (roundSrc p t.castSucc, idx18)
  /-- The rounds are source predicates below the table's length, their shared expressions below
  the expressions' length, their outputs of `1600` coordinates. -/
  round_facts : ∀ p : Fin 10, ∀ t : Fin 24, roundPred p t < program.predicates.length ∧ program.inSource (program.predicate (roundPred p t)) = true ∧ linRef p t < program.exprs.length ∧ linRef p t - 1 < program.exprs.length ∧ 1600 ≤ (program.value (outVal p t)).size
  /-- The constant states: all ones (`const11`), all zeros (`const13`), in domain `H`'s field. -/
  const_states : program.constEntries 11 = List.replicate 1600 1 ∧ program.constEntries 13 = List.replicate 1600 0 ∧ program.isConstant 11 = true ∧ program.isConstant 13 = true ∧ program.valueField 11 = 1 ∧ program.valueField 13 = 1 ∧ program.domainField 1 = 1
  /-- The round constants' states: the bits of `rc t` in lane `(0, 0)`. -/
  const_rc : ∀ t : Fin 24, program.constEntries (rcLeaf t) = List.ofFn (fun j : Fin 1600 => if (j : ℕ) < 64 ∧ (rc t).testBit j then 1 else 0) ∧ program.isConstant (rcLeaf t) = true ∧ program.valueField (rcLeaf t) = 1

set_option maxRecDepth 8192 in
/-- The native program at the ROM parameters has these facts. -/
instance : MldsaHHashData program where
  roundShapes := by
    decide +kernel
  round_facts := by
    decide +kernel
  const_states := by
    decide +kernel
  const_rc := by
    decide +kernel

variable {program : RealizedProgram} [MldsaHHashData program]

/-- **The shapes of the `240` rounds** (generated data: reading predicate `263` of the table
unfolds `List.getD` that deep). -/
theorem roundShapes : ∀ p : Fin 10, ∀ t : Fin 24, (program.predicate (roundPred p t)).body.roundShape? = some ⟨1, outVal p t, linRef p t, rcLeaf t, 11, 13, idx24, idx25⟩ ∧ (program.expr (linRef p t)).linShape? = some ⟨roundSrc p t.castSucc, linRef p t - 1, idx19, idx20, idx21, idx22, idx23⟩ ∧ (program.expr (linRef p t - 1)).colShape? = some (roundSrc p t.castSucc, idx18) :=
  MldsaHHashData.roundShapes
/-- The rounds are source predicates below the table's length, their shared expressions below
the expressions' length, their outputs of `1600` coordinates. -/
theorem round_facts : ∀ p : Fin 10, ∀ t : Fin 24, roundPred p t < program.predicates.length ∧ program.inSource (program.predicate (roundPred p t)) = true ∧ linRef p t < program.exprs.length ∧ linRef p t - 1 < program.exprs.length ∧ 1600 ≤ (program.value (outVal p t)).size :=
  MldsaHHashData.round_facts
/-- The constant states: all ones (`const11`), all zeros (`const13`), in domain `H`'s field. -/
theorem const_states : program.constEntries 11 = List.replicate 1600 1 ∧ program.constEntries 13 = List.replicate 1600 0 ∧ program.isConstant 11 = true ∧ program.isConstant 13 = true ∧ program.valueField 11 = 1 ∧ program.valueField 13 = 1 ∧ program.domainField 1 = 1 :=
  MldsaHHashData.const_states
/-- The round constants' states: the bits of `rc t` in lane `(0, 0)`. -/
theorem const_rc : ∀ t : Fin 24, program.constEntries (rcLeaf t) = List.ofFn (fun j : Fin 1600 => if (j : ℕ) < 64 ∧ (rc t).testBit j then 1 else 0) ∧ program.isConstant (rcLeaf t) = true ∧ program.valueField (rcLeaf t) = 1 :=
  MldsaHHashData.const_rc
end GordieHowe.MLDSA44.Native.ROMParams
