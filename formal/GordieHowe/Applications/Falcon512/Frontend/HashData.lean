-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Keccak.Frontend.Rounds
public import GordieHowe.Applications.Falcon512.Frontend.Basic
public import GordieHowe.Generated.Falcon512.Native.ROMParams.Program

@[expose] public section

/-!
# GordieHowe frontend: native Falcon, the Keccak trace's data

The round table of a native Falcon program's `h2p.shake` (`roundPred`, `outVal`, `linRef`,
`roundSrc`, `rcLeaf`), the index maps of the linear part (`keccakMaps`, the maps of `Falcon512.Native.ROMParams`,
which every native Falcon program shares), and the program facts decided over its tables
(`FalconHHashData`: the `264` rounds' shapes and the constant states), each program instantiating
them by `decide` (a few minutes).
-/

namespace GordieHowe.Falcon512

open Generated.Falcon512.Native.ROMParams.Program hiding program
open GordieHowe.Bits GordieHowe.Keccak GordieHowe.KeccakTrace

/-- **The predicate of round `t` of permutation `p`**: the absorb permutation's rounds
`h2p.shake.blocks.r0 … r23` are predicates `0 … 23`, the squeezes' `h2p.shake.squeeze.r0 … r239`
predicates `30 … 269`. -/
def roundPred (p : Fin 11) (t : Fin 24) : ℕ := if (p : ℕ) = 0 then t else 30 + 24 * (p - 1) + t

/-- **The output value of round `t` of permutation `p`**: `49 + 2 t` for the absorb permutation;
for squeeze round `s = 24 (p − 1) + t`, `99 + 2 s` plus one for each output view (`out.p1`, …)
before it. -/
def outVal (p t : ℕ) : ℕ :=
  if p = 0 then 49 + 2 * t else 99 + 2 * (24 * (p - 1) + t) + (24 * (p - 1) + t) / 24

/-- **The shared expression of round `t`'s linear part.** -/
def linRef (p : Fin 11) (t : Fin 24) : ℕ :=
  if (p : ℕ) = 0 then 4 + 2 * t else 58 + 2 * (24 * (p - 1) + t)

/-- **State `t` of permutation `p`**: the input of round `t` (`t < 24`), the output of round
`t − 1` (`t ≥ 1`). The absorb permutation reads the absorbed block (`ref 2`), the first squeeze
`h2p.shake.state` (`ref 56`), every other squeeze the previous permutation's output. -/
def roundSrc (p : Fin 11) (t : Fin 25) : RealizedProgram.StateSrc :=
  if (t : ℕ) = 0 then
    (if (p : ℕ) = 0 then .ref 2 else if (p : ℕ) = 1 then .ref 56 else .leaf (outVal (p - 1) 23))
  else .leaf (outVal p (t - 1))

/-- **The identifier round `t` of permutation `p` reads its state from.** -/
def roundSrcId (p : Fin 11) (t : Fin 24) : ℕ :=
  match roundSrc p t.castSucc with
  | .leaf v => v
  | .ref k => k

/-- **Whether round `t` of permutation `p` reads its state from a shared expression.** -/
def roundSrcIsRef (p : Fin 11) (t : Fin 24) : Bool :=
  match roundSrc p t.castSucc with
  | .leaf _ => false
  | .ref _ => true

/-- A round reading a shared expression reads the identified one. -/
theorem roundSrc_of_isRef {p : Fin 11} {t : Fin 24} (h : roundSrcIsRef p t = true) :
    roundSrc p t.castSucc = .ref (roundSrcId p t) := by
  unfold roundSrcIsRef at h
  unfold roundSrcId
  split at h <;> simp_all

/-- A round reading a value reads the identified one. -/
theorem roundSrc_of_not_isRef {p : Fin 11} {t : Fin 24} (h : roundSrcIsRef p t = false) :
    roundSrc p t.castSucc = .leaf (roundSrcId p t) := by
  unfold roundSrcIsRef at h
  unfold roundSrcId
  split at h <;> simp_all

/-- **The value of round `t`'s constant** (`h2p.shake`'s `ι` states). -/
def rcLeaf (t : Fin 24) : ℕ :=
  [2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 9, 23, 8, 24].getD t 0

/-- **The view the stream reads its samples' block `k` from**: `h2p.shake.state` for the first
block, the output views `h2p.shake.out.p1 … p10` for the others. -/
def viewVal (k : ℕ) : ℕ := if k = 0 then 97 else outVal k 23 + 1

/-- **The zero slot of view `k`**: its size, where the stream's maps send the other blocks'
samples. -/
def zslot (k : ℕ) : ℕ := if k = 0 then 1600 else if k = 10 then 592 else 1088

/-- **The row of round `t` of permutation `p`** in the rounds' shape families: the predicate, the
output, the linear part, the all-ones state, the round constant, the zero state, the source, the
column parities and the committed words. -/
def roundRow (p : Fin 11) (t : Fin 24) : List ℕ :=
  [roundPred p t, outVal p t, linRef p t, 1, rcLeaf t, 3, roundSrcId p t, linRef p t - 1,
    outVal p t - 1]

/-- **The index maps of the linear part** (`KeccakMaps`), by `decide` (about a minute). -/
theorem keccakMaps : RealizedProgram.KeccakMaps idx6 idx7 idx8 idx9 idx10 idx11 idx12 idx13 := by
  decide +kernel

/-- **The program facts of `h2p.shake` decided over the tables** (each program instantiates them by
`decide`): the `264` rounds' shapes, the rounds' predicates, expressions and outputs, the constant
states. -/
class FalconHHashData (program : RealizedProgram) : Prop where
  /-- **The shapes of the `264` rounds** (generated data: reading predicate `269` of the table
unfolds `List.getD` that deep). -/
  roundShapes : ∀ p : Fin 11, ∀ t : Fin 24,
      (program.predicate (roundPred p t)).body.roundShape? =
          some ⟨0, outVal p t, linRef p t, rcLeaf t, 1, 3, idx12, idx13⟩ ∧
        (program.expr (linRef p t)).linShape? =
          some ⟨roundSrc p t.castSucc, linRef p t - 1, idx7, idx8, idx9, idx10, idx11⟩ ∧
        (program.expr (linRef p t - 1)).colShape? = some (roundSrc p t.castSucc, idx6)
  /-- The rounds are source predicates below the table's length, their shared expressions below
the expressions' length, their outputs of `1600` coordinates. -/
  round_facts : ∀ p : Fin 11, ∀ t : Fin 24,
      roundPred p t < program.predicates.length ∧
        program.inSource (program.predicate (roundPred p t)) = true ∧
        linRef p t < program.exprs.length ∧ linRef p t - 1 < program.exprs.length ∧
        1600 ≤ (program.value (outVal p t)).size
  /-- The constant states: all ones (`const2`), all zeros (`const4`). -/
  const_states : program.constEntries 1 = List.replicate 1600 1 ∧
      program.constEntries 3 = List.replicate 1600 0 ∧ program.isConstant 1 = true ∧
      program.isConstant 3 = true ∧ program.valueField 1 = 0 ∧ program.valueField 3 = 0
  /-- The round constants' states: the bits of `rc t` in lane `(0, 0)`. -/
  const_rc : ∀ t : Fin 24, program.constEntries (rcLeaf t) =
        List.ofFn (fun j : Fin 1600 => if (j : ℕ) < 64 ∧ (rc t).testBit j then 1 else 0) ∧
      program.isConstant (rcLeaf t) = true ∧ program.valueField (rcLeaf t) = 0

end GordieHowe.Falcon512
