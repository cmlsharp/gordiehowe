-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Keccak.Frontend.Rounds
public import GordieHoweCerts.Applications.MLDSA44.Frontend.Basic

@[expose] public section

/-!
# GordieHowe frontend: `MLDSA44.Native.ROMParams`, the Keccak trace's data

The facts about the program's three SHAKE256 calls of domain `H` that are decided over its tables,
separated from the proofs (`GordieHoweCerts/Applications/MLDSA44/Frontend/Hash.lean`) because deciding them takes a few
minutes. The trace has ten Keccak-f permutations (`240` round predicates): permutation `0` is `μ`'s
absorb (`h2c.mu.blocks.r0 … r23`, predicates `18 … 41`), permutations `1 … 7` are `c̃'`'s seven
absorbs (`h2c.c_tilde.r0 … r167`, predicates `48 … 215`), permutations `8` and `9` the
SampleInBall stream's absorb and squeeze (`h2c.sib.r0 … r47`, predicates `216 … 263`). The file
holds the round table (`roundPred`, `outVal`, `linRef`, `roundSrc`, `rcLeaf`), the index maps of
the linear part (`keccakMaps`), the rounds' shapes (`roundShapes`) and the constant states. The
program facts of permutations `1 … 9` alone (`MldsaHHashDataCore`, `roundShapes_core`) are those of
domain `H`'s core, which a program without `μ`'s call holds.
-/

namespace GordieHowe.MLDSA44

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

/-- The rounds of permutations `1 … 9` are domain `H`'s core predicates (`48 … 263`). -/
theorem roundPred_ge_core (p : Fin 10) (hp : (p : ℕ) ≠ 0) (t : Fin 24) : 48 ≤ roundPred p t := by
  unfold roundPred
  rw [if_neg hp]
  omega

/-- The rounds of permutation `0` are `μ`'s predicates (`18 … 41`). -/
theorem roundPred_le_mu (t : Fin 24) : roundPred 0 t ≤ 47 := by
  unfold roundPred
  have := t.isLt
  simp only [Fin.val_zero, if_true]
  omega

/-- **The output value of round `t` of permutation `p`**: `72 + 2 t` for `μ`'s absorb; for round
`s = 24 (p − 1) + t` of the later ones `122 + 2 s`, plus one past `c̃'`'s output view (the
stream's rounds). -/
def outVal (p t : ℕ) : ℕ :=
  if p = 0 then 72 + 2 * t else 122 + 2 * (24 * (p - 1) + t) + (if 8 ≤ p then 1 else 0)

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
  [11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 18, 32, 17,
    33].getD t 0

/-- **The index maps of the linear part** (`KeccakMaps`), by `decide`. -/
theorem keccakMaps : RealizedProgram.KeccakMaps idx17 idx18 idx19 idx20 idx21 idx22 idx23 idx24 := by
  decide +kernel

/-- **The program facts of domain `H`'s Keccak trace** (`MldsaHBase` and): the shapes of the `240` rounds (with the index maps of the program at the ROM parameters), their table facts, and the constant states. Each program instantiates it by `decide`. -/
class MldsaHHashData (program : RealizedProgram) : Prop extends MldsaHBase program where
  /-- **The shapes of the `240` rounds** (generated data: reading predicate `263` of the table
  unfolds `List.getD` that deep). -/
  roundShapes : ∀ p : Fin 10, ∀ t : Fin 24, (program.predicate (roundPred p t)).body.roundShape? = some ⟨1, outVal p t, linRef p t, rcLeaf t, 10, 12, idx23, idx24⟩ ∧ (program.expr (linRef p t)).linShape? = some ⟨roundSrc p t.castSucc, linRef p t - 1, idx18, idx19, idx20, idx21, idx22⟩ ∧ (program.expr (linRef p t - 1)).colShape? = some (roundSrc p t.castSucc, idx17)
  /-- The rounds are source predicates below the table's length, their shared expressions below
  the expressions' length, their outputs of `1600` coordinates. -/
  round_facts : ∀ p : Fin 10, ∀ t : Fin 24, roundPred p t < program.predicates.length ∧ program.inSource (program.predicate (roundPred p t)) = true ∧ linRef p t < program.exprs.length ∧ linRef p t - 1 < program.exprs.length ∧ 1600 ≤ (program.value (outVal p t)).size
  /-- The constant states: all ones (`const10`), all zeros (`const12`), in domain `H`'s field. -/
  const_states : program.constEntries 10 = List.replicate 1600 1 ∧ program.constEntries 12 = List.replicate 1600 0 ∧ program.isConstant 10 = true ∧ program.isConstant 12 = true ∧ program.valueField 10 = 1 ∧ program.valueField 12 = 1 ∧ program.domainField 1 = 1
  /-- The round constants' states: the bits of `rc t` in lane `(0, 0)`. -/
  const_rc : ∀ t : Fin 24, program.constEntries (rcLeaf t) = List.ofFn (fun j : Fin 1600 => if (j : ℕ) < 64 ∧ (rc t).testBit j then 1 else 0) ∧ program.isConstant (rcLeaf t) = true ∧ program.valueField (rcLeaf t) = 1

/-- A row of the checked round family has its round's shapes, with the given state source. -/
private theorem round_of_row {r : List ℕ} {src : RealizedProgram.StateSrc}
    (hb : ∃ t, (program.predicate (r.getD 0 0)).body = .equal 1 (.add (.leaf (r.getD 1 0))
      (.add (.add (.ref (r.getD 2 0)) (.mul (.sub (.leaf (r.getD 3 0)) (.reindex idx23
      (.ref (r.getD 2 0)))) (.reindex idx24 (.ref (r.getD 2 0))))) (.leaf (r.getD 4 0))))
      (.leaf (r.getD 5 0)) t)
    (hl : program.expr (r.getD 2 0) = .reindex idx22 (.add (.add src.expr (.reindex idx19
      (.reindex idx18 (.ref (r.getD 7 0))))) (.reindex idx19 (.reindex idx21 (.reindex idx20
      (.ref (r.getD 7 0)))))))
    (hc : program.expr (r.getD 7 0) = .apply (.sum 5) (.reindex idx17 src.expr)) :
    (program.predicate (r.getD 0 0)).body.roundShape? =
        some ⟨1, r.getD 1 0, r.getD 2 0, r.getD 4 0, r.getD 3 0, r.getD 5 0, idx23, idx24⟩ ∧
      (program.expr (r.getD 2 0)).linShape? =
        some ⟨src, r.getD 7 0, idx18, idx19, idx20, idx21, idx22⟩ ∧
      (program.expr (r.getD 7 0)).colShape? = some (src, idx17) := by
  obtain ⟨t, ht⟩ := hb
  exact ⟨RealizedProgram.PredBody.roundShape?_of_eq ht, RealizedProgram.Expr.linShape?_of_eq hl,
    RealizedProgram.Expr.colShape?_of_eq hc⟩

/-- Each round has a row of the checked round family: the first permutation round reads the
permutation's input expression, every later round the previous round's output. -/
private theorem round_rows : ∀ p : Fin 10, ∀ t : Fin 24,
    ((t : ℕ) = 0 → ∃ r ∈ Generated.MLDSA44.Native.ROMParams.Shapes.family_keccak_rounds_0_rows, r.getD 0 0 = roundPred p t ∧
      r.getD 1 0 = outVal p t ∧ r.getD 2 0 = linRef p t ∧ r.getD 3 0 = 10 ∧
      r.getD 4 0 = rcLeaf t ∧ r.getD 5 0 = 12 ∧ r.getD 6 0 = linRef p 0 - 2 ∧
      r.getD 7 0 = linRef p t - 1) ∧
    ((t : ℕ) ≠ 0 → ∃ r ∈ Generated.MLDSA44.Native.ROMParams.Shapes.family_keccak_rounds_1_rows, r.getD 0 0 = roundPred p t ∧
      r.getD 1 0 = outVal p t ∧ r.getD 2 0 = linRef p t ∧ r.getD 3 0 = 10 ∧
      r.getD 4 0 = rcLeaf t ∧ r.getD 5 0 = 12 ∧ r.getD 6 0 = outVal p (t - 1) ∧
      r.getD 7 0 = linRef p t - 1) := by
  decide +kernel

/-- The rounds' checked shapes and table facts. -/
private theorem rounds_checked (p : Fin 10) (t : Fin 24) :
    ((program.predicate (roundPred p t)).body.roundShape? =
        some ⟨1, outVal p t, linRef p t, rcLeaf t, 10, 12, idx23, idx24⟩ ∧
      (program.expr (linRef p t)).linShape? =
        some ⟨roundSrc p t.castSucc, linRef p t - 1, idx18, idx19, idx20, idx21, idx22⟩ ∧
      (program.expr (linRef p t - 1)).colShape? = some (roundSrc p t.castSucc, idx17)) ∧
    (roundPred p t < program.predicates.length ∧
      program.inSource (program.predicate (roundPred p t)) = true ∧
      linRef p t < program.exprs.length ∧ linRef p t - 1 < program.exprs.length ∧
      1600 ≤ (program.value (outVal p t)).size) := by
  by_cases h0 : (t : ℕ) = 0
  · obtain ⟨r, hr, e0, e1, e2, e3, e4, e5, e6, e7⟩ := (round_rows p t).1 h0
    have hsrc : roundSrc p t.castSucc = .ref (r.getD 6 0) := by
      rw [e6]; simp only [roundSrc, Fin.coe_castSucc, h0, ↓reduceIte]
    have hrow := round_of_row (src := .ref (r.getD 6 0)) (Generated.MLDSA44.Native.ROMParams.ShapeFacts.family_keccak_rounds_0_predicate0_body hr)
      (Generated.MLDSA44.Native.ROMParams.ShapeFacts.family_keccak_rounds_0_expr0_eq hr) (Generated.MLDSA44.Native.ROMParams.ShapeFacts.family_keccak_rounds_0_expr1_eq hr)
    have hrole := Generated.MLDSA44.Native.ROMParams.ShapeFacts.family_keccak_rounds_0_predicate0_role hr
    have hhead := Generated.MLDSA44.Native.ROMParams.ShapeFacts.family_keccak_rounds_0_value0_header hr
    rw [e0, e1, e2, e3, e4, e5, e7] at hrow
    rw [e0] at hrole
    rw [e1] at hhead
    rw [hsrc]
    refine ⟨hrow, hrole.1, program.inSource_of_source hrole.2, ?_, ?_, ?_⟩
    · rw [← e2]; exact RealizedProgram.expr_lt_of_ne_default (by
        rw [Generated.MLDSA44.Native.ROMParams.ShapeFacts.family_keccak_rounds_0_expr0_eq hr]; intro h; cases h)
    · rw [← e7]; exact RealizedProgram.expr_lt_of_ne_default (by
        rw [Generated.MLDSA44.Native.ROMParams.ShapeFacts.family_keccak_rounds_0_expr1_eq hr]; intro h; cases h)
    · exact (RealizedProgram.valueShape_size hhead.2).ge
  · obtain ⟨r, hr, e0, e1, e2, e3, e4, e5, e6, e7⟩ := (round_rows p t).2 h0
    have hsrc : roundSrc p t.castSucc = .leaf (r.getD 6 0) := by
      rw [e6]; simp only [roundSrc, Fin.coe_castSucc, h0, if_false]
    have hrow := round_of_row (src := .leaf (r.getD 6 0)) (Generated.MLDSA44.Native.ROMParams.ShapeFacts.family_keccak_rounds_1_predicate0_body hr)
      (Generated.MLDSA44.Native.ROMParams.ShapeFacts.family_keccak_rounds_1_expr0_eq hr) (Generated.MLDSA44.Native.ROMParams.ShapeFacts.family_keccak_rounds_1_expr1_eq hr)
    have hrole := Generated.MLDSA44.Native.ROMParams.ShapeFacts.family_keccak_rounds_1_predicate0_role hr
    have hhead := Generated.MLDSA44.Native.ROMParams.ShapeFacts.family_keccak_rounds_1_value0_header hr
    rw [e0, e1, e2, e3, e4, e5, e7] at hrow
    rw [e0] at hrole
    rw [e1] at hhead
    rw [hsrc]
    refine ⟨hrow, hrole.1, program.inSource_of_source hrole.2, ?_, ?_, ?_⟩
    · rw [← e2]; exact RealizedProgram.expr_lt_of_ne_default (by
        rw [Generated.MLDSA44.Native.ROMParams.ShapeFacts.family_keccak_rounds_1_expr0_eq hr]; intro h; cases h)
    · rw [← e7]; exact RealizedProgram.expr_lt_of_ne_default (by
        rw [Generated.MLDSA44.Native.ROMParams.ShapeFacts.family_keccak_rounds_1_expr1_eq hr]; intro h; cases h)
    · exact (RealizedProgram.valueShape_size hhead.2).ge

set_option maxRecDepth 8192 in
/-- The native program at the ROM parameters has these facts. -/
instance : MldsaHHashData program where
  roundShapes := fun p t => (rounds_checked p t).1
  round_facts := fun p t => (rounds_checked p t).2
  const_states := by
    shape_decide
  const_rc := by
    intro t
    fin_cases t
    · show program.constEntries 11 = _ ∧ program.isConstant 11 = true ∧ program.valueField 11 = 1
      shape_decide
    · show program.constEntries 13 = _ ∧ program.isConstant 13 = true ∧ program.valueField 13 = 1
      shape_decide
    · show program.constEntries 14 = _ ∧ program.isConstant 14 = true ∧ program.valueField 14 = 1
      shape_decide
    · show program.constEntries 15 = _ ∧ program.isConstant 15 = true ∧ program.valueField 15 = 1
      shape_decide
    · show program.constEntries 16 = _ ∧ program.isConstant 16 = true ∧ program.valueField 16 = 1
      shape_decide
    · show program.constEntries 17 = _ ∧ program.isConstant 17 = true ∧ program.valueField 17 = 1
      shape_decide
    · show program.constEntries 18 = _ ∧ program.isConstant 18 = true ∧ program.valueField 18 = 1
      shape_decide
    · show program.constEntries 19 = _ ∧ program.isConstant 19 = true ∧ program.valueField 19 = 1
      shape_decide
    · show program.constEntries 20 = _ ∧ program.isConstant 20 = true ∧ program.valueField 20 = 1
      shape_decide
    · show program.constEntries 21 = _ ∧ program.isConstant 21 = true ∧ program.valueField 21 = 1
      shape_decide
    · show program.constEntries 22 = _ ∧ program.isConstant 22 = true ∧ program.valueField 22 = 1
      shape_decide
    · show program.constEntries 23 = _ ∧ program.isConstant 23 = true ∧ program.valueField 23 = 1
      shape_decide
    · show program.constEntries 24 = _ ∧ program.isConstant 24 = true ∧ program.valueField 24 = 1
      shape_decide
    · show program.constEntries 25 = _ ∧ program.isConstant 25 = true ∧ program.valueField 25 = 1
      shape_decide
    · show program.constEntries 26 = _ ∧ program.isConstant 26 = true ∧ program.valueField 26 = 1
      shape_decide
    · show program.constEntries 27 = _ ∧ program.isConstant 27 = true ∧ program.valueField 27 = 1
      shape_decide
    · show program.constEntries 28 = _ ∧ program.isConstant 28 = true ∧ program.valueField 28 = 1
      shape_decide
    · show program.constEntries 29 = _ ∧ program.isConstant 29 = true ∧ program.valueField 29 = 1
      shape_decide
    · show program.constEntries 30 = _ ∧ program.isConstant 30 = true ∧ program.valueField 30 = 1
      shape_decide
    · show program.constEntries 31 = _ ∧ program.isConstant 31 = true ∧ program.valueField 31 = 1
      shape_decide
    · show program.constEntries 18 = _ ∧ program.isConstant 18 = true ∧ program.valueField 18 = 1
      shape_decide
    · show program.constEntries 32 = _ ∧ program.isConstant 32 = true ∧ program.valueField 32 = 1
      shape_decide
    · show program.constEntries 17 = _ ∧ program.isConstant 17 = true ∧ program.valueField 17 = 1
      shape_decide
    · show program.constEntries 33 = _ ∧ program.isConstant 33 = true ∧ program.valueField 33 = 1
      shape_decide

/-- **The program facts of domain `H`'s core Keccak trace** (`MldsaHBaseCore` and): the shapes and
table facts of the `192` rounds of permutations `1 … 9` (`c̃'`'s absorbs and the SampleInBall
stream's absorb and squeeze), and the constant states. A program holding domain `H` without `μ`'s
call (permutation `0`) instantiates it. -/
class MldsaHHashDataCore (program : RealizedProgram) : Prop extends MldsaHBaseCore program where
  /-- The shapes of the rounds of permutations `1 … 9`. -/
  roundShapes : ∀ p : Fin 10, (p : ℕ) ≠ 0 → ∀ t : Fin 24, (program.predicate (roundPred p t)).body.roundShape? = some ⟨1, outVal p t, linRef p t, rcLeaf t, 10, 12, idx23, idx24⟩ ∧ (program.expr (linRef p t)).linShape? = some ⟨roundSrc p t.castSucc, linRef p t - 1, idx18, idx19, idx20, idx21, idx22⟩ ∧ (program.expr (linRef p t - 1)).colShape? = some (roundSrc p t.castSucc, idx17)
  /-- The rounds of permutations `1 … 9` are source predicates below the table's length, their
  shared expressions below the expressions' length, their outputs of `1600` coordinates. -/
  round_facts : ∀ p : Fin 10, (p : ℕ) ≠ 0 → ∀ t : Fin 24, roundPred p t < program.predicates.length ∧ program.inSource (program.predicate (roundPred p t)) = true ∧ linRef p t < program.exprs.length ∧ linRef p t - 1 < program.exprs.length ∧ 1600 ≤ (program.value (outVal p t)).size
  /-- The constant states: all ones (`const10`), all zeros (`const12`), in domain `H`'s field. -/
  const_states : program.constEntries 10 = List.replicate 1600 1 ∧ program.constEntries 12 = List.replicate 1600 0 ∧ program.isConstant 10 = true ∧ program.isConstant 12 = true ∧ program.valueField 10 = 1 ∧ program.valueField 12 = 1 ∧ program.domainField 1 = 1
  /-- The round constants' states: the bits of `rc t` in lane `(0, 0)`. -/
  const_rc : ∀ t : Fin 24, program.constEntries (rcLeaf t) = List.ofFn (fun j : Fin 1600 => if (j : ℕ) < 64 ∧ (rc t).testBit j then 1 else 0) ∧ program.isConstant (rcLeaf t) = true ∧ program.valueField (rcLeaf t) = 1

/-- A program with domain `H`'s Keccak trace has its core's. -/
instance {program : RealizedProgram} [h : MldsaHHashData program] : MldsaHHashDataCore program where
  roundShapes p _ t := h.roundShapes p t
  round_facts p _ t := h.round_facts p t
  const_states := h.const_states
  const_rc := h.const_rc

section Full

variable {program : RealizedProgram} [MldsaHHashData program]

/-- **The shapes of the `240` rounds** (generated data: reading predicate `263` of the table
unfolds `List.getD` that deep). -/
theorem roundShapes : ∀ p : Fin 10, ∀ t : Fin 24, (program.predicate (roundPred p t)).body.roundShape? = some ⟨1, outVal p t, linRef p t, rcLeaf t, 10, 12, idx23, idx24⟩ ∧ (program.expr (linRef p t)).linShape? = some ⟨roundSrc p t.castSucc, linRef p t - 1, idx18, idx19, idx20, idx21, idx22⟩ ∧ (program.expr (linRef p t - 1)).colShape? = some (roundSrc p t.castSucc, idx17) :=
  MldsaHHashData.roundShapes
/-- The rounds are source predicates below the table's length, their shared expressions below
the expressions' length, their outputs of `1600` coordinates. -/
theorem round_facts : ∀ p : Fin 10, ∀ t : Fin 24, roundPred p t < program.predicates.length ∧ program.inSource (program.predicate (roundPred p t)) = true ∧ linRef p t < program.exprs.length ∧ linRef p t - 1 < program.exprs.length ∧ 1600 ≤ (program.value (outVal p t)).size :=
  MldsaHHashData.round_facts

end Full

variable {program : RealizedProgram} [MldsaHHashDataCore program]

/-- **The shapes of the rounds of permutations `1 … 9`** (`roundShapes` off permutation `0`). -/
theorem roundShapes_core : ∀ p : Fin 10, (p : ℕ) ≠ 0 → ∀ t : Fin 24, (program.predicate (roundPred p t)).body.roundShape? = some ⟨1, outVal p t, linRef p t, rcLeaf t, 10, 12, idx23, idx24⟩ ∧ (program.expr (linRef p t)).linShape? = some ⟨roundSrc p t.castSucc, linRef p t - 1, idx18, idx19, idx20, idx21, idx22⟩ ∧ (program.expr (linRef p t - 1)).colShape? = some (roundSrc p t.castSucc, idx17) :=
  MldsaHHashDataCore.roundShapes
/-- The rounds of permutations `1 … 9` are source predicates below the table's length, their
shared expressions below the expressions' length, their outputs of `1600` coordinates. -/
theorem round_facts_core : ∀ p : Fin 10, (p : ℕ) ≠ 0 → ∀ t : Fin 24, roundPred p t < program.predicates.length ∧ program.inSource (program.predicate (roundPred p t)) = true ∧ linRef p t < program.exprs.length ∧ linRef p t - 1 < program.exprs.length ∧ 1600 ≤ (program.value (outVal p t)).size :=
  MldsaHHashDataCore.round_facts
/-- The constant states: all ones (`const10`), all zeros (`const12`), in domain `H`'s field. -/
theorem const_states : program.constEntries 10 = List.replicate 1600 1 ∧ program.constEntries 12 = List.replicate 1600 0 ∧ program.isConstant 10 = true ∧ program.isConstant 12 = true ∧ program.valueField 10 = 1 ∧ program.valueField 12 = 1 ∧ program.domainField 1 = 1 :=
  MldsaHHashDataCore.const_states
/-- The round constants' states: the bits of `rc t` in lane `(0, 0)`. -/
theorem const_rc : ∀ t : Fin 24, program.constEntries (rcLeaf t) = List.ofFn (fun j : Fin 1600 => if (j : ℕ) < 64 ∧ (rc t).testBit j then 1 else 0) ∧ program.isConstant (rcLeaf t) = true ∧ program.valueField (rcLeaf t) = 1 :=
  MldsaHHashDataCore.const_rc
end GordieHowe.MLDSA44
