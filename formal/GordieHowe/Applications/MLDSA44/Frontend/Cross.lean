-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Frontend.Basic
public import GordieHowe.Language.Library.Eval

@[expose] public section

/-!
# GordieHowe frontend: `MLDSA44.Native.ROMParams`, the crossing

The crossing's obligation of the frontend (`GordieHowe.MLDSA44.CrossSound`, `crossSound`):
`mac.equal` (predicate `272`) is `cross(H, x, A, y)` of width `1` with `x` the shared expression
`525` (H's `w1` bits at coordinates below `6144`, then H's decoded support and sign of each
coefficient alternately) and `y` the shared expression `7` (A's `hint.w1` bits, then A's challenge
bits `challenge.c`). The compiler's contract (`GordieHowe.RealizedProgram.HoldsWith`) gives the readings' equality
where every reading of `x` is below `2`: the `w1` part is a bit view, the support and sign are bits
by hypothesis (SampleInBall's soundness).
-/

namespace GordieHowe.MLDSA44

open Generated.MLDSA44.Native.ROMParams.Program
open GordieHowe.Bits

/-! ## The program's data -/

/-! The program's predicate and shared-expression tables have `273` and `526` entries; reading an
entry by `rfl` unfolds `List.getD` that deep, past the default recursion depth, so the identities
below raise `maxRecDepth` (generated data, not a proof structure). -/

section Tables

set_option maxRecDepth 4096

theorem pred272 : program.predicate 272 = «p.mac.equal» := rfl
theorem expr525 : program.expr 525 =
    .reindex idx83 (RealizedProgram.concatR (.leaf 70) [.ref 523, .ref 524]) := rfl
theorem expr524 : program.expr 524 = .ref 522 := rfl
theorem expr7 : program.expr 7 = .reindex idx10 (RealizedProgram.concatR (.leaf 62) [.leaf 59]) :=
  rfl

end Tables

/-- The program's shared expressions read only earlier ones. -/
theorem refsOrdered : program.RefsOrdered :=
  (RealizedProgram.refsOrderedB_iff program).1 (by decide +kernel)

/-- The lengths the crossing reads. -/
theorem len525 : program.exprLen (.ref 525) = 6656 := by decide +kernel
theorem len523 : program.exprLen (.ref 523) = 256 := by decide +kernel
theorem len524 : program.exprLen (.ref 524) = 256 := by decide +kernel
theorem len71 : program.exprLen (.leaf 70) = 6144 := by decide +kernel
theorem len63 : program.exprLen (.leaf 62) = 6144 := by decide +kernel
theorem len60 : program.exprLen (.leaf 59) = 512 := by decide +kernel
theorem crossFields : program.domainField 1 = 1 ∧ program.domainField 0 = 0 := by
  decide +kernel
theorem crossRefs : 525 < program.exprs.length ∧ 524 < program.exprs.length ∧
    7 < program.exprs.length := by
  decide +kernel

/-! The index maps of the crossing: `x` reads `w1` below `6144`, then the support and the sign of
each coefficient alternately; `y` reads its two parts in order. -/

theorem idx10_id' : ∀ a < 104, ∀ b < 64, idx10.entry (64 * a + b) = 64 * a + b := by decide +kernel
theorem idx10_id : ∀ t < 6656, idx10.entry t = t := fun t ht => by
  have h := idx10_id' (t / 64) (by omega) (t % 64) (by omega)
  rwa [Nat.div_add_mod] at h
theorem idx83_lo' : ∀ a < 96, ∀ b < 64, idx83.entry (64 * a + b) = 64 * a + b := by decide +kernel
theorem idx83_lo : ∀ t < 6144, idx83.entry t = t := fun t ht => by
  have h := idx83_lo' (t / 64) (by omega) (t % 64) (by omega)
  rwa [Nat.div_add_mod] at h
theorem idx83_even : ∀ k < 256, idx83.entry (6144 + 2 * k) = 6144 + k := by decide +kernel
theorem idx83_odd : ∀ k < 256, idx83.entry (6144 + (2 * k + 1)) = 6400 + k := by decide +kernel

/-- **The program facts of domain `H` the crossing's operands read** (`MldsaHBaseCore` and): the shared
expressions `525` (the crossing's `x`, with the index maps of the program at the ROM parameters) and `524`, their
lengths and ordering, and the bit view `70` (H's `w1`). Each program instantiates it by `decide`. -/
class MldsaHCross (program : RealizedProgram) : Prop extends MldsaHBaseCore program where
  /-- The shared expressions read only earlier ones. -/
  refsOrdered : program.RefsOrdered
  /-- Expression `525` exists. -/
  lt525 : 525 < program.exprs.length
  /-- Expression `524` exists. -/
  lt524 : 524 < program.exprs.length
  /-- Expression `525`, the crossing's `x`. -/
  expr525 : program.expr 525 =
    .reindex idx83 (RealizedProgram.concatR (.leaf 70) [.ref 523, .ref 524])
  /-- Expression `524` is `522`. -/
  expr524 : program.expr 524 = .ref 522
  /-- The length of `70`. -/
  len71 : program.exprLen (.leaf 70) = 6144
  /-- The length of `523`. -/
  len523 : program.exprLen (.ref 523) = 256
  /-- The length of `524`. -/
  len524 : program.exprLen (.ref 524) = 256
  /-- Value `70` is a bit view. -/
  bitView71 : program.isBitView 70 = true
  /-- Domain `H` is field `1`. -/
  domainField1 : program.domainField 1 = 1

/-- The native program at the ROM parameters has the crossing's facts of domain `H`. -/
instance : MldsaHCross program where
  refsOrdered := refsOrdered
  lt525 := crossRefs.1
  lt524 := crossRefs.2.1
  expr525 := expr525
  expr524 := expr524
  len71 := len71
  len523 := len523
  len524 := len524
  bitView71 := by decide +kernel
  domainField1 := crossFields.1

section H

variable {program : RealizedProgram} [MldsaHCross program] {F0 FH : RealizedProgram.FieldInterp} [HField FH]

set_option hygiene false in
local notation "interp" => RealizedProgram.mldsaInterpOf F0 FH

/-! ## The two operands' coordinates -/

section Operands

variable (e : program.Env interp)

/-- **`x` below `6144`** is H's `w1` bit. -/
theorem x_lo {t : ℕ} (ht : t < 6144) :
    program.evalE (program.reader e) 1 (.ref 525) t = program.evalE (program.reader e) 1 (.leaf 70) t := by
  rw [RealizedProgram.evalE_ref MldsaHCross.refsOrdered _ _ MldsaHCross.lt525, MldsaHCross.expr525,
    RealizedProgram.evalE_wiring_part _ _ _ _ _ (j := 0) (k := t) (by simp)
      (by simp [MldsaHCross.len71, ht]) (by simp [idx83_lo t ht, RealizedProgram.partBase])]
  rfl

/-- **`x` at `6144 + 2 k`** is H's decoded support of coefficient `k`. -/
theorem x_even {k : ℕ} (hk : k < 256) :
    program.evalE (program.reader e) 1 (.ref 525) (6144 + 2 * k) =
      program.evalE (program.reader e) 1 (.ref 523) k := by
  rw [RealizedProgram.evalE_ref MldsaHCross.refsOrdered _ _ MldsaHCross.lt525, MldsaHCross.expr525,
    RealizedProgram.evalE_wiring_part _ _ _ _ _ (j := 1) (k := k) (by simp)
      (by simp [MldsaHCross.len523, hk])
      (by simp [idx83_even k hk, RealizedProgram.partBase, MldsaHCross.len71])]
  rfl

/-- **`x` at `6144 + 2 k + 1`** is H's decoded sign of coefficient `k`. -/
theorem x_odd {k : ℕ} (hk : k < 256) :
    program.evalE (program.reader e) 1 (.ref 525) (6144 + (2 * k + 1)) =
      program.evalE (program.reader e) 1 (.ref 522) k := by
  rw [RealizedProgram.evalE_ref MldsaHCross.refsOrdered _ _ MldsaHCross.lt525, MldsaHCross.expr525,
    RealizedProgram.evalE_wiring_part _ _ _ _ _ (j := 2) (k := k) (by simp)
      (by simp [MldsaHCross.len524, hk])
      (by simp [idx83_odd k hk, RealizedProgram.partBase, MldsaHCross.len71, MldsaHCross.len523] <;>
        omega)]
  change program.evalE (program.reader e) 1 (.ref 524) k = _
  rw [RealizedProgram.evalE_ref MldsaHCross.refsOrdered _ _ MldsaHCross.lt524, MldsaHCross.expr524]

end Operands

/-! ## The crossing -/

/-- **H's `w1` bits are bits** (a bit view). -/
theorem w1H_bool (e : program.Env interp) (t : ℕ) :
    program.evalE (program.reader e) 1 (.leaf 70) t = 0 ∨
      program.evalE (program.reader e) 1 (.leaf 70) t = 1 :=
  RealizedProgram.evalE_leaf_bool_of_isBitView e MldsaHCross.bitView71 1 t

/-- An element of domain `H`'s field that is a bit is read below `2`. -/
theorem toNat_lt_two_of_gf128_bool {x : (interp 1).K} (h : x = 0 ∨ x = 1) :
    (interp 1).toNat x < 2 := by
  rcases h with rfl | rfl
  · exact (HField.toNat_zero (FH := FH)).symm ▸ Nat.two_pos
  · exact (HField.toNat_one (FH := FH)).symm ▸ Nat.one_lt_two

end H

/-- **The program facts of the crossing's A operand** (`MldsaABase`, `MldsaHCross` and): the
shared expression `7` (A's operand, with the index maps of the program at the ROM parameters), its pieces' lengths,
and `mac.equal` (predicate `272`) a crossing of `525` and `7`.
Each program instantiates it by `decide`. -/
class MldsaACross (program : RealizedProgram) : Prop extends MldsaABase program, MldsaHCross program where
  /-- Expression `7` exists. -/
  lt7 : 7 < program.exprs.length
  /-- Expression `7`, the crossing's `y`. -/
  expr7 : program.expr 7 = .reindex idx10 (RealizedProgram.concatR (.leaf 62) [.leaf 59])
  /-- The length of `63`. -/
  len63 : program.exprLen (.leaf 62) = 6144
  /-- The length of `60`. -/
  len60 : program.exprLen (.leaf 59) = 512
  /-- The length of `525`. -/
  len525 : program.exprLen (.ref 525) = 6656
  /-- Domain `A` is field `0`. -/
  domainField0 : program.domainField 0 = 0
  /-- Predicate `272` is a source predicate. -/
  src272 : 272 < program.predicates.length ∧ program.inSource (program.predicate 272) = true
  /-- Predicate `272` (`mac.equal`) crosses `525` of domain `H` and `7` of domain `A`. -/
  crossPred : ∃ c, (program.predicate 272).body = .cross 1 (.ref 525) 0 (.ref 7) {} c

set_option maxRecDepth 4096 in
/-- The native program at the ROM parameters has the crossing's facts. -/
instance : MldsaACross program where
  lt7 := crossRefs.2.2
  expr7 := expr7
  len63 := len63
  len60 := len60
  len525 := len525
  domainField0 := crossFields.2
  src272 := ⟨by decide +kernel, by rw [pred272]; rfl⟩
  crossPred := ⟨_, by rw [pred272]; rfl⟩

section A

set_option linter.unusedSectionVars false

variable {program : RealizedProgram} [MldsaACross program] {F0 FH : RealizedProgram.FieldInterp} [QField F0]
  [HField FH]

set_option hygiene false in
local notation "interp" => RealizedProgram.mldsaInterpOf F0 FH

section OperandsA

variable (e : program.Env interp)

/-- **`y` below `6144`** is A's `hint.w1` bit. -/
theorem y_lo {t : ℕ} (ht : t < 6144) :
    program.evalE (program.reader e) 0 (.ref 7) t = program.evalE (program.reader e) 0 (.leaf 62) t := by
  rw [RealizedProgram.evalE_ref MldsaHCross.refsOrdered _ _ MldsaACross.lt7, MldsaACross.expr7,
    RealizedProgram.evalE_wiring_part _ _ _ _ _ (j := 0) (k := t) (by simp)
      (by simp [MldsaACross.len63, ht]) (by simp [idx10_id t (by omega), RealizedProgram.partBase])]
  rfl

/-- **`y` at `6144 + i`** is A's challenge bit `i`. -/
theorem y_hi {i : ℕ} (hi : i < 512) :
    program.evalE (program.reader e) 0 (.ref 7) (6144 + i) =
      program.evalE (program.reader e) 0 (.leaf 59) i := by
  rw [RealizedProgram.evalE_ref MldsaHCross.refsOrdered _ _ MldsaACross.lt7, MldsaACross.expr7,
    RealizedProgram.evalE_wiring_part _ _ _ _ _ (j := 1) (k := i) (by simp)
      (by simp [MldsaACross.len60, hi])
      (by simp [idx10_id (6144 + i) (by omega), RealizedProgram.partBase, MldsaACross.len63])]
  rfl

end OperandsA

/-- **`mac.equal` gives the crossing** wherever the source program holds and H's decoded support
and sign are bits: the compiler's contract (`RealizedProgram.HoldsWith` of a cross-field `equal`) at its
premise, every reading of `x` below `2`. -/
theorem crossSound : CrossSound (program := program) (F0 := F0) (FH := FH) := by
  intro e hs hsup hsgn
  have hmac : program.HoldsAt e (program.predicate 272).body :=
    hs.preds _ (RealizedProgram.predicate_mem MldsaACross.src272.1) MldsaACross.src272.2
  obtain ⟨c, hc⟩ := MldsaACross.crossPred (program := program)
  rw [hc] at hmac
  obtain ⟨-, hxy⟩ := hmac
  change (∀ i < program.exprLen (.ref 525),
      (interp (program.domainField 1)).toNat (program.evalE (program.reader e)
        (program.domainField 1) (.ref 525) i) < 2) → ∀ i < program.exprLen (.ref 525),
      (interp (program.domainField 1)).toNat (program.evalE (program.reader e)
        (program.domainField 1) (.ref 525) i) =
      (interp (program.domainField 0)).toNat (program.evalE (program.reader e)
        (program.domainField 0) (.ref 7) i) at hxy
  rw [MldsaHCross.domainField1, MldsaACross.domainField0, MldsaACross.len525] at hxy
  have hpre : ∀ i < 6656, (interp 1).toNat (program.evalE (program.reader e) 1 (.ref 525) i) < 2 := by
    intro i hi
    by_cases hlo : i < 6144
    · rw [x_lo e hlo]
      exact toNat_lt_two_of_gf128_bool (w1H_bool e i)
    · obtain ⟨k, hk, rfl | rfl⟩ : ∃ k < 256, i = 6144 + 2 * k ∨ i = 6144 + (2 * k + 1) :=
        ⟨(i - 6144) / 2, by omega, by omega⟩
      · rw [x_even e hk]
        exact hsup ⟨k, hk⟩
      · rw [x_odd e hk]
        exact hsgn ⟨k, hk⟩
  have heq := hxy hpre
  refine ⟨fun t => ?_, fun k => ?_, fun k => ?_⟩
  · have h := heq t (by have := t.isLt; omega)
    rw [x_lo e t.isLt, y_lo e t.isLt] at h
    exact h.symm
  · have hk : (k : ℕ) < 256 := k.isLt
    have h := heq (6144 + 2 * k) (by omega)
    rw [x_even e hk, show 6144 + 2 * (k : ℕ) = 6144 + (2 * k + 0) from rfl,
      y_hi e (by omega)] at h
    exact h.symm
  · have hk : (k : ℕ) < 256 := k.isLt
    have h := heq (6144 + (2 * k + 1)) (by omega)
    rw [x_odd e hk, y_hi e (by omega)] at h
    exact h.symm

end A

end GordieHowe.MLDSA44
