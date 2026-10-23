-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Emulated.Frontend.Basic
public import GordieHowe.Generated.MLDSA44.Emulated.ROMParams.Program
public import GordieHowe.Applications.MLDSA44.Native.ROMParams.Frontend.Cross

@[expose] public section

/-!
# GordieHowe frontend: an emulated ML-DSA program, the crossing

The crossing's obligation (`GordieHowe.MLDSA44.Emulated.ROMParams.CrossSound`, `crossSound`): `mac.equal` (predicate
`275`) is `cross(H, x, A, y)` of width `1` with `x` the shared expression `527`, the native
program's `525` renamed (H's `w1` bits, then H's decoded support and sign alternately; read through
the renaming, `GordieHowe.RealizedProgram.evalE_rename`, and the native frontend's `x_lo`, `x_even`, `x_odd`) and `y`
the shared expression `6` (A's `hint.w1` bits, then A's challenge bits `challenge.c`). The
compiler's contract (`GordieHowe.RealizedProgram.HoldsWith`) gives the readings' equality where every reading of `x`
is below `2`.
-/

namespace GordieHowe.MLDSA44.Emulated

open Generated.MLDSA44.Emulated.ROMParams.Program (idx8 idx9)
open GordieHowe.Bits
open Native.ROMParams (MldsaHHash MldsaHSample MldsaHConsts)

/-- **The program facts of an emulated program's crossing** (`MldsaEMain` and): the shared expression
`6` (A's operand, with the index maps of the program at the ROM parameters), the shared expressions' order, the lengths
and fields the crossing reads, and `mac.equal` (predicate `275`) a crossing of `527` and `6`. Each
emulated program instantiates it by `decide`. -/
class MldsaECross (program : RealizedProgram) extends MldsaEMain program where
  /-- `expr6`. -/
  expr6 : program.expr 6 = .add (.reindex idx8 (.concat (.leaf 64) (.leaf 7))) (.reindex idx9 (.concat (.leaf 61) (.leaf 7)))
  /-- The program's shared expressions read only earlier ones. -/
  refsOrdered : program.RefsOrdered
  /-- The lengths and fields the crossing reads. -/
  crossData : program.exprLen (.ref 527) = 6656 ∧ program.exprLen (.leaf 64) = 6144 ∧ program.exprLen (.leaf 61) = 512 ∧ program.domainField 1 = 1 ∧ program.domainField 0 = 0 ∧ program.valueField 7 = 0 ∧ 6 < program.exprs.length ∧ program.isConstant 7 = true ∧ program.constEntries 7 = [0] ∧ 275 < program.predicates.length ∧ program.inSource (program.predicate 275) = true ∧ (525 : ℕ) ∈ hR
  /-- Predicate `275` (`mac.equal`) crosses `527` of domain `H` and `6` of domain `A`. -/
  crossPred : ∃ c, (program.predicate 275).body = .cross 1 (.ref 527) 0 (.ref 6) {} c

set_option linter.unusedSectionVars false

variable {program : RealizedProgram} [MldsaECross program] {F0 FH : RealizedProgram.FieldInterp} [AField F0]
  [HField FH]

set_option hygiene false in
local notation "nat" => MldsaEmbed.nat program

variable [MldsaHHash nat] [MldsaHSample nat] [MldsaHConsts nat FH]

set_option hygiene false in
local notation "interp" => RealizedProgram.mldsaInterpOf F0 FH

/-! ## The program's data -/

/-! The program's predicate and shared-expression tables have `276` and `528` entries; reading an
entry by `rfl` unfolds `List.getD` that deep, past the default recursion depth, so the identities
below raise `maxRecDepth` (generated data, not a proof structure; as `GordieHowe/Applications/MLDSA44/Native/ROMParams/Frontend/Cross.lean`). -/

section Tables

set_option maxRecDepth 4096

theorem expr6 : program.expr 6 = .add (.reindex idx8 (.concat (.leaf 64) (.leaf 7))) (.reindex idx9 (.concat (.leaf 61) (.leaf 7))) :=
  MldsaECross.expr6

end Tables

/-- The program's shared expressions read only earlier ones. -/
theorem refsOrdered : program.RefsOrdered :=
  MldsaECross.refsOrdered

/-- The lengths and fields the crossing reads. -/
theorem crossData : program.exprLen (.ref 527) = 6656 ∧ program.exprLen (.leaf 64) = 6144 ∧ program.exprLen (.leaf 61) = 512 ∧ program.domainField 1 = 1 ∧ program.domainField 0 = 0 ∧ program.valueField 7 = 0 ∧ 6 < program.exprs.length ∧ program.isConstant 7 = true ∧ program.constEntries 7 = [0] ∧ 275 < program.predicates.length ∧ program.inSource (program.predicate 275) = true ∧ (525 : ℕ) ∈ hR :=
  MldsaECross.crossData

/-! The index maps of the crossing. -/

theorem idx8_lo' : ∀ a < 96, ∀ b < 64, idx8.entry (64 * a + b) = 64 * a + b := by decide +kernel
theorem idx8_lo : ∀ t < 6144, idx8.entry t = t := fun t ht => by
  have h := idx8_lo' (t / 64) (by omega) (t % 64) (by omega)
  rwa [Nat.div_add_mod] at h
theorem idx8_hi : ∀ i < 512, idx8.entry (6144 + i) = 6144 := by decide +kernel
theorem idx9_lo' : ∀ a < 96, ∀ b < 64, idx9.entry (64 * a + b) = 512 := by decide +kernel
theorem idx9_lo : ∀ t < 6144, idx9.entry t = 512 := fun t ht => by
  have h := idx9_lo' (t / 64) (by omega) (t % 64) (by omega)
  rwa [Nat.div_add_mod] at h
theorem idx9_hi : ∀ i < 512, idx9.entry (6144 + i) = i := by decide +kernel

/-! ## The two operands' coordinates -/

section Operands

variable (e : program.Env interp)

/-- The zero constant of `A` reads `0`. -/
theorem zero7 (i : ℕ) : program.evalE (program.reader e) 0 (.leaf 7) i = 0 := by
  rw [RealizedProgram.evalE_leaf_of_isConstant e (crossData (program := program)).2.2.2.2.2.2.2.1,
    RealizedProgram.constRead_of_valueField (crossData (program := program)).2.2.2.2.2.1, (crossData (program := program)).2.2.2.2.2.2.2.2.1]
  have h : ([0] : List ℕ).getD i 0 = 0 := by cases i <;> simp
  rw [h, AField.decode_eq]
  exact Nat.cast_zero

/-- **`x`** is the native program's crossing operand, read through the renaming. -/
theorem x_eq (i : ℕ) : program.evalE (program.reader e) 1 (.ref 527) i =
    (nat).evalE ((nat).reader (pull e)) 1 (.ref 525) i :=
  congrFun (RealizedProgram.evalE_rename MldsaEmbed.embedding e (e := .ref 525) rfl (by simp [RealizedProgram.Expr.directNodes])
    (by simpa [RealizedProgram.Expr.refs] using (crossData (program := program)).2.2.2.2.2.2.2.2.2.2.2)) i

/-- **`y` below `6144`** is A's `hint.w1` bit. -/
theorem y_lo {t : ℕ} (ht : t < 6144) :
    program.evalE (program.reader e) 0 (.ref 6) t = program.evalE (program.reader e) 0 (.leaf 64) t := by
  rw [RealizedProgram.evalE_ref (refsOrdered (program := program)) _ _ (crossData (program := program)).2.2.2.2.2.2.1, (expr6 (program := program))]
  simp only [RealizedProgram.evalE_add, RealizedProgram.evalE_reindex, RealizedProgram.evalE_concat, idx8_lo t ht,
    idx9_lo t ht, (crossData (program := program)).2.1, (crossData (program := program)).2.2.1, ht, lt_self_iff_false, if_true, if_false, zero7,
    add_zero]

/-- **`y` at `6144 + i`** is A's challenge bit `i`. -/
theorem y_hi {i : ℕ} (hi : i < 512) :
    program.evalE (program.reader e) 0 (.ref 6) (6144 + i) =
      program.evalE (program.reader e) 0 (.leaf 61) i := by
  rw [RealizedProgram.evalE_ref (refsOrdered (program := program)) _ _ (crossData (program := program)).2.2.2.2.2.2.1, (expr6 (program := program))]
  simp only [RealizedProgram.evalE_add, RealizedProgram.evalE_reindex, RealizedProgram.evalE_concat, idx8_hi i hi,
    idx9_hi i hi, (crossData (program := program)).2.1, (crossData (program := program)).2.2.1, hi, lt_self_iff_false, if_true, if_false, zero7,
    zero_add]

end Operands

/-! ## The crossing -/

/-- **`mac.equal` gives the crossing** wherever the source program holds and H's decoded support
and sign are bits: the compiler's contract at its premise, every reading of `x` below `2`. -/
theorem crossSound : CrossSound (program := program) (F0 := F0) (FH := FH) := by
  intro e hs hsup hsgn
  have hmac : program.HoldsAt e (program.predicate 275).body :=
    hs.preds _ (RealizedProgram.predicate_mem (crossData (program := program)).2.2.2.2.2.2.2.2.2.1)
      (crossData (program := program)).2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨c, hc⟩ := MldsaECross.crossPred (program := program)
  rw [hc] at hmac
  obtain ⟨-, hxy⟩ := hmac
  change (∀ i < program.exprLen (.ref 527),
      (interp (program.domainField 1)).toNat (program.evalE (program.reader e)
        (program.domainField 1) (.ref 527) i) < 2) → ∀ i < program.exprLen (.ref 527),
      (interp (program.domainField 1)).toNat (program.evalE (program.reader e)
        (program.domainField 1) (.ref 527) i) =
      (interp (program.domainField 0)).toNat (program.evalE (program.reader e)
        (program.domainField 0) (.ref 6) i) at hxy
  rw [(crossData (program := program)).2.2.2.1, (crossData (program := program)).2.2.2.2.1, (crossData (program := program)).1] at hxy
  have hpre : ∀ i < 6656,
      (interp 1).toNat (program.evalE (program.reader e) 1 (.ref 527) i) < 2 := by
    intro i hi
    rw [x_eq]
    by_cases hlo : i < 6144
    · rw [Native.ROMParams.x_lo (pull e) hlo]
      exact Native.ROMParams.toNat_lt_two_of_gf128_bool (Native.ROMParams.w1H_bool (pull e) i)
    · obtain ⟨k, hk, rfl | rfl⟩ : ∃ k < 256, i = 6144 + 2 * k ∨ i = 6144 + (2 * k + 1) :=
        ⟨(i - 6144) / 2, by omega, by omega⟩
      · rw [Native.ROMParams.x_even (pull e) hk]
        exact hsup ⟨k, hk⟩
      · rw [Native.ROMParams.x_odd (pull e) hk]
        exact hsgn ⟨k, hk⟩
  have heq := hxy hpre
  refine ⟨fun t => ?_, fun k => ?_, fun k => ?_⟩
  · have h := heq t (by have := t.isLt; omega)
    rw [x_eq, Native.ROMParams.x_lo (pull e) t.isLt, y_lo e t.isLt] at h
    exact h.symm
  · have hk : (k : ℕ) < 256 := k.isLt
    have h := heq (6144 + 2 * k) (by omega)
    rw [x_eq, Native.ROMParams.x_even (pull e) hk,
      show 6144 + 2 * (k : ℕ) = 6144 + (2 * k + 0) from rfl, y_hi e (by omega)] at h
    exact h.symm
  · have hk : (k : ℕ) < 256 := k.isLt
    have h := heq (6144 + (2 * k + 1)) (by omega)
    rw [x_eq, Native.ROMParams.x_odd (pull e) hk, y_hi e (by omega)] at h
    exact h.symm

end GordieHowe.MLDSA44.Emulated
