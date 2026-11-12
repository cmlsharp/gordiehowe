-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweCerts.Applications.MLDSA44.Emulated.Frontend.Basic
public import GordieHoweCerts.Generated.MLDSA44.Emulated.ROMParams.Program
public import GordieHoweCerts.Applications.MLDSA44.Frontend.Cross

@[expose] public section

/-!
# GordieHowe frontend: an emulated ML-DSA program, the crossing

The crossing's obligation (`GordieHowe.MLDSA44.Emulated.ROMParams.CrossSound`, `crossSound`): `mac.equal` (predicate
`crossPred`) is `cross(H, x, A, y)` of width `1` with `x` the native program's shared expression
`525` renamed (H's `w1` bits, then H's decoded support and sign alternately; read through
the renaming, `GordieHowe.RealizedProgram.evalE_rename`, and the native frontend's `x_lo`, `x_even`, `x_odd`) and `y`
the shared expression `6` (A's `hint.w1` bits, then A's challenge bits `challenge.c`). The
compiler's contract (`GordieHowe.RealizedProgram.HoldsWith`) gives the readings' equality where every reading of `x`
is below `2`.
-/

namespace GordieHowe.MLDSA44.Emulated

open Generated.MLDSA44.Emulated.ROMParams.Program (idx8)
open GordieHowe.Bits

/-- **The program facts of an emulated program's crossing** (`MldsaEMain` and): the shared expression
`6` (A's operand, with the index maps of the program at the ROM parameters), the shared expressions' order, the lengths
and fields the crossing reads, and `mac.equal` (predicate `crossPred`) a crossing of the native
operand `525`, renamed, and `6`. Each emulated program instantiates it by `decide`. -/
class MldsaECross (program : RealizedProgram) extends MldsaEMain program where
  /-- `expr6`. -/
  expr6 : program.expr 6 = .reindex idx8 (RealizedProgram.concatR (.leaf 63) [.leaf 60])
  /-- The program's shared expressions read only earlier ones. -/
  refsOrdered : program.RefsOrdered
  /-- `mac.equal`, the crossing. -/
  crossPred : ℕ
  /-- The lengths and fields the crossing reads. -/
  crossData : program.exprLen (.ref ((MldsaEmbed.σ program).ref 525)) = 6656 ∧ program.exprLen (.leaf 63) = 6144 ∧ program.exprLen (.leaf 60) = 512 ∧ program.domainField 1 = 1 ∧ program.domainField 0 = 0 ∧ 6 < program.exprs.length ∧ crossPred < program.predicates.length ∧
    program.inSource (program.predicate crossPred) = true ∧ (525 : ℕ) ∈ MldsaEmbed.R program
  /-- `mac.equal` crosses the native operand `525`, renamed, of domain `H` and `6` of domain `A`. -/
  cross : ∃ c, (program.predicate crossPred).body = .cross 1 (.ref ((MldsaEmbed.σ program).ref 525)) 0 (.ref 6) {} c

set_option linter.unusedSectionVars false

variable {program : RealizedProgram} [MldsaECross program] {F0 FH : RealizedProgram.FieldInterp} [RealizedProgram.PrimeCastField F0 pGold]
  [HField FH]

set_option hygiene false in
local notation "nat" => MldsaEmbed.nat program

set_option hygiene false in
local notation "σ" => MldsaEmbed.σ program

set_option hygiene false in
local notation "hV" => MldsaEmbed.V program

variable [MldsaHHash nat] [MldsaHSample nat] [MldsaHConsts nat FH]

set_option hygiene false in
local notation "interp" => RealizedProgram.mldsaInterpOf F0 FH

/-! ## The program's data -/

/-! The program's predicate and shared-expression tables have `276` and `528` entries; the
identities below read entries of them. -/

section Tables


theorem expr6 : program.expr 6 = .reindex idx8 (RealizedProgram.concatR (.leaf 63) [.leaf 60]) :=
  MldsaECross.expr6

end Tables

/-- The program's shared expressions read only earlier ones. -/
theorem refsOrdered : program.RefsOrdered :=
  MldsaECross.refsOrdered

/-- The lengths and fields the crossing reads. -/
theorem crossData : program.exprLen (.ref ((σ).ref 525)) = 6656 ∧ program.exprLen (.leaf 63) = 6144 ∧
    program.exprLen (.leaf 60) = 512 ∧ program.domainField 1 = 1 ∧ program.domainField 0 = 0 ∧
    6 < program.exprs.length ∧ MldsaECross.crossPred program < program.predicates.length ∧
    program.inSource (program.predicate (MldsaECross.crossPred program)) = true ∧
    (525 : ℕ) ∈ MldsaEmbed.R program :=
  MldsaECross.crossData

/-! The index map of the crossing: `y` reads its two parts in order. -/

theorem idx8_id' : ∀ a < 104, ∀ b < 64, idx8.entry (64 * a + b) = 64 * a + b := by decide +kernel
theorem idx8_id : ∀ t < 6656, idx8.entry t = t := fun t ht => by
  have h := idx8_id' (t / 64) (by omega) (t % 64) (by omega)
  rwa [Nat.div_add_mod] at h

/-! ## The two operands' coordinates -/

section Operands

variable (e : program.Env interp)

/-- **`x`** is the native program's crossing operand, read through the renaming. -/
theorem x_eq (i : ℕ) : program.evalE (program.reader e) 1 (.ref ((σ).ref 525)) i =
    (nat).evalE ((nat).reader (pull e)) 1 (.ref 525) i :=
  congrFun (RealizedProgram.evalE_rename MldsaEmbed.embedding e (e := .ref 525) rfl (by simp [RealizedProgram.Expr.directNodes])
    (by simpa [RealizedProgram.Expr.refs] using (crossData (program := program)).2.2.2.2.2.2.2.2)) i

/-- **`y` below `6144`** is A's `hint.w1` bit. -/
theorem y_lo {t : ℕ} (ht : t < 6144) :
    program.evalE (program.reader e) 0 (.ref 6) t = program.evalE (program.reader e) 0 (.leaf 63) t := by
  rw [RealizedProgram.evalE_ref (refsOrdered (program := program)) _ _
      (crossData (program := program)).2.2.2.2.2.1, (expr6 (program := program)),
    RealizedProgram.evalE_wiring_part _ _ _ _ _ (j := 0) (k := t) (by simp)
      (by simp [(crossData (program := program)).2.1, ht])
      (by simp [idx8_id t (by omega), RealizedProgram.partBase])]
  rfl

/-- **`y` at `6144 + i`** is A's challenge bit `i`. -/
theorem y_hi {i : ℕ} (hi : i < 512) :
    program.evalE (program.reader e) 0 (.ref 6) (6144 + i) =
      program.evalE (program.reader e) 0 (.leaf 60) i := by
  rw [RealizedProgram.evalE_ref (refsOrdered (program := program)) _ _
      (crossData (program := program)).2.2.2.2.2.1, (expr6 (program := program)),
    RealizedProgram.evalE_wiring_part _ _ _ _ _ (j := 1) (k := i) (by simp)
      (by simp [(crossData (program := program)).2.2.1, hi])
      (by simp [idx8_id (6144 + i) (by omega), RealizedProgram.partBase,
        (crossData (program := program)).2.1])]
  rfl

end Operands

/-! ## The crossing -/

/-- **`mac.equal` gives the crossing** wherever the source program holds and H's decoded support
and sign are bits: the compiler's contract at its premise, every reading of `x` below `2`. -/
theorem crossSound : CrossSound (program := program) (F0 := F0) (FH := FH) := by
  intro e hs hsup hsgn
  have hmac : program.HoldsAt e (program.predicate (MldsaECross.crossPred program)).body :=
    hs.preds _ (RealizedProgram.predicate_mem (crossData (program := program)).2.2.2.2.2.2.1)
      (crossData (program := program)).2.2.2.2.2.2.2.1
  obtain ⟨c, hc⟩ := MldsaECross.cross (program := program)
  rw [hc] at hmac
  obtain ⟨-, hxy⟩ := hmac
  change (∀ i < program.exprLen (.ref ((σ).ref 525)),
      (interp (program.domainField 1)).toNat (program.evalE (program.reader e)
        (program.domainField 1) (.ref ((σ).ref 525)) i) < 2) → ∀ i < program.exprLen (.ref ((σ).ref 525)),
      (interp (program.domainField 1)).toNat (program.evalE (program.reader e)
        (program.domainField 1) (.ref ((σ).ref 525)) i) =
      (interp (program.domainField 0)).toNat (program.evalE (program.reader e)
        (program.domainField 0) (.ref 6) i) at hxy
  rw [(crossData (program := program)).2.2.2.1, (crossData (program := program)).2.2.2.2.1, (crossData (program := program)).1] at hxy
  have hpre : ∀ i < 6656,
      (interp 1).toNat (program.evalE (program.reader e) 1 (.ref ((σ).ref 525)) i) < 2 := by
    intro i hi
    rw [x_eq]
    by_cases hlo : i < 6144
    · rw [MLDSA44.x_lo (pull e) hlo]
      exact MLDSA44.toNat_lt_two_of_gf128_bool (MLDSA44.w1H_bool (pull e) i)
    · obtain ⟨k, hk, rfl | rfl⟩ : ∃ k < 256, i = 6144 + 2 * k ∨ i = 6144 + (2 * k + 1) :=
        ⟨(i - 6144) / 2, by omega, by omega⟩
      · rw [MLDSA44.x_even (pull e) hk]
        exact hsup ⟨k, hk⟩
      · rw [MLDSA44.x_odd (pull e) hk]
        exact hsgn ⟨k, hk⟩
  have heq := hxy hpre
  refine ⟨fun t => ?_, fun k => ?_, fun k => ?_⟩
  · have h := heq t (by have := t.isLt; omega)
    rw [x_eq, MLDSA44.x_lo (pull e) t.isLt, y_lo e t.isLt] at h
    exact h.symm
  · have hk : (k : ℕ) < 256 := k.isLt
    have h := heq (6144 + 2 * k) (by omega)
    rw [x_eq, MLDSA44.x_even (pull e) hk,
      show 6144 + 2 * (k : ℕ) = 6144 + (2 * k + 0) from rfl, y_hi e (by omega)] at h
    exact h.symm
  · have hk : (k : ℕ) < 256 := k.isLt
    have h := heq (6144 + (2 * k + 1)) (by omega)
    rw [x_eq, MLDSA44.x_odd (pull e) hk, y_hi e (by omega)] at h
    exact h.symm

end GordieHowe.MLDSA44.Emulated
