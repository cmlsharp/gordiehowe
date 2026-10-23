-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Emulated.HonestAlgebra
public import GordieHowe.Applications.MLDSA44.Native.ROMParams.HonestSelect
public import GordieHowe.Language.Honest.Digits
public import GordieHowe.Applications.MLDSA44.Emulated.System.Honest

@[expose] public section

/-!
# GordieHowe: the honest valuation of an emulated ML-DSA program

The honest committed values of an emulated ML-DSA program (`MLDSA44.Emulated.ROMParams`,
`MLDSA44.Emulated.QROMParams`) on an honest input (`honestVal`): domain `H`'s are the native program's
(`GordieHowe.MLDSA44.Native.ROMParams.hVal` at the embedded native program, one identifier lower), and domain `A`'s
(`aVal`) `GordieHowe.MLDSA44.Emulated`'s honest assignment's hint, challenge bits, UseHint output bits and
signs (`GordieHowe.MLDSA44.Emulated.honestAssignment`) and the digits of `w'`, of `z + 130993`, of the UseHint
offset and of the slack, in the bases and at the values of the program's digit layout
(`MldsaEAlgebra.layout`, `MldsaELayout`). The realization's values (the complement's digits, the
signature relation's quotient digits, the histograms) are generated (`GordieHowe.RealizedProgram.genCommitted`). With the
readings at the source environment (`rdA_honest`, the environment read as the native program's:
`readsCells_honest`), a value bound to its digits reading its honest natural
(`evalE_expr_of_digits`) and domain `A`'s predicates at the honest values.

The two emulated programs share the value and predicate identifiers outside the layout and differ
in their fields, the MAC's width, the radix of its digits and the layout. The program facts the
honest strategy reads are the class `MldsaEmulatedHonest`, decided per program.
-/

namespace GordieHowe.MLDSA44.Emulated

open GordieHowe.Bits RealizedProgram
open MLDSA44 (HonestInput)
open Native.ROMParams (hVal MldsaHHash MldsaHSample MldsaHConsts MldsaHHonest MldsaHShuffle MldsaHSelHonest MldsaHNativeData MldsaHNodes)

/-- **Domain `A`'s committed values** of a layout: the hint, the challenge bits, the UseHint output
bits and signs, and the layout's digits of `w'`, of `z + 130993`, of the offset and of the slack. -/
def aValues (L : MldsaELayout) : List ℕ := [60, 61, 64, 65] ++ (L).digitValues

/-- **The MAC's predicates**: `mac.A` (the accumulator row), the lower digit's and the top digit's
ranges, the no-wrap check, the tail `mac`. -/
def macRolePreds : List ℕ := [3, 16, 17, 18, 273]

/-! ## The layout's values are distinct -/

section Distinct

variable {L : MldsaELayout} (h : (aValues L).Nodup)
include h

theorem nodup_digitValues : (L).digitValues.Nodup := (List.nodup_append.1 h).2.1

theorem fixed_not_mem {u v : ℕ} (hu : u ∈ [60, 61, 64, 65]) (hv : v ∈ (L).digitValues) : v ≠ u :=
  fun e => (List.nodup_append.1 h).2.2 u hu v hv e.symm

theorem w_nodup : (L).w.ids.Nodup := by
  have := nodup_digitValues h
  unfold MldsaELayout.digitValues at this
  exact (List.nodup_append.1 (List.nodup_append.1 (List.nodup_append.1 this).1).1).1

theorem z_nodup : (L).z.ids.Nodup := by
  have := nodup_digitValues h
  unfold MldsaELayout.digitValues at this
  exact (List.nodup_append.1 (List.nodup_append.1 (List.nodup_append.1 this).1).1).2.1

theorem offset_nodup : (L).offset.ids.Nodup := by
  have := nodup_digitValues h
  unfold MldsaELayout.digitValues at this
  exact (List.nodup_append.1 (List.nodup_append.1 this).1).2.1

theorem slack_nodup : (L).slack.ids.Nodup := by
  have := nodup_digitValues h
  unfold MldsaELayout.digitValues at this
  exact (List.nodup_append.1 this).2.1

theorem z_not_w {v : ℕ} (hv : v ∈ (L).z.ids) : v ∉ (L).w.ids := fun hw => by
  have := nodup_digitValues h
  unfold MldsaELayout.digitValues at this
  exact (List.nodup_append.1 (List.nodup_append.1 (List.nodup_append.1 this).1).1).2.2 v hw v hv rfl

theorem offset_not_wz {v : ℕ} (hv : v ∈ (L).offset.ids) : v ∉ (L).w.ids ∧ v ∉ (L).z.ids := by
  have := nodup_digitValues h
  unfold MldsaELayout.digitValues at this
  have h3 := (List.nodup_append.1 (List.nodup_append.1 this).1).2.2
  exact ⟨fun hw => h3 v (List.mem_append_left _ hw) v hv rfl,
    fun hz => h3 v (List.mem_append_right _ hz) v hv rfl⟩

theorem slack_not_wzo {v : ℕ} (hv : v ∈ (L).slack.ids) :
    v ∉ (L).w.ids ∧ v ∉ (L).z.ids ∧ v ∉ (L).offset.ids := by
  have := nodup_digitValues h
  unfold MldsaELayout.digitValues at this
  have h4 := (List.nodup_append.1 this).2.2
  exact ⟨fun hw => h4 v (List.mem_append_left _ (List.mem_append_left _ hw)) v hv rfl,
    fun hz => h4 v (List.mem_append_left _ (List.mem_append_right _ hz)) v hv rfl,
    fun ho => h4 v (List.mem_append_right _ ho) v hv rfl⟩

end Distinct

theorem w_mem_digitValues {L : MldsaELayout} {v : ℕ} (hv : v ∈ (L).w.ids) : v ∈ (L).digitValues := by
  unfold MldsaELayout.digitValues
  simp [hv]

theorem z_mem_digitValues {L : MldsaELayout} {v : ℕ} (hv : v ∈ (L).z.ids) : v ∈ (L).digitValues := by
  unfold MldsaELayout.digitValues
  simp [hv]

theorem offset_mem_digitValues {L : MldsaELayout} {v : ℕ} (hv : v ∈ (L).offset.ids) :
    v ∈ (L).digitValues := by
  unfold MldsaELayout.digitValues
  simp [hv]

theorem slack_mem_digitValues {L : MldsaELayout} {v : ℕ} (hv : v ∈ (L).slack.ids) :
    v ∈ (L).digitValues := by
  unfold MldsaELayout.digitValues
  simp [hv]

theorem mem_aValues_of_digit {L : MldsaELayout} {v : ℕ} (hv : v ∈ (L).digitValues) :
    v ∈ aValues L :=
  List.mem_append_right _ hv

theorem fixed_mem_aValues {L : MldsaELayout} {v : ℕ} (hv : v ∈ [60, 61, 64, 65]) :
    v ∈ aValues L :=
  List.mem_append_left _ hv

set_option linter.unusedSectionVars false

set_option hygiene false in
local notation "interp" => mldsaInterpOf F0 FH

set_option hygiene false in
local notation "nat" => MldsaEmbed.nat program

set_option hygiene false in
local notation "L" => MldsaEAlgebra.layout program

/-- **The program facts of an emulated ML-DSA program's honest strategy** (each program
instantiates them by `decide`): the statement of a key (`stmtOfKey`) with what the honest prover
reads of it, the transfer of domain `H`'s committed values from the embedded native program, the
kinds, sizes and classes of domain `A`'s values with the digit layout's (`MldsaEAlgebra.layout`)
values bound to its digits and room for the honest naturals, and the only cross-field `equal` the
MAC's. -/
class MldsaEmulatedHonest (program : RealizedProgram) [MldsaEAlgebra program] (F0 FH : outParam FieldInterp)
    where
  /-- The statement of a key. -/
  stmtOfKey : MLDSA44.PublicKey44 → program.Valuation interp
  /-- The realization's prime-subfield nodes. -/
  PN : ℕ → List String
  /-- Every value bound to its digits reads committed values and constants (`BoundOk`). -/
  bound : ∀ v < program.values.length, program.BoundOk v
  /-- The key's statement holds the key's preprocessing. -/
  keyOf : ∀ pk, KeyOf pk (stmtOfKey pk)
  /-- The key's statement holds the bits of `tr` at value `68`. -/
  stmt68 : ∀ pk, ∀ j (hj : j < 512), (castElt (b := 1) (stmtOfKey pk 68 j) : (interp 1).K) =
    constBit (MLDSA44.PoP.Compose.trOf pk ⟨j / 8, by omega⟩).toNat (j % 8)
  /-- Domain `H`'s committed cells are the native program's, one identifier higher. -/
  hCells : ∀ v < (nat).values.length, (nat).privCellB v = true → (nat).valueField v = 1 →
    v ∈ hV ∧ program.privCellB (v + 1) = true
  /-- Domain `A`'s committed values are distinct. -/
  a_nodup : (aValues L).Nodup
  /-- Domain `A`'s committed values are cells of field `0`. -/
  a_cells : ∀ v ∈ aValues L, program.privCellB v = true ∧ program.valueField v = 0
  /-- `z` is bound to its digits less the offset `130993`. -/
  kind59 : (program.value 59).kind =
    .bound (.add (L).z.expr (.scale (.const 18446744069414584320) (.leaf 63)))
  /-- `w'` is bound to its digits. -/
  kind62 : (program.value 62).kind = .bound (L).w.expr
  /-- The offset is bound to its digits. -/
  kind66 : (program.value 66).kind = .bound (L).offset.expr
  /-- The slack is bound to its digits. -/
  kind67 : (program.value 67).kind = .bound (L).slack.expr
  /-- The bound values of domain `A` are values of field `0`. -/
  boundVals : ∀ v ∈ [59, 62, 66, 67], v < program.values.length ∧ program.valueField v = 0
  /-- The digits have one coordinate per coefficient. -/
  digitSizes : ∀ v ∈ (L).digitValues, (program.value v).size = 1024
  /-- The hint has `1024` coordinates. -/
  size60 : (program.value 60).size = 1024
  /-- The challenge bits have `512` coordinates. -/
  size61 : (program.value 61).size = 512
  /-- The UseHint output bits have `6144` coordinates. -/
  size64 : (program.value 64).size = 6144
  /-- The signs have `1024` coordinates. -/
  size65 : (program.value 65).size = 1024
  /-- `w'`'s digits hold every natural below `q`. -/
  wFits : (L).w.Fits 8380417
  /-- `z + 130993`'s digits hold every natural below `261987`. -/
  zFits : (L).z.Fits 261987
  /-- The offset's digits hold every natural up to `γ₂`. -/
  offsetFits : (L).offset.Fits 95233
  /-- The slack's digits hold every natural up to `γ₂`. -/
  slackFits : (L).slack.Fits 95233
  /-- The offset's and the slack's bound lies above `γ₂`. -/
  offsetRoom : 95232 < (L).offsetBound
  /-- The MAC with its digit tail. -/
  mac : program.DigitsMac PN
  /-- The MAC's width. -/
  macW : ℕ
  /-- The program is well formed. -/
  wellFormed : program.WellFormed
  /-- The interpretation's registry. -/
  registered : (interp).Registered program
  /-- The interpretation's integer readings. -/
  lawful : (interp).Lawful program PN
  /-- The MAC model. -/
  macModel : (interp).MacModel program
  /-- The honest statements lie within the declared bounds. -/
  bounded : ∀ i : HonestInput, program.StmtBounded interp (stmtOfKey i.y.key)
  /-- The statement has no member checks. -/
  checks : program.statement.checks = []
  /-- The realization's predicates outside the MAC's are no source predicates. -/
  realPreds : ∀ q ∈ [4, 5, 10, 19], program.inSource (program.predicate q) = false
  /-- The blind's cells. -/
  blind_cells : (program.value 569).kind = .padCopy 572 "polynomialBits" ∧
    (program.value 569).domain < program.domains.length ∧
    (∀ j < macW, CellKey.val 569 j ∈ program.cellKeys (program.value 569).domain) ∧
    program.valueField 569 = 0 ∧ (program.value 569).size = macW
  /-- The program has `276` predicates. -/
  predicates_length : program.predicates.length = 276
  /-- The A operand of the crossing has `6656` coordinates. -/
  len6 : program.exprLen (.ref 6) = 6656
  /-- The bits the A operand reads. -/
  cross_vals : program.isConstant 64 = false ∧ program.isConstant 61 = false ∧
    program.valueField 64 = 0 ∧ program.valueField 61 = 0
  /-- `mac.equal` is predicate `275`, the MAC's. -/
  hb : (program.predicate 275).body = .cross 1 (.ref 527) 0 (.ref 6) {} mac.real
  /-- The MAC crosses `ref 527` of domain `H` and `ref 6` of domain `A`. -/
  mac_shape : mac.dx = 1 ∧ mac.x = Expr.ref 527 ∧ mac.dy = 0 ∧ mac.y = Expr.ref 6 ∧ mac.k = {} ∧
    mac.cdy = 0 ∧ mac.cy = Expr.ref 6
  /-- The only cross-field `equal` is the MAC's. -/
  crossMac : ∀ p ∈ program.predicates, ∀ dx x dy y k real, p.body = .cross dx x dy y k real →
    (program.predicate mac.pid).body = p.body
  /-- The committed values' classes. -/
  cell_classes : (List.range program.values.length).all (fun v =>
    !program.isCellValue (program.value v).domain v || !decide (program.IsSourceValue v) ||
      (program.valueField v == 1 && (program.value v).node.map (·.name) == some "GF(2^16)" &&
        decide (1 ≤ v) && decide (v - 1 ∈ hV) &&
        ((Native.ROMParams.wordsOwner? (v - 1)).isSome ||
          [70, 120, 558, 561, 563, 564, 565, 566].contains (v - 1))) ||
      (program.valueField v == 1 && (program.value v).node.map (·.name) == some "bit" &&
        decide (1 ≤ v) && decide (v - 1 ∈ hV) && [68, 69, 557, 562].contains (v - 1)) ||
      (program.valueField v == 0 && (program.value v).node.map (·.name) == some "GF(p^1)" &&
        ((aValues L).contains v || v == 569))) = true
  /-- Only the blind is a pad copy. -/
  padCopy_only : (List.range program.values.length).all (fun w => w == 569 ||
    match (program.value w).kind with
    | .padCopy _ _ => false
    | _ => true) = true
  /-- The node-typed values that are not late. -/
  typed_classes : (List.range program.values.length).all (fun v =>
    !((program.value v).typeSource == .node) || decide (program.IsLate v) ||
      ((match (program.value v).kind with
        | .bits w _ => (match (program.value w).kind with
          | .priv => true
          | _ => false)
        | _ => false) && (program.value v).type == .bit) ||
      (program.privCellB v && program.isCellValue (program.value v).domain v &&
        (match (program.value v).type with
          | .sub S => (program.value v).node.map (·.name) == some S
          | .bit => (program.value v).node.map (·.name) == some "bit" && program.valueField v == 1
          | .field => true))) = true

variable {program : RealizedProgram} [MldsaEAlgebra program] {F0 FH : FieldInterp} [AField F0]
  [HField FH] [MldsaHHonest nat] [MldsaHSample nat] [MldsaHSelHonest nat]
  [MldsaHConsts nat FH] [Native.ROMParams.MldsaHNativeData FH] [MldsaHNodes FH]
  [hE : MldsaEmulatedHonest program F0 FH]

open MldsaEmulatedHonest

/-! ## A value bound to its digits -/

section Digits

omit hE

/-- **The digits' sum from position `t` on reads its terms** in domain `A`. -/
theorem evalE_exprFrom (rd : program.Valuation interp) (b j : ℕ) :
    ∀ (t : ℕ) (acc : Expr) (ds : List ℕ), program.evalE rd 0 (DigitLayout.exprFrom b t acc ds) j =
      program.evalE rd 0 acc j + ∑ s ∈ Finset.range ds.length,
        ((b ^ (t + s) : ℕ) : (interp 0).K) * program.evalE rd 0 (.leaf (ds.getD s 0)) j
  | t, acc, [] => by simp
  | t, acc, d :: ds => by
    rw [DigitLayout.exprFrom_cons, evalE_exprFrom rd b j (t + 1), List.length_cons,
      Finset.sum_range_succ', evalE_add, evalE_scaleA]
    have hs : ∑ s ∈ Finset.range ds.length, ((b ^ (t + (s + 1)) : ℕ) : (interp 0).K) *
        program.evalE rd 0 (.leaf ((d :: ds).getD (s + 1) 0)) j =
        ∑ s ∈ Finset.range ds.length, ((b ^ (t + 1 + s) : ℕ) : (interp 0).K) *
          program.evalE rd 0 (.leaf (ds.getD s 0)) j :=
      Finset.sum_congr rfl fun s _ => by
        rw [List.getD_cons_succ, show t + (s + 1) = t + 1 + s by omega]
    rw [hs, List.getD_cons_zero, Nat.add_zero]
    ring

/-- **A value bound to digits reads the natural they hold**: where digit `s` reads digit `s` of a
natural `n` the digits hold, the digits' expression reads `n`. -/
theorem evalE_expr_of_digits {D : DigitLayout} {n N : ℕ} (hD : D.Fits N) (hn : n < N)
    (rd : program.Valuation interp) (j : ℕ)
    (h : ∀ s (hs : s < D.ids.length), program.evalE rd 0 (.leaf D.ids[s]) j =
      (DigitLayout.digitAt D.base n s : (interp 0).K)) :
    program.evalE rd 0 D.expr j = (n : (interp 0).K) := by
  obtain ⟨b, _ | ⟨d, ds⟩⟩ := D
  · exact absurd rfl hD.ne
  have hlt : n < b ^ (ds.length + 1) := lt_trans hn hD.le
  have h' : ∀ s < ds.length + 1, program.evalE rd 0 (.leaf ((d :: ds).getD s 0)) j =
      (DigitLayout.digitAt b n s : (interp 0).K) := fun s hs => by
    rw [List.getD_eq_getElem _ _ (by simpa using hs)]
    exact h s (by simpa using hs)
  have hn' : (n : (interp 0).K) =
      ((∑ s ∈ Finset.range (ds.length + 1), b ^ s * DigitLayout.digitAt b n s : ℕ) :
        (interp 0).K) := by
    rw [DigitLayout.sum_digitAt, Nat.mod_eq_of_lt hlt]
  have h0 := h' 0 (by omega)
  rw [List.getD_cons_zero] at h0
  rw [DigitLayout.expr_cons, evalE_exprFrom, hn', Finset.sum_range_succ', Nat.cast_add,
    Nat.cast_sum, h0, add_comm]
  congr 1
  · refine Finset.sum_congr rfl fun s hs => ?_
    have := h' (s + 1) (by simp only [Finset.mem_range] at hs; omega)
    rw [List.getD_cons_succ] at this
    rw [this, Nat.cast_mul, Nat.add_comm 1 s]
  · simp

end Digits

/-! ## Domain `A`'s honest naturals -/

variable (F0) in
/-- **`Emulated`'s honest assignment** of an honest input (domain `A`'s honest values, in
domain `A`'s field; its domain-`H` part is read at `GF(2^128)` and unused). -/
-- spec-side
noncomputable abbrev nativeE (i : HonestInput) :=
  Emulated.honestAssignment (KH := GF2_128) (F := F0.K) gf2_128PackedBasis i.y

/-- **The flat index** `m < 1024` of a coefficient `(i, k)` of a `4 × 256` value. -/
def fm (j : ℕ) (h : j < 1024) : Fin (Native.Rows.nRows * Native.Rows.deg) := ⟨j, h⟩

/-- **The flat index** `m < 1024` of a coefficient `(j, k)` of `z`. -/
def fmz (j : ℕ) (h : j < 1024) : Fin (Native.Rows.nCols * Native.Rows.deg) := ⟨j, h⟩

/-- **The honest `w'`** of coefficient `m`: its canonical representative below `q`. -/
-- spec-side
noncomputable def wN (i : HonestInput) (m : Fin (Native.Rows.nRows * Native.Rows.deg)) : ℕ :=
  NativeAlgebraCircuit.flat (Emulated.honestWNat i.y) m

/-- **The honest shifted `z`** of coefficient `m`: `z + 130993`. -/
-- spec-side
def zN (i : HonestInput) (m : Fin (Native.Rows.nCols * Native.Rows.deg)) : ℕ :=
  NativeAlgebraCircuit.flat (Emulated.honestZNat i.y) m

/-- **The honest UseHint offset** of coefficient `m`, as `Emulated`'s honest assignment commits
it: its digit of base `2^24` (`UseHint.honest`). -/
-- spec-side
noncomputable def offN (i : HonestInput) (m : Fin (Native.Rows.nRows * Native.Rows.deg)) : ℕ :=
  NativeAlgebraCircuit.flat (fun a b => GordieHowe.MLDSA44.useHintOffset mldsa44.γ₂
    (NativeAlgebraCircuit.Honest.hintBool i.y.h a b) (NativeAlgebraCircuit.Honest.wCoeff i.y.key i.y.c i.y.z a b) /
      Emulated.Params.wBound ^ ((0 : Fin 1) : ℕ) % Emulated.Params.wBound) m

/-- **The honest UseHint slack** of coefficient `m`, as `Emulated`'s honest assignment
commits it. -/
-- spec-side
noncomputable def slN (i : HonestInput) (m : Fin (Native.Rows.nRows * Native.Rows.deg)) : ℕ :=
  NativeAlgebraCircuit.flat (fun a b =>
    (mldsa44.γ₂ - 1 + GordieHowe.MLDSA44.useHintEndpoint (UseHint.hiCount mldsa44.γ₂)
      (NativeAlgebraCircuit.Honest.hintBool i.y.h a b)
      (GordieHowe.MLDSA44.useHintSign mldsa44.γ₂ (NativeAlgebraCircuit.Honest.wCoeff i.y.key i.y.c i.y.z a b))
      (_root_.MLDSA.Concrete.useHintCoeff (NativeAlgebraCircuit.Honest.hintBool i.y.h a b)
        (NativeAlgebraCircuit.Honest.wCoeff i.y.key i.y.c i.y.z a b) mldsa44.γ₂) -
      GordieHowe.MLDSA44.useHintOffset mldsa44.γ₂ (NativeAlgebraCircuit.Honest.hintBool i.y.h a b)
        (NativeAlgebraCircuit.Honest.wCoeff i.y.key i.y.c i.y.z a b)) /
      Emulated.Params.wBound ^ ((0 : Fin 1) : ℕ) % Emulated.Params.wBound) m

/-- **The honest hint weight**: the number of set hint bits. -/
-- spec-side
def wtN (i : HonestInput) : ℕ :=
  ∑ m : Fin (Native.Rows.nRows * Native.Rows.deg),
    (NativeAlgebraCircuit.flat (NativeAlgebraCircuit.Honest.hintBool i.y.h) m).toNat

variable (F0) in
/-- **Domain `A`'s honest values** (in domain `A`'s field) at a digit layout: the hint (`60`), the
challenge bits (`61`), the UseHint output bits (`64`) and signs (`65`) of `Emulated`'s
honest assignment; the layout's digits (`DigitLayout.digit`) of `w'`, of `z + 130993`, of the
offset and of the slack; `0` elsewhere (the realization's values are generated, `RealizedProgram.genCommitted`).

Running time: a prover computing these values would take the time of `Emulated`'s honest
assignment and one digit per coordinate. This running time is argued here, not proved in Lean. -/
-- spec-side
noncomputable def aVal (L' : MldsaELayout) (i : HonestInput) (v j : ℕ) : F0.K :=
  if v = 61 then
    (if h : j < 512 then (nativeE F0 i).cA ⟨j / 2, by change j / 2 < 256; omega⟩ ⟨j % 2, by omega⟩
      else 0)
  else if v = 64 then
    (if h : j < 6144 then NativeAlgebraCircuit.outputBits (nativeE F0 i).w1A
      ⟨j / 6, by change j / 6 < 4 * 256; omega⟩ ⟨j % 6, by change j % 6 < 6; omega⟩ else 0)
  else if h : j < 1024 then
    if v = 60 then NativeAlgebraCircuit.flat (nativeE F0 i).h (fm j h)
    else if v = 65 then NativeAlgebraCircuit.flat (nativeE F0 i).np (fm j h)
    else if v ∈ L'.w.ids then ((L'.w.digit (wN i (fm j h)) v : ℕ) : F0.K)
    else if v ∈ L'.z.ids then ((L'.z.digit (zN i (fmz j h)) v : ℕ) : F0.K)
    else if v ∈ L'.offset.ids then ((L'.offset.digit (offN i (fm j h)) v : ℕ) : F0.K)
    else if v ∈ L'.slack.ids then ((L'.slack.digit (slN i (fm j h)) v : ℕ) : F0.K)
    else 0
  else 0

variable (program F0 FH) in
/-- **The honest committed values of an emulated program** on an honest input: domain `A`'s
values (`aVal` at the program's layout) and domain `H`'s, the native program's (`hVal`) one
identifier lower.

Running time: a prover computing these values would take the time of `hVal` and of `aVal`.
This running time is argued here, not proved in Lean. -/
-- spec-side
noncomputable def honestVal (i : HonestInput) (v j : ℕ) : (interp (program.valueField v)).K :=
  if v ∈ aValues L then castElt (a := 0) (aVal F0 L i v j)
  else if 1 ≤ v ∧ v - 1 ∈ hV then castElt (hVal nat F0 FH i (v - 1) j)
  else 0

/-! ## The honest values by class -/

section Classes

variable (i : HonestInput)

theorem honestVal_a : ∀ v, v ∈ aValues L → ∀ n,
    castElt (b := 0) (honestVal program F0 FH i v n) = aVal F0 L i v n := by
  intro v hv n
  unfold honestVal
  rw [if_pos hv]
  exact castElt_castElt_of_eq (a_cells (program := program) v hv).2.symm _

/-- **The environment read as the native program's reads domain `H`'s honest values**
(`Emulated.reader_pull`). -/
theorem readsCells_honest (x : program.Valuation interp) (c : ∀ k, (program.layout interp).Ch k)
    (π : (program.layout interp).Pads) :
    (nat).ReadsCells 1 (pull (program.srcEnv interp x (honestVal program F0 FH i) c π))
      (hVal nat F0 FH i) := fun v j hp hf hj => by
  have hl : v < (nat).values.length := by
    unfold RealizedProgram.privCellB at hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    exact hp.1.1.2
  obtain ⟨hvV, hp'⟩ := hCells (program := program) v hl hp hf
  obtain ⟨-, -, hfE, hsz, -⟩ := (MldsaEmbed.embedding (program := program)).vals v hvV
  have hfE' : program.valueField (v + 1) = (nat).valueField v := hfE
  have hsz' : (program.value (v + 1)).size = ((nat).value v).size := hsz
  have hnA : v + 1 ∉ aValues L := fun h => by
    have := (a_cells (program := program) (v + 1) h).2
    omega
  rw [reader_pull _ hvV, RealizedProgram.reader_srcEnv_of_privCellB x _ c π hp' (by rw [hsz']; exact hj)]
  unfold honestVal
  rw [if_neg hnA, if_pos ⟨by omega, by simpa using hvV⟩]
  rw [castElt_castElt_eq]
  simp only [Nat.add_sub_cancel]
  rw [if_pos hfE'.symm]
  exact castElt_self _

end Classes

/-! ## `aVal` at each value -/

section Access

variable (L' : MldsaELayout) (i : HonestInput) {j : ℕ}

theorem aVal_60 (h : j < 1024) :
    aVal F0 L' i 60 j = NativeAlgebraCircuit.flat (nativeE F0 i).h (fm j h) := by
  unfold aVal
  simp only [show (60 : ℕ) ≠ 61 by decide, show (60 : ℕ) ≠ 64 by decide,
    if_false, dif_pos h, if_true]

theorem aVal_65 (h : j < 1024) :
    aVal F0 L' i 65 j = NativeAlgebraCircuit.flat (nativeE F0 i).np (fm j h) := by
  unfold aVal
  simp only [show (65 : ℕ) ≠ 61 by decide, show (65 : ℕ) ≠ 64 by decide,
    show (65 : ℕ) ≠ 60 by decide,
    if_false, dif_pos h, if_true]

theorem aVal_61 (h : j < 512) : aVal F0 L' i 61 j =
    (nativeE F0 i).cA ⟨j / 2, by change j / 2 < 256; omega⟩ ⟨j % 2, by omega⟩ := by
  unfold aVal
  rw [if_pos rfl]
  exact dif_pos h

theorem aVal_64 (h : j < 6144) : aVal F0 L' i 64 j = NativeAlgebraCircuit.outputBits (nativeE F0 i).w1A
    ⟨j / 6, by change j / 6 < 4 * 256; omega⟩ ⟨j % 6, by change j % 6 < 6; omega⟩ := by
  unfold aVal
  rw [if_neg (by decide), if_pos rfl]
  exact dif_pos h

variable {L'} (hnd : (aValues L').Nodup)
include hnd

/-- A digit value of the layout is none of the fixed values. -/
theorem aVal_digit_ne {v : ℕ} (hv : v ∈ L'.digitValues) :
    v ≠ 61 ∧ v ≠ 64 ∧ v ≠ 60 ∧ v ≠ 65 :=
  ⟨fixed_not_mem hnd (by simp) hv, fixed_not_mem hnd (by simp) hv,
    fixed_not_mem hnd (by simp) hv, fixed_not_mem hnd (by simp) hv⟩

/-- **`w'`'s digit `s`** reads digit `s` of the honest `w'`. -/
theorem aVal_w {s : ℕ} (hs : s < L'.w.ids.length) (h : j < 1024) :
    aVal F0 L' i L'.w.ids[s] j =
      ((DigitLayout.digitAt L'.w.base (wN i (fm j h)) s : ℕ) : F0.K) := by
  have hv := List.getElem_mem hs
  obtain ⟨h1, h2, h3, h4⟩ := aVal_digit_ne hnd (w_mem_digitValues hv)
  unfold aVal
  rw [if_neg h1, if_neg h2, dif_pos h, if_neg h3, if_neg h4, if_pos hv,
    DigitLayout.digit_getElem (w_nodup hnd)]

/-- **`z + 130993`'s digit `s`** reads digit `s` of the honest shifted `z`. -/
theorem aVal_z {s : ℕ} (hs : s < L'.z.ids.length) (h : j < 1024) :
    aVal F0 L' i L'.z.ids[s] j =
      ((DigitLayout.digitAt L'.z.base (zN i (fmz j h)) s : ℕ) : F0.K) := by
  have hv := List.getElem_mem hs
  obtain ⟨h1, h2, h3, h4⟩ := aVal_digit_ne hnd (z_mem_digitValues hv)
  unfold aVal
  rw [if_neg h1, if_neg h2, dif_pos h, if_neg h3, if_neg h4, if_neg (z_not_w hnd hv), if_pos hv,
    DigitLayout.digit_getElem (z_nodup hnd)]

/-- **The offset's digit `s`** reads digit `s` of the honest offset. -/
theorem aVal_offset {s : ℕ} (hs : s < L'.offset.ids.length) (h : j < 1024) :
    aVal F0 L' i L'.offset.ids[s] j =
      ((DigitLayout.digitAt L'.offset.base (offN i (fm j h)) s : ℕ) : F0.K) := by
  have hv := List.getElem_mem hs
  obtain ⟨h1, h2, h3, h4⟩ := aVal_digit_ne hnd (offset_mem_digitValues hv)
  obtain ⟨hw, hz⟩ := offset_not_wz hnd hv
  unfold aVal
  rw [if_neg h1, if_neg h2, dif_pos h, if_neg h3, if_neg h4, if_neg hw, if_neg hz, if_pos hv,
    DigitLayout.digit_getElem (offset_nodup hnd)]

/-- **The slack's digit `s`** reads digit `s` of the honest slack. -/
theorem aVal_slack {s : ℕ} (hs : s < L'.slack.ids.length) (h : j < 1024) :
    aVal F0 L' i L'.slack.ids[s] j =
      ((DigitLayout.digitAt L'.slack.base (slN i (fm j h)) s : ℕ) : F0.K) := by
  have hv := List.getElem_mem hs
  obtain ⟨h1, h2, h3, h4⟩ := aVal_digit_ne hnd (slack_mem_digitValues hv)
  obtain ⟨hw, hz, ho⟩ := slack_not_wzo hnd hv
  unfold aVal
  rw [if_neg h1, if_neg h2, dif_pos h, if_neg h3, if_neg h4, if_neg hw, if_neg hz, if_neg ho,
    if_pos hv, DigitLayout.digit_getElem (slack_nodup hnd)]

/-- **A digit of the layout is a natural's cast.** -/
theorem aVal_digit_natCast {v : ℕ} (hv : v ∈ L'.digitValues) (h : j < 1024) :
    ∃ k : ℕ, aVal F0 L' i v j = (k : F0.K) := by
  obtain ⟨h1, h2, h3, h4⟩ := aVal_digit_ne hnd hv
  unfold aVal
  rw [if_neg h1, if_neg h2, dif_pos h, if_neg h3, if_neg h4]
  split_ifs
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨0, by simp⟩

end Access

/-! ## Facts about the honest naturals -/

section Nats

variable (i : HonestInput)

theorem wN_lt (m : Fin (Native.Rows.nRows * Native.Rows.deg)) : wN i m < 8380417 := by
  unfold wN NativeAlgebraCircuit.flat Emulated.honestWNat
  exact ZMod.val_lt _

theorem zN_lt (m : Fin (Native.Rows.nCols * Native.Rows.deg)) : zN i m < 261987 := by
  unfold zN NativeAlgebraCircuit.flat
  exact Emulated.honestZNat_lt i.valid _ _

theorem zN_cast (m : Fin (Native.Rows.nCols * Native.Rows.deg)) :
    ((zN i m : ℕ) : F0.K) = ((NativeAlgebraCircuit.flat (NativeAlgebraCircuit.Honest.zCentered i.y.z) m : ℤ) : F0.K) +
      ((130993 : ℕ) : F0.K) := by
  unfold zN NativeAlgebraCircuit.flat
  rw [← Int.cast_natCast, Emulated.honestZNat_cast i.valid]
  push_cast
  rfl

theorem offN_slN_le (m : Fin (Native.Rows.nRows * Native.Rows.deg)) :
    offN i m ≤ 95232 ∧ slN i m ≤ 95232 := by
  unfold offN slN NativeAlgebraCircuit.flat
  dsimp only
  have h := (GordieHowe.MLDSA44.useHintRelation_honest (γ₂ := mldsa44.γ₂) (by decide) (by decide)
    (NativeAlgebraCircuit.Honest.hintBool i.y.h (finProdFinEquiv.symm m).1 (finProdFinEquiv.symm m).2)
    (NativeAlgebraCircuit.Honest.wCoeff i.y.key i.y.c i.y.z (finProdFinEquiv.symm m).1
      (finProdFinEquiv.symm m).2)).1
  have hE := GordieHowe.MLDSA44.useHintEndpoint_le_one (UseHint.hiCount mldsa44.γ₂)
    (NativeAlgebraCircuit.Honest.hintBool i.y.h (finProdFinEquiv.symm m).1 (finProdFinEquiv.symm m).2)
    (GordieHowe.MLDSA44.useHintSign mldsa44.γ₂ (NativeAlgebraCircuit.Honest.wCoeff i.y.key i.y.c i.y.z
      (finProdFinEquiv.symm m).1 (finProdFinEquiv.symm m).2))
    (_root_.MLDSA.Concrete.useHintCoeff
      (NativeAlgebraCircuit.Honest.hintBool i.y.h (finProdFinEquiv.symm m).1 (finProdFinEquiv.symm m).2)
      (NativeAlgebraCircuit.Honest.wCoeff i.y.key i.y.c i.y.z (finProdFinEquiv.symm m).1
        (finProdFinEquiv.symm m).2) mldsa44.γ₂)
  have hγ : mldsa44.γ₂ = 95232 := rfl
  have hM : UseHint.hiCount mldsa44.γ₂ = (_root_.MLDSA.modulus - 1) / (2 * mldsa44.γ₂) := rfl
  rw [← hM] at h
  constructor
  · exact (Nat.mod_le _ _).trans (by simp only [Fin.val_zero, pow_zero, Nat.div_one]; omega)
  · exact (Nat.mod_le _ _).trans (by simp only [Fin.val_zero, pow_zero, Nat.div_one]; omega)

theorem wtN_le : wtN i ≤ 80 := by
  have h := NativeAlgebraCircuit.Honest.card_hintBool_le i.y.h (i.valid.checks.2.2)
  unfold wtN
  rw [Finset.card_filter] at h
  refine le_of_eq_of_le (Finset.sum_congr rfl fun m _ => ?_) h
  cases NativeAlgebraCircuit.flat (NativeAlgebraCircuit.Honest.hintBool i.y.h) m <;> rfl

end Nats

/-! ## Domain `A`'s readings at the source environment -/

section Readings

variable {i : HonestInput} {x : program.Valuation interp} {c : ∀ k, (program.layout interp).Ch k}
  {π : (program.layout interp).Pads}

/-- **A committed value of domain `A` reads its honest value** at the source environment. -/
theorem rdA_honest {v : ℕ} (hv : v ∈ aValues L) {j : ℕ} (hj : j < (program.value v).size) :
    rdA (program.srcEnv interp x (honestVal program F0 FH i) c π) v j = aVal F0 L i v j := by
  unfold rdA
  rw [evalE_leaf, reader_srcEnv_of_privCellB x _ c π (a_cells (program := program) v hv).1 hj]
  exact honestVal_a i v hv j

/-- **A fixed committed value of domain `A` reads its honest value** at the source environment. -/
theorem rdA_honest_fixed {v : ℕ} (hv : v ∈ [60, 61, 64, 65]) {j : ℕ}
    (hj : j < (program.value v).size) :
    rdA (program.srcEnv interp x (honestVal program F0 FH i) c π) v j = aVal F0 L i v j :=
  rdA_honest (fixed_mem_aValues hv) hj

/-- **A bound value of domain `A` reads its expression** at the source environment. -/
theorem rdA_bound {v : ℕ} {e : Expr} (hk : (program.value v).kind = .bound e)
    (hf : program.valueField v = 0) (hv : v < program.values.length) (j : ℕ) :
    rdA (program.srcEnv interp x (honestVal program F0 FH i) c π) v j =
      program.evalE (program.reader (program.srcEnv interp x (honestVal program F0 FH i) c π)) 0
        e j := by
  unfold rdA
  rw [evalE_leaf, reader_bindAsg_of_boundOk (bound (program := program)) rfl hv hk]
  revert hf
  generalize program.valueField v = f
  intro hf
  subst hf
  rfl

set_option hygiene false in
local notation "E" => program.srcEnv interp x (honestVal program F0 FH i) c π

/-- **A digit of the layout reads its honest value** at the source environment. -/
theorem rdA_digit {v : ℕ} (hv : v ∈ (L).digitValues) {m : ℕ} (hm : m < 1024) :
    rdA E v m = aVal F0 L i v m :=
  rdA_honest (mem_aValues_of_digit hv) (by rw [digitSizes (program := program) v hv]; exact hm)

/-- **`w'` reads its honest natural.** -/
theorem rdA_62 {m : ℕ} (hm : m < 1024) : rdA E 62 m = ((wN i (fm m hm) : ℕ) : (interp 0).K) := by
  obtain ⟨hl, hf⟩ := boundVals (program := program) 62 (by simp)
  rw [rdA_bound kind62 hf hl]
  refine evalE_expr_of_digits wFits (wN_lt i _) _ m fun s hs => ?_
  exact (rdA_digit (w_mem_digitValues (List.getElem_mem hs)) hm).trans
    (aVal_w i a_nodup hs hm)

/-- **`z` reads its centered coefficient.** -/
theorem rdA_59 {m : ℕ} (hm : m < 1024) :
    rdA E 59 m = ((NativeAlgebraCircuit.flat (NativeAlgebraCircuit.Honest.zCentered i.y.z) (fmz m hm) : ℤ) :
      (interp 0).K) := by
  obtain ⟨hl, hf⟩ := boundVals (program := program) 59 (by simp)
  rw [rdA_bound kind59 hf hl, evalE_add, evalE_negA]
  have hz : program.evalE (program.reader E) 0 (L).z.expr m = ((zN i (fmz m hm) : ℕ) : (interp 0).K) :=
    evalE_expr_of_digits zFits (zN_lt i _) _ m fun s hs =>
      (rdA_digit (z_mem_digitValues (List.getElem_mem hs)) hm).trans (aVal_z i a_nodup hs hm)
  change _ + -rdA _ 63 m = _
  rw [hz, rdA_63 _ hm, zN_cast]
  ring

/-- **The offset reads its digits' sum.** -/
theorem rdA_66 {m : ℕ} (hm : m < 1024) :
    rdA E 66 m = ((offN i (fm m hm) : ℕ) : (interp 0).K) := by
  obtain ⟨hl, hf⟩ := boundVals (program := program) 66 (by simp)
  rw [rdA_bound kind66 hf hl]
  refine evalE_expr_of_digits offsetFits (Nat.lt_succ_of_le (offN_slN_le i _).1) _ m
    fun s hs => ?_
  exact (rdA_digit (offset_mem_digitValues (List.getElem_mem hs)) hm).trans
    (aVal_offset i a_nodup hs hm)

/-- **The slack reads its digits' sum.** -/
theorem rdA_67 {m : ℕ} (hm : m < 1024) :
    rdA E 67 m = ((slN i (fm m hm) : ℕ) : (interp 0).K) := by
  obtain ⟨hl, hf⟩ := boundVals (program := program) 67 (by simp)
  rw [rdA_bound kind67 hf hl]
  refine evalE_expr_of_digits slackFits (Nat.lt_succ_of_le (offN_slN_le i _).2) _ m
    fun s hs => ?_
  exact (rdA_digit (slack_mem_digitValues (List.getElem_mem hs)) hm).trans
    (aVal_slack i a_nodup hs hm)

/-- **The UseHint output bits read `Emulated`'s honest assignment's.** -/
theorem bitsA_honest {m : ℕ} (hm : m < 1024) :
    bitsA E m = NativeAlgebraCircuit.outputBits (nativeE F0 i).w1A (fm m hm) := by
  funext b
  have hb := b.isLt
  change (b : ℕ) < 6 at hb
  unfold bitsA
  rw [rdA_honest_fixed (i := i) (x := x) (c := c) (π := π) (by simp)
      (by rw [size64 (program := program)]; omega),
    aVal_64 _ i (by omega)]
  have e1 : (⟨(6 * m + b) / 6, by change (6 * m + b) / 6 < 4 * 256; omega⟩ :
      Fin (Native.Rows.nRows * Native.Rows.deg)) = fm m hm := Fin.ext (by simp only [fm]; omega)
  have e2 : (⟨(6 * m + b) % 6, by change (6 * m + b) % 6 < 6; omega⟩ : Fin mldsa44.r1_bits) = b :=
    Fin.ext (by simp only; omega)
  rw [e1, e2]

end Readings

/-! ## Domain `A`'s predicates at the honest values -/

section HoldsA

variable (i : HonestInput) {x : program.Valuation interp} {c : ∀ k, (program.layout interp).Ch k}
  {π : (program.layout interp).Pads}

/-- **`Emulated`'s honest algebra constraints** (`Emulated.algebraConstraints_honest`). -/
theorem nativeEC : Emulated.AlgebraConstraints i.y.key (nativeE F0 i) :=
  Emulated.algebraConstraints_honest (KH := GF2_128) (F := F0.K) (B := gf2_128PackedBasis)
    i.valid

set_option hygiene false in
local notation "E" => program.srcEnv interp x (honestVal program F0 FH i) c π

theorem w1Bits_bool : ∀ m < 1024, ∀ t < 6, rdA E 64 (6 * m + t) = 0 ∨ rdA E 64 (6 * m + t) = 1 :=
  fun m hm t ht => by
    have h := congrFun (bitsA_honest (i := i) (x := x) (c := c) (π := π) hm) ⟨t, ht⟩
    unfold bitsA at h
    rw [h]
    exact (nativeEC (F0 := F0) i).w1Bool _

theorem h60_bool : ∀ m < 1024, rdA E 60 m = 0 ∨ rdA E 60 m = 1 := fun m hm => by
  have h60 := size60 (program := program)
  rw [rdA_honest_fixed (i := i) (x := x) (c := c) (π := π) (by simp) (by rw [h60]; exact hm),
    aVal_60 _ i hm]
  exact (nativeEC (F0 := F0) i).hBool _ _

theorem h65_bool : ∀ m < 1024, rdA E 65 m = 0 ∨ rdA E 65 m = 1 := fun m hm => by
  have h65 := size65 (program := program)
  rw [rdA_honest_fixed (i := i) (x := x) (c := c) (π := π) (by simp) (by rw [h65]; exact hm),
    aVal_65 _ i hm]
  exact (nativeEC (F0 := F0) i).npBool _ _

theorem h61_bool : ∀ s < 512, rdA E 61 s = 0 ∨ rdA E 61 s = 1 := fun s hs => by
  have h61 := size61 (program := program)
  rw [rdA_honest_fixed (i := i) (x := x) (c := c) (π := π) (by simp) (by rw [h61]; exact hs),
    aVal_61 _ i hs]
  exact (nativeEC (F0 := F0) i).cBool _ _

theorem useHint_at {m : ℕ} (hm : m < 1024) :
    UseHint.WrapHolds mldsa44.γ₂ (rdA E 60 m) (rdA E 62 m) (rdA E 65 m) (rdA E 66 m) (rdA E 67 m)
      (bitsA E m) := by
  have h60 := size60 (program := program)
  have h65 := size65 (program := program)
  rw [rdA_honest_fixed (i := i) (x := x) (c := c) (π := π) (v := 60) (by simp) (by rw [h60]; exact hm),
    rdA_honest_fixed (i := i) (x := x) (c := c) (π := π) (v := 65) (by simp) (by rw [h65]; exact hm),
    rdA_62 hm, rdA_66 hm, rdA_67 hm, bitsA_honest hm, aVal_60 _ i hm, aVal_65 _ i hm]
  exact (nativeEC (F0 := F0) i).useHint (fm m hm)

/-- **`hint.w1_bound` holds** at the honest values. -/
theorem w1bound_honest : program.HoldsWith (program.reader E) (program.predicate 0).body :=
  w1bound0_of _ (w1Bits_bool i) fun _ hm => (useHint_at i hm).le

/-- **`hint.decompose` holds** at the honest values. -/
theorem decompose_honest : program.HoldsWith (program.reader E) (program.predicate 1).body :=
  decompose1_of (w1Bits_bool i) fun _ hm => (useHint_at i hm).wrap

theorem offset_nat : ∀ m < 1024, ∃ k : ℕ, k < (L).offsetBound ∧ rdA E 66 m = k :=
  fun m hm => ⟨_, by have := (offN_slN_le i (fm m hm)).1; have := offsetRoom (program := program); omega,
    rdA_66 hm⟩

theorem slack_nat : ∀ m < 1024, ∃ k : ℕ, k < (L).offsetBound ∧ rdA E 67 m = k :=
  fun m hm => ⟨_, by have := (offN_slN_le i (fm m hm)).2; have := offsetRoom (program := program); omega,
    rdA_67 hm⟩

/-- **`hint.interval` holds** at the honest values. -/
theorem interval_honest : program.HoldsWith (program.reader E) (program.predicate 2).body :=
  interval2_of _ (w1Bits_bool i) (h60_bool i) (h65_bool i) (offset_nat i) (slack_nat i)
    fun _ hm => (useHint_at i hm).interval

/-- **`hint.offset` holds** at the honest values. -/
theorem offset_honest : program.HoldsWith (program.reader E) (program.predicate 13).body :=
  offset13_of _ (offset_nat i)

/-- **`hint.slack` holds** at the honest values. -/
theorem slack_honest : program.HoldsWith (program.reader E) (program.predicate 14).body :=
  slack14_of _ (slack_nat i)

/-- **`signature.w` holds** at the honest values. -/
theorem w_honest : program.HoldsWith (program.reader E) (program.predicate 11).body :=
  w11_of _ fun m hm => ⟨_, by have := wN_lt i (fm m hm); omega, rdA_62 hm⟩

/-- **`norm.z` holds** at the honest values. -/
theorem norm_honest : program.HoldsWith (program.reader E) (program.predicate 12).body :=
  norm12_of _ fun m hm => ⟨zN i (fmz m hm), zN_lt i (fmz m hm), by
    rw [rdA_59 hm, zN_cast]⟩

/-- **`hint_weight.weight` holds** at the honest values. -/
theorem weight_honest : program.HoldsWith (program.reader E) (program.predicate 15).body := by
  have h60 := size60 (program := program)
  refine weight15_of _ ⟨wtN i, by have := wtN_le i; omega, ?_⟩
  unfold wtN
  rw [Nat.cast_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [rdA_honest_fixed (i := i) (x := x) (c := c) (π := π) (by simp) (by rw [h60]; exact t.isLt),
    aVal_60 _ i t.isLt]
  rfl

/-- **The type checks of `A` hold** at the honest values (`h`, `c`, `w1`, the signs). -/
theorem bools_honest {q : ℕ} (hq : q ∈ [6, 7, 8, 9]) :
    program.HoldsWith (program.reader E) (program.predicate q).body := by
  have h60 := size60 (program := program)
  have h61 := size61 (program := program)
  have h64 := size64 (program := program)
  have h65 := size65 (program := program)
  obtain ⟨b6, b7, b8, b9⟩ := boolChecks (program := program)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact boolA_of _ b6 fun j hj => h60_bool i j (h60 ▸ hj)
  · exact boolA_of _ b7 fun j hj => h61_bool i j (h61 ▸ hj)
  · refine boolA_of _ b8 fun j hj => ?_
    rw [h64] at hj
    have := w1Bits_bool i (x := x) (c := c) (π := π) (j / 6) (by omega) (j % 6) (by omega)
    rwa [Nat.div_add_mod] at this
  · exact boolA_of _ b9 fun j hj => h65_bool i j (h65 ▸ hj)

end HoldsA

/-! ## The signature relation at the honest values -/

section Sig

variable (i : HonestInput) {x : program.Valuation interp} {c : ∀ k, (program.layout interp).Ch k}
  {π : (program.layout interp).Pads}

set_option hygiene false in
local notation "E" => program.srcEnv interp x (honestVal program F0 FH i) c π

theorem flat_lt' (i' : Fin 4) (k : Fin 256) : (i' : ℕ) * 256 + k < 1024 := by
  have h1 := i'.isLt
  have h2 := k.isLt
  omega

theorem fm_eq (i' : Fin Native.Rows.nRows) (k : Fin Native.Rows.deg)
    (h : (i' : ℕ) * 256 + k < 1024) : fm ((i' : ℕ) * 256 + k) h = finProdFinEquiv (i', k) :=
  Fin.ext (by simp only [fm, finProdFinEquiv_apply_val, show Native.Rows.deg = 256 from rfl]; ring)

theorem fmz_eq (j : Fin Native.Rows.nCols) (k : Fin Native.Rows.deg)
    (h : (j : ℕ) * 256 + k < 1024) : fmz ((j : ℕ) * 256 + k) h = finProdFinEquiv (j, k) :=
  Fin.ext (by simp only [fmz, finProdFinEquiv_apply_val, show Native.Rows.deg = 256 from rfl]; ring)

/-- **`w'` reads `Emulated`'s honest assignment's** at coefficient `(i', k)`. -/
theorem rdA_62_native (i' : Fin Native.Rows.nRows) (k : Fin Native.Rows.deg) :
    rdA E 62 ((i' : ℕ) * 256 + k) = (nativeE F0 i).w i' k := by
  rw [rdA_62 (m := (i' : ℕ) * 256 + k) (flat_lt' i' k), wN, fm_eq i' k (flat_lt' i' k),
    NativeAlgebraCircuit.flat_apply]
  rfl

/-- **`z` reads `Emulated`'s honest assignment's** at coefficient `(j, k)`. -/
theorem rdA_59_native (j : Fin Native.Rows.nCols) (k : Fin Native.Rows.deg) :
    rdA E 59 ((j : ℕ) * 256 + k) = (nativeE F0 i).z j k := by
  rw [rdA_59 (m := (j : ℕ) * 256 + k) (flat_lt' j k), fmz_eq j k (flat_lt' j k),
    NativeAlgebraCircuit.flat_apply]
  rfl

/-- **The challenge bits read `Emulated`'s honest assignment's.** -/
theorem rdA_61_native (k : Fin Native.Rows.deg) (t : Fin 2) :
    rdA E 61 (2 * k + t) = (nativeE F0 i).cA k t := by
  have h61 := size61 (program := program)
  have hk := k.isLt
  have ht := t.isLt
  rw [rdA_honest_fixed (i := i) (x := x) (c := c) (π := π) (by simp)
      (by rw [h61]; change 2 * (k : ℕ) + t < 512; change (k : ℕ) < 256 at hk; omega),
    aVal_61 _ i (by change 2 * (k : ℕ) + t < 512; change (k : ℕ) < 256 at hk; omega)]
  congr 1
  · exact Fin.ext (by simp only; change (k : ℕ) < 256 at hk; omega)
  · exact Fin.ext (by simp only; change (k : ℕ) < 256 at hk; omega)

omit [MldsaHHonest nat] [MldsaHSample nat] [MldsaHSelHonest nat] [MldsaHConsts nat FH]
  [Native.ROMParams.MldsaHNativeData FH] [MldsaHNodes FH] hE in
theorem toNatE_zero : (interp 0).toNat (0 : (interp 0).K) = 0 := by
  have := toNat_gold_natCast (F0 := F0) (FH := FH) (k := 0) (by norm_num [pGold])
  simpa using this

omit [MldsaHHonest nat] [MldsaHSample nat] [MldsaHSelHonest nat] [MldsaHConsts nat FH]
  [Native.ROMParams.MldsaHNativeData FH] [MldsaHNodes FH] hE in
theorem toNatE_one : (interp 0).toNat (1 : (interp 0).K) = 1 := by
  have := toNat_gold_natCast (F0 := F0) (FH := FH) (k := 1) (by norm_num [pGold])
  simpa using this

/-- **The challenge's integer readings** are the honest support and sign bits. -/
theorem evalInt_ref78_honest (k : Fin Native.Rows.deg) :
    program.evalIntWith (program.reader E) 0 (.ref 7) k = Emulated.honestSup i.y k ∧
      program.evalIntWith (program.reader E) 0 (.ref 8) k = Emulated.honestSgn i.y k := by
  have hb := (boundZW (program := program)).2.2
  have hf := (sigData (program := program)).2.2.2.2.2.2.2.2.1
  have h0 := rdA_61_native (F0 := F0) i (x := x) (c := c) (π := π) k 0
  have h1 := rdA_61_native (F0 := F0) i (x := x) (c := c) (π := π) k 1
  obtain ⟨e7, e8⟩ := evalInt_ref78 E k
  refine ⟨?_, ?_⟩
  · rw [e7, intOf_priv E hb hf]
    simp only [Fin.val_zero, Nat.add_zero] at h0
    rw [h0]
    change ((interp 0).toNat (HashCircuit.ternaryBits (K := F0.K) (i.y.c k)).1 : ℤ) = _
    rw [show (HashCircuit.ternaryBits (K := F0.K) (i.y.c k)).1 = if i.y.c k = 0 then 0 else 1 from rfl]
    unfold Emulated.honestSup
    split_ifs
    · rw [toNatE_zero]
      rfl
    · rw [toNatE_one]
      rfl
  · rw [e8, intOf_priv E hb hf]
    simp only [Fin.val_one] at h1
    rw [h1]
    change ((interp 0).toNat (HashCircuit.ternaryBits (K := F0.K) (i.y.c k)).2 : ℤ) = _
    rw [show (HashCircuit.ternaryBits (K := F0.K) (i.y.c k)).2 = if i.y.c k = -1 then 1 else 0 from rfl]
    unfold Emulated.honestSgn
    split_ifs
    · rw [toNatE_one]
      rfl
    · rw [toNatE_zero]
      rfl

/-- **`signature.relation` holds** (predicate `274`) at the honest values, at the key's
statement. -/
theorem sig274_honest (hx : x = hE.stmtOfKey i.y.key) :
    program.HoldsWith (program.reader E) (program.predicate 274).body := by
  have hk : KeyOf i.y.key (program.srcEnv interp x (honestVal program F0 FH i) c π).stmt := by
    change KeyOf i.y.key x
    rw [hx]
    exact keyOf _
  refine sig274_of E hk (wv := Emulated.honestWNat i.y) (zv := Emulated.honestZNat i.y)
    (fun i' k => ?_) (fun j m => ?_) ?_
  · have hv := rdA_62_native (F0 := F0) i (x := x) (c := c) (π := π) i' k
    refine intOf_of_boundInt (boundZW (program := program)).2.1
      (sigData (program := program)).2.2.2.2.2.2.2.2.2.1 (z := (Emulated.honestWNat i.y i' k : ℤ))
      ?_ (by rw [hv, Int.cast_natCast]; rfl)
    have hlt : Emulated.honestWNat i.y i' k < 8380417 :=
      ZMod.val_lt (NativeAlgebraCircuit.Honest.wCoeff i.y.key i.y.c i.y.z i' k)
    rw [abs_of_nonneg (by positivity)]
    have h2 : 2 * Emulated.honestWNat i.y i' k < pGold := by
      norm_num [pGold]
      omega
    exact_mod_cast h2
  · have hv := rdA_59_native (F0 := F0) i (x := x) (c := c) (π := π) j m
    have hz := Emulated.zCentered_natAbs_lt (y := i.y) i.valid j m
    have hzc := Emulated.honestZNat_cast (y := i.y) i.valid j m
    rw [intOf_of_boundInt (boundZW (program := program)).1
      (sigData (program := program)).2.2.2.2.2.2.2.1
      (z := NativeAlgebraCircuit.Honest.zCentered i.y.z j m) ?_ (by rw [hv]; rfl)]
    · unfold Rows.signedZ
      rw [hzc]
      simp [Rows.shift, Native.Params.normOffset]
    · have hb : (NativeAlgebraCircuit.Honest.zCentered i.y.z j m).natAbs < 130994 := hz
      have ha : |NativeAlgebraCircuit.Honest.zCentered i.y.z j m| < 130994 := by
        rw [Int.abs_eq_natAbs]; exact_mod_cast hb
      norm_num [pGold]
      omega
  · have hcf : (fun m : Fin Native.Rows.deg => program.evalIntWith (program.reader E) 0 (.ref 7) m -
        2 * program.evalIntWith (program.reader E) 0 (.ref 8) m) =
        fun k => Emulated.honestSup i.y k - 2 * Emulated.honestSgn i.y k :=
      funext fun k => by rw [(evalInt_ref78_honest i k).1, (evalInt_ref78_honest i k).2]
    rw [hcf]
    exact Emulated.congruent_honest i.valid

end Sig

end GordieHowe.MLDSA44.Emulated
