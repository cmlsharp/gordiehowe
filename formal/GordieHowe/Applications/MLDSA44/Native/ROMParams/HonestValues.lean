-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Native.ROMParams.HonestSelect
public import GordieHowe.Applications.MLDSA44.Honest.A
public import GordieHowe.Language.Honest.Digits

@[expose] public section

/-!
# GordieHowe: the honest valuation of a native ML-DSA program

The honest committed values of a native ML-DSA program (`MLDSA44.Native.ROMParams`,
`MLDSA44.Native.QROMParams`) on an honest input (`honestVal`): domain `H`'s (`hVal`: the hash's inputs,
SampleInBall's selection and memory cells) and domain `A`'s (`aVal`): `GordieHowe.MLDSA44.PoP.Native`'s honest
assignment's hint, challenge bits, `w'`, UseHint output bits and signs
(`GordieHowe.MLDSA44.Native.honestAssignment`), the base-`512` digits of `z + 130993`, of its complement to
`261986`, of the UseHint offset and slack, and the static histogram of their needles. With the
readings of these values at the source environment (`rdA_honest`) and domain `A`'s predicates at
them.

The two native programs share every value and predicate identifier and differ in their fields, the
MAC's width and the radix of its digits. The program facts the honest strategy reads are the class
`MldsaNativeHonest`, decided per program (`GordieHowe/Applications/MLDSA44/Native/ROMParams/HonestFacts.lean`,
`GordieHowe/Applications/MLDSA44/Native/QROMParams/HonestFacts.lean`).
-/

namespace GordieHowe.MLDSA44.Native.ROMParams

open GordieHowe.Bits RealizedProgram
open Native.Params (T)

/-- **Domain `A`'s committed values.** -/
def AValues : List ℕ := [59, 60, 61, 63, 64, 576, 577, 581, 582, 583, 584]

/-- **The MAC's predicates**: `mac.A` (the accumulator row), the lower digit's and the top digit's
ranges, the no-wrap check, the tail `mac`. -/
def macRolePreds : List ℕ := [4, 15, 16, 17, 271]

set_option linter.unusedSectionVars false

set_option hygiene false in
local notation "interp" => mldsaInterpOf F0 FH

/-- **The program facts of a native ML-DSA program's honest strategy** (each program instantiates
them by `decide`): the MAC `mac` with its digit tail (`mac.equal` of `ref 525` and `ref 7`, width
`macW`), the statement of a key (`stmtOfKey`) with what the honest prover reads of it, the only
cross-field `equal` the MAC's, and the kinds, sizes and classes of the values the honest values are
read through. -/
class MldsaNativeHonest (program : RealizedProgram) (F0 FH : outParam FieldInterp) where
  /-- The realized program's prime-subfield nodes. -/
  PN : ℕ → List String
  /-- The program declares no statement bound. -/
  noBounds : program.declaredRanges = []
  /-- The MAC with its digit tail. -/
  mac : program.DigitsMac PN
  /-- The MAC's width. -/
  macW : ℕ
  /-- The statement of a key. -/
  stmtOfKey : MLDSA44.PublicKey44 → program.Valuation interp
  /-- Every value bound to its digits reads committed values and constants (`BoundOk`). -/
  bound : ∀ v < program.values.length, program.BoundOk v
  /-- The program is well formed. -/
  wellFormed : program.WellFormed
  /-- The interpretation's registry. -/
  registered : (interp).Registered program
  /-- The interpretation's integer readings. -/
  lawful : (interp).Lawful program PN
  /-- The MAC model. -/
  macModel : (interp).MacModel program
  /-- The key's statement holds the key's preprocessing. -/
  keyOf : ∀ pk, KeyOf pk (stmtOfKey pk)
  /-- The key's statement holds naturals at `key.a_hat`. -/
  stmt56 : ∀ pk, ∀ j < 4096, ∃ n : ℕ, (castElt (b := 0) (stmtOfKey pk 56 j) : (interp 0).K) = n
  /-- The key's statement holds naturals at `key.t1`. -/
  stmt57 : ∀ pk, ∀ j < 1024, ∃ n : ℕ, (castElt (b := 0) (stmtOfKey pk 57 j) : (interp 0).K) = n
  /-- The key's statement holds the bits of `tr` at value `67`. -/
  stmt67 : ∀ pk, ∀ j (hj : j < 512), (castElt (b := 1) (stmtOfKey pk 67 j) : (interp 1).K) =
    constBit (MLDSA44.PoP.Compose.trOf pk ⟨j / 8, by omega⟩).toNat (j % 8)
  /-- The statement has no member checks. -/
  checks : program.statement.checks = []
  /-- The realization's predicates outside the MAC's are no source predicates. -/
  realPreds : ∀ q ∈ [5, 10], program.inSource (program.predicate q) = false
  /-- `key.a_hat` and `key.t1` are opaque statement values. -/
  kinds5657 : (program.value 56).kind = .pub (.opaque "key.a_hat" []) ∧
    (program.value 57).kind = .pub (.opaque "key.t1" [])
  /-- Domain `A`'s committed values are cells of field `0`. -/
  a_cells : ∀ v ∈ AValues, program.privCellB v = true ∧ program.valueField v = 0
  /-- Domain `A`'s bound values. -/
  a_kinds : (program.value 58).kind = .bound (.add (.add (.leaf 576) (.scale (.const 512)
      (.leaf 577))) (.scale (.const 8380416) (.leaf 62))) ∧
    (program.value 65).kind = .bound (.add (.leaf 581) (.scale (.const 512) (.leaf 582))) ∧
    (program.value 66).kind = .bound (.add (.leaf 583) (.scale (.const 512) (.leaf 584)))
  /-- The fields and sizes of domain `A`'s values. -/
  a_bound : program.valueField 58 = 0 ∧ program.valueField 65 = 0 ∧ program.valueField 66 = 0 ∧
    58 < program.values.length ∧ 65 < program.values.length ∧ 66 < program.values.length ∧
    (∀ v ∈ [576, 577, 581, 582, 583, 584], (program.value v).size = 1024) ∧
    (program.value 59).size = 1024 ∧ (program.value 60).size = 512 ∧
    (program.value 61).size = 1024 ∧ (program.value 63).size = 6144 ∧
    (program.value 64).size = 1024 ∧ (program.value 578).size = 1024 ∧
    (program.value 579).size = 1024 ∧ (program.value 586).size = 512
  /-- The blind's cells. -/
  blind_cells : (program.value 568).kind = .padCopy 571 "polynomialBits" ∧
    (program.value 568).domain < program.domains.length ∧
    (∀ j < macW, CellKey.val 568 j ∈ program.cellKeys (program.value 568).domain) ∧
    program.valueField 568 = 0 ∧ (program.value 568).size = macW
  /-- The program has `273` predicates. -/
  predicates_length : program.predicates.length = 273
  /-- The A operand of the crossing has `6656` coordinates. -/
  len7 : program.exprLen (.ref 7) = 6656
  /-- The bits the A operand reads. -/
  cross_vals : program.isConstant 63 = false ∧ program.isConstant 60 = false ∧
    program.valueField 63 = 0 ∧ program.valueField 60 = 0
  /-- `mac.equal` is predicate `272`, the MAC's. -/
  hb : (program.predicate 272).body = .cross 1 (.ref 525) 0 (.ref 7) {} mac.real
  /-- The MAC crosses `ref 525` of domain `H` and `ref 7` of domain `A`. -/
  mac_shape : mac.dx = 1 ∧ mac.x = Expr.ref 525 ∧ mac.dy = 0 ∧ mac.y = Expr.ref 7 ∧ mac.k = {} ∧
    mac.cdy = 0 ∧ mac.cy = Expr.ref 7
  /-- The only cross-field `equal` is the MAC's. -/
  crossMac : ∀ p ∈ program.predicates, ∀ dx x dy y k real, p.body = .cross dx x dy y k real →
    (program.predicate mac.pid).body = p.body
  /-- The committed values' classes. -/
  cell_classes : (List.range program.values.length).all (fun v =>
    !program.isCellValue (program.value v).domain v || !decide (program.IsSourceValue v) ||
      (program.valueField v == 1 && (program.value v).node.map (·.name) == some "GF(2^16)" &&
        ((wordsOwner? v).isSome || [70, 120, 558, 561, 563, 564, 565, 566].contains v)) ||
      (program.valueField v == 1 && (program.value v).node.map (·.name) == some "bit" &&
        [68, 69, 557, 562].contains v) ||
      (program.valueField v == 0 && (program.value v).node.map (·.name) == some "GF(p^1)" &&
        (AValues.contains v || v == 568))) = true
  /-- Only the blind is a pad copy. -/
  padCopy_only : (List.range program.values.length).all (fun w => w == 568 ||
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

variable {program : RealizedProgram} [MldsaAAlgebra program] [MldsaHHonest program] [MldsaHShuffle program]
  [MldsaHSelHonest program] {F0 FH : FieldInterp} [QField F0] [HField FH]
  [MldsaHConsts program FH] [MldsaHNativeData FH] [MldsaHNodes FH]
  [hN : MldsaNativeHonest program F0 FH]

open MldsaNativeHonest

/-! ## Domain `A`'s honest naturals -/

variable (F0) in
/-- **`Native`'s honest assignment** of an honest input (domain `A`'s honest values, in domain
`A`'s field; its domain-`H` part is read at `GF(2^128)` and unused). -/
-- spec-side
noncomputable abbrev nativeA (i : MLDSA44.HonestInput) :=
  Native.honestAssignment (KH := GF2_128) (F := F0.K) gf2_128PackedBasis i.y

/-- **The flat index** `m < 1024` of a coefficient `(i, k)` of a `4 × 256` value. -/
def fm (j : ℕ) (h : j < 1024) : Fin (Rows.nRows * Rows.deg) := ⟨j, h⟩

/-- **The flat index** `m < 1024` of a coefficient `(j, k)` of `z`. -/
def fmz (j : ℕ) (h : j < 1024) : Fin (Rows.nCols * Rows.deg) := ⟨j, h⟩

/-- **The honest UseHint offset** of coefficient `m`, as committed: its base-`T^2` digit
(`UseHint.honest`). -/
-- spec-side
noncomputable def offN (i : MLDSA44.HonestInput) (m : Fin (Rows.nRows * Rows.deg)) : ℕ :=
  MLDSA44.NativeAlgebraCircuit.flat (fun a b => GordieHowe.MLDSA44.useHintOffset mldsa44.γ₂ (MLDSA44.NativeAlgebraCircuit.Honest.hintBool i.y.h a b)
    (MLDSA44.NativeAlgebraCircuit.Honest.wCoeff i.y.key i.y.c i.y.z a b) / (T * T) ^ ((0 : Fin 1) : ℕ) % (T * T)) m

/-- **The honest UseHint slack** of coefficient `m`, as committed: its base-`T^2` digit
(`UseHint.honest`). -/
-- spec-side
noncomputable def slN (i : MLDSA44.HonestInput) (m : Fin (Rows.nRows * Rows.deg)) : ℕ :=
  MLDSA44.NativeAlgebraCircuit.flat (fun a b =>
    (mldsa44.γ₂ - 1 + GordieHowe.MLDSA44.useHintEndpoint (UseHint.hiCount mldsa44.γ₂)
      (MLDSA44.NativeAlgebraCircuit.Honest.hintBool i.y.h a b)
      (GordieHowe.MLDSA44.useHintSign mldsa44.γ₂ (MLDSA44.NativeAlgebraCircuit.Honest.wCoeff i.y.key i.y.c i.y.z a b))
      (_root_.MLDSA.Concrete.useHintCoeff (MLDSA44.NativeAlgebraCircuit.Honest.hintBool i.y.h a b)
        (MLDSA44.NativeAlgebraCircuit.Honest.wCoeff i.y.key i.y.c i.y.z a b) mldsa44.γ₂) -
      GordieHowe.MLDSA44.useHintOffset mldsa44.γ₂ (MLDSA44.NativeAlgebraCircuit.Honest.hintBool i.y.h a b)
        (MLDSA44.NativeAlgebraCircuit.Honest.wCoeff i.y.key i.y.c i.y.z a b)) / (T * T) ^ ((0 : Fin 1) : ℕ) % (T * T)) m

/-- **The honest shifted `z`** of coefficient `m`: `z + 130993` (the centered coefficient shifted
by `γ₁ − β − 1`), a natural below `261987` on a valid input. -/
-- spec-side
def zN (i : MLDSA44.HonestInput) (m : Fin (Rows.nCols * Rows.deg)) : ℕ :=
  MLDSA44.NativeAlgebraCircuit.flat (fun a b => (MLDSA44.NativeAlgebraCircuit.Honest.zCentered i.y.z a b + 130993).toNat) m

/-- **The honest hint weight**: the number of set hint bits. -/
-- spec-side
def wtN (i : MLDSA44.HonestInput) : ℕ :=
  ∑ m : Fin (Rows.nRows * Rows.deg),
    (MLDSA44.NativeAlgebraCircuit.flat (MLDSA44.NativeAlgebraCircuit.Honest.hintBool i.y.h) m).toNat

variable (F0) in
/-- **Domain `A`'s honest values** (field `F_q^6`): the hint (`59`), the challenge bits (`60`),
`w'` (`61`), the UseHint output bits (`63`) and signs (`64`) of `Native`'s honest
assignment; the digits of the values bound to their digits: of `z + 130993` (`576`, `577`), of
the offset (`581`, `582`) and of the slack (`583`, `584`); `0` elsewhere (the realization's values
are generated, `RealizedProgram.genCommitted`).

Running time: a prover computing these values would take the time of `Native`'s honest
assignment (one `computeWApprox`, `O(k N)` UseHint advice computations).
This running time is argued here, not proved in Lean. -/
-- spec-side
noncomputable def aVal (i : MLDSA44.HonestInput) (v j : ℕ) : F0.K :=
  if v = 60 then
    (if h : j < 512 then (nativeA F0 i).cA ⟨j / 2, by change j / 2 < 256; omega⟩ ⟨j % 2, by omega⟩
      else 0)
  else if v = 63 then
    (if h : j < 6144 then MLDSA44.NativeAlgebraCircuit.outputBits (nativeA F0 i).w1A
      ⟨j / 6, by change j / 6 < 4 * 256; omega⟩ ⟨j % 6, by change j % 6 < 6; omega⟩ else 0)
  else if h : j < 1024 then
    if v = 59 then MLDSA44.NativeAlgebraCircuit.flat (nativeA F0 i).h (fm j h)
    else if v = 61 then MLDSA44.NativeAlgebraCircuit.flat (nativeA F0 i).w (fm j h)
    else if v = 64 then MLDSA44.NativeAlgebraCircuit.flat (nativeA F0 i).np (fm j h)
    else if v = 576 then ((zN i (fmz j h) % 512 : ℕ) : F0.K)
    else if v = 577 then ((zN i (fmz j h) / 512 : ℕ) : F0.K)
    else if v = 581 then ((offN i (fm j h) % 512 : ℕ) : F0.K)
    else if v = 582 then ((offN i (fm j h) / 512 : ℕ) : F0.K)
    else if v = 583 then ((slN i (fm j h) % 512 : ℕ) : F0.K)
    else if v = 584 then ((slN i (fm j h) / 512 : ℕ) : F0.K)
    else 0
  else 0

variable (program F0 FH) in
/-- **The honest committed values of a native program** on an honest input: domain `A`'s
values (`aVal`), domain `H`'s (`hVal`: the hash's inputs, the selected bytes' bits, the threshold
words, the memory cells).

Running time: a prover computing these values would take the time of `hVal` and of `aVal`.
This running time is argued here, not proved in Lean. -/
-- spec-side
noncomputable def honestVal (i : MLDSA44.HonestInput) (v j : ℕ) : (interp (program.valueField v)).K :=
  if v ∈ AValues then castElt (a := 0) (aVal F0 i v j)
  else hVal program F0 FH i v j

/-! ## The honest values by class -/

section Classes

variable (i : MLDSA44.HonestInput)

theorem honestVal_of_field {v : ℕ} (hf : program.valueField v = 1) :
    honestVal program F0 FH i v = hVal program F0 FH i v := funext fun j => by
  have hv : v ∉ AValues := fun h => by
    have := ((a_cells (program := program)) v h).2
    omega
  unfold honestVal
  rw [if_neg hv]

theorem honestVal_a : ∀ v, v ∈ AValues → ∀ n,
    castElt (b := 0) (honestVal program F0 FH i v n) = aVal F0 i v n := by
  intro v hv n
  unfold honestVal
  rw [if_pos hv]
  exact castElt_castElt_of_eq ((a_cells (program := program)) v hv).2.symm _

/-- **The source environment reads domain `H`'s honest values.** -/
theorem readsCells_honest (x : program.Valuation interp) (c : ∀ k, (program.layout interp).Ch k)
    (π : (program.layout interp).Pads) :
    program.ReadsCells 1 (program.srcEnv interp x (honestVal program F0 FH i) c π)
      (hVal program F0 FH i) := fun v j hp hf hj => by
  rw [RealizedProgram.reader_srcEnv_of_privCellB x _ c π hp hj, honestVal_of_field i hf]

end Classes

/-! ## `aVal` at each value -/

section Access

variable (i : MLDSA44.HonestInput) {j : ℕ}

theorem aVal_59 (h : j < 1024) : aVal F0 i 59 j = MLDSA44.NativeAlgebraCircuit.flat (nativeA F0 i).h (fm j h) := by
  unfold aVal
  simp only [show (59 : ℕ) ≠ 60 by decide, show (59 : ℕ) ≠ 63 by decide,
    if_false, dif_pos h, if_true]

theorem aVal_61 (h : j < 1024) : aVal F0 i 61 j = MLDSA44.NativeAlgebraCircuit.flat (nativeA F0 i).w (fm j h) := by
  unfold aVal
  simp only [show (61 : ℕ) ≠ 60 by decide, show (61 : ℕ) ≠ 63 by decide,
    show (61 : ℕ) ≠ 59 by decide, if_false, dif_pos h, if_true]

theorem aVal_64 (h : j < 1024) : aVal F0 i 64 j = MLDSA44.NativeAlgebraCircuit.flat (nativeA F0 i).np (fm j h) := by
  unfold aVal
  simp only [show (64 : ℕ) ≠ 60 by decide, show (64 : ℕ) ≠ 63 by decide,
    show (64 : ℕ) ≠ 59 by decide, show (64 : ℕ) ≠ 61 by decide,
    if_false, dif_pos h, if_true]

theorem aVal_60 (h : j < 512) : aVal F0 i 60 j =
    (nativeA F0 i).cA ⟨j / 2, by change j / 2 < 256; omega⟩ ⟨j % 2, by omega⟩ := by
  unfold aVal
  rw [if_pos rfl]
  exact dif_pos h

theorem aVal_63 (h : j < 6144) : aVal F0 i 63 j = MLDSA44.NativeAlgebraCircuit.outputBits (nativeA F0 i).w1A
    ⟨j / 6, by change j / 6 < 4 * 256; omega⟩ ⟨j % 6, by change j % 6 < 6; omega⟩ := by
  unfold aVal
  rw [if_neg (by decide), if_pos rfl]
  exact dif_pos h

/-- **The digits of domain `A`** at a coefficient. -/
theorem aVal_digits (h : j < 1024) :
    aVal F0 i 576 j = ((zN i (fmz j h) % 512 : ℕ) : F0.K) ∧
    aVal F0 i 577 j = ((zN i (fmz j h) / 512 : ℕ) : F0.K) ∧
    aVal F0 i 581 j = ((offN i (fm j h) % 512 : ℕ) : F0.K) ∧
    aVal F0 i 582 j = ((offN i (fm j h) / 512 : ℕ) : F0.K) ∧
    aVal F0 i 583 j = ((slN i (fm j h) % 512 : ℕ) : F0.K) ∧
    aVal F0 i 584 j = ((slN i (fm j h) / 512 : ℕ) : F0.K) := by
  unfold aVal
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [dif_pos h, Nat.reduceEqDiff, if_false, if_true]

end Access

/-! ## Domain `A`'s readings at the source environment -/

section Readings

variable {i : MLDSA44.HonestInput} {x : program.Valuation interp} {c : ∀ k, (program.layout interp).Ch k}
  {π : (program.layout interp).Pads}

/-- **A committed value of domain `A` reads its honest value** at the source environment. -/
theorem rdA_honest {v : ℕ} (hv : v ∈ AValues) {j : ℕ} (hj : j < (program.value v).size) :
    rdA (program.srcEnv interp x (honestVal program F0 FH i) c π) v j = aVal F0 i v j := by
  unfold rdA
  rw [evalE_leaf, reader_srcEnv_of_privCellB x _ c π ((a_cells (program := program)) v hv).1 hj]
  exact honestVal_a i v hv j

/-- **A bound value of domain `A` reads its expression** at the source environment. -/
theorem rdA_bound {v : ℕ} {e : Expr} (hk : (program.value v).kind = .bound e)
    (hf : program.valueField v = 0) (hv : v < program.values.length) (j : ℕ) :
    rdA (program.srcEnv interp x (honestVal program F0 FH i) c π) v j =
      program.evalE (program.reader (program.srcEnv interp x (honestVal program F0 FH i) c π)) 0 e j := by
  unfold rdA
  rw [evalE_leaf, reader_bindAsg_of_boundOk (bound (program := program)) rfl hv hk]
  revert hf
  generalize program.valueField v = f
  intro hf
  subst hf
  rfl

/-- **The offset reads its digits' sum**: the committed offset of `Native`'s honest
assignment. -/
theorem rdA_65 {m : ℕ} (hm : m < 1024) :
    rdA (program.srcEnv interp x (honestVal program F0 FH i) c π) 65 m = ((offN i (fm m hm) : ℕ) : (interp 0).K) := by
  obtain ⟨-, h65, -⟩ := (a_kinds (program := program))
  obtain ⟨-, hf, -, -, hl, -, hs, -⟩ := (a_bound (program := program))
  rw [rdA_bound h65 hf hl, evalE_add, evalE_scale_const, decode_fq6]
  change rdA _ 581 m + _ * rdA _ 582 m = _
  rw [rdA_honest (i := i) (x := x) (c := c) (π := π) (by decide) (by rw [hs 581 (by decide)]; exact hm),
    rdA_honest (i := i) (x := x) (c := c) (π := π) (by decide) (by rw [hs 582 (by decide)]; exact hm),
    (aVal_digits i hm).2.2.1, (aVal_digits i hm).2.2.2.1]
  rw [← Nat.cast_mul, ← Nat.cast_add]
  congr 1
  omega

/-- **The slack reads its digits' sum.** -/
theorem rdA_66 {m : ℕ} (hm : m < 1024) :
    rdA (program.srcEnv interp x (honestVal program F0 FH i) c π) 66 m = ((slN i (fm m hm) : ℕ) : (interp 0).K) := by
  obtain ⟨-, -, h66⟩ := (a_kinds (program := program))
  obtain ⟨-, -, hf, -, -, hl, hs, -⟩ := (a_bound (program := program))
  rw [rdA_bound h66 hf hl, evalE_add, evalE_scale_const, decode_fq6]
  change rdA _ 583 m + _ * rdA _ 584 m = _
  rw [rdA_honest (i := i) (x := x) (c := c) (π := π) (by decide) (by rw [hs 583 (by decide)]; exact hm),
    rdA_honest (i := i) (x := x) (c := c) (π := π) (by decide) (by rw [hs 584 (by decide)]; exact hm),
    (aVal_digits i hm).2.2.2.2.1, (aVal_digits i hm).2.2.2.2.2]
  rw [← Nat.cast_mul, ← Nat.cast_add]
  congr 1
  omega

/-- **The UseHint output bits read `Native`'s honest assignment's.** -/
theorem bitsA_honest {m : ℕ} (hm : m < 1024) :
    bitsA (program.srcEnv interp x (honestVal program F0 FH i) c π) m =
      MLDSA44.NativeAlgebraCircuit.outputBits (nativeA F0 i).w1A (fm m hm) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h63, -⟩ := (a_bound (program := program))
  funext b
  have hb := b.isLt
  change (b : ℕ) < 6 at hb
  unfold bitsA
  rw [rdA_honest (i := i) (x := x) (c := c) (π := π) (by decide) (by rw [h63]; omega), aVal_63 i (by omega)]
  have e1 : (⟨(6 * m + b) / 6, by change (6 * m + b) / 6 < 4 * 256; omega⟩ :
      Fin (Rows.nRows * Rows.deg)) = fm m hm := Fin.ext (by simp only [fm]; omega)
  have e2 : (⟨(6 * m + b) % 6, by change (6 * m + b) % 6 < 6; omega⟩ : Fin mldsa44.r1_bits) = b :=
    Fin.ext (by simp only; omega)
  rw [e1, e2]

/-- The offset of `Native`'s honest assignment is the committed offset's natural. -/
theorem offset_native (m : Fin (Rows.nRows * Rows.deg)) :
    MLDSA44.NativeAlgebraCircuit.flat (nativeA F0 i).offset m = ((offN i m : ℕ) : (interp 0).K) := rfl

/-- The slack of `Native`'s honest assignment is the committed slack's natural. -/
theorem slack_native (m : Fin (Rows.nRows * Rows.deg)) :
    MLDSA44.NativeAlgebraCircuit.flat (nativeA F0 i).slack m = ((slN i m : ℕ) : (interp 0).K) := rfl

end Readings

/-! ## Domain `A`'s UseHint and Booleanity predicates at the honest values -/

section HoldsA

variable (i : MLDSA44.HonestInput) {x : program.Valuation interp} {c : ∀ k, (program.layout interp).Ch k}
  {π : (program.layout interp).Pads}

/-- **`Native`'s honest algebra constraints** (`Native.algebraConstraints_honest`). -/
theorem nativeAC : Native.AlgebraConstraints i.y.key (nativeA F0 i) :=
  Native.algebraConstraints_honest (KH := GF2_128) (F := F0.K) (B := gf2_128PackedBasis)

set_option hygiene false in
local notation "E" => program.srcEnv interp x (honestVal program F0 FH i) c π

theorem w1Bits_bool : ∀ m < 1024, ∀ t < 6, rdA E 63 (6 * m + t) = 0 ∨ rdA E 63 (6 * m + t) = 1 :=
  fun m hm t ht => by
    have h := congrFun (bitsA_honest (i := i) (x := x) (c := c) (π := π) hm) ⟨t, ht⟩
    unfold bitsA at h
    rw [h]
    exact (nativeAC i).w1Bool _

theorem useHint_at {m : ℕ} (hm : m < 1024) :
    Native.UseHintHolds (rdA E 59 m) (rdA E 61 m) (rdA E 64 m) (rdA E 65 m) (rdA E 66 m)
      (bitsA E m) := by
  obtain ⟨-, -, -, -, -, -, -, h59, -, h61, -, h64, -⟩ := (a_bound (program := program))
  rw [rdA_honest (i := i) (x := x) (c := c) (π := π) (by decide) (by rw [h59]; exact hm), rdA_honest (i := i) (x := x) (c := c) (π := π) (by decide) (by rw [h61]; exact hm),
    rdA_honest (i := i) (x := x) (c := c) (π := π) (by decide) (by rw [h64]; exact hm), rdA_65 hm, rdA_66 hm, bitsA_honest hm,
    aVal_59 i hm, aVal_61 i hm, aVal_64 i hm, ← offset_native, ← slack_native]
  exact (nativeAC i).useHint (fm m hm)

/-- **`hint.w1_bound` holds** at the honest values. -/
theorem w1bound_honest : program.HoldsWith (program.reader E) (program.predicate 1).body :=
  w1bound1_of _ (w1Bits_bool i) fun _ hm => (useHint_at i hm).le

/-- **`hint.decompose` holds** at the honest values. -/
theorem decompose_honest : program.HoldsWith (program.reader E) (program.predicate 2).body :=
  decompose2_of (w1Bits_bool i) fun _ hm => (useHint_at i hm).decompose

theorem offN_lt (m : Fin (Rows.nRows * Rows.deg)) : offN i m < 262144 :=
  Nat.mod_lt _ (by norm_num [T])

theorem slN_lt (m : Fin (Rows.nRows * Rows.deg)) : slN i m < 262144 :=
  Nat.mod_lt _ (by norm_num [T])

theorem h59_bool : ∀ m < 1024, rdA E 59 m = 0 ∨ rdA E 59 m = 1 := fun m hm => by
  obtain ⟨-, -, -, -, -, -, -, h59, -⟩ := (a_bound (program := program))
  rw [rdA_honest (i := i) (x := x) (c := c) (π := π) (by decide) (by rw [h59]; exact hm), aVal_59 i hm]
  exact (nativeAC i).hBool _ _

theorem h64_bool : ∀ m < 1024, rdA E 64 m = 0 ∨ rdA E 64 m = 1 := fun m hm => by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h64, -⟩ := (a_bound (program := program))
  rw [rdA_honest (i := i) (x := x) (c := c) (π := π) (by decide) (by rw [h64]; exact hm), aVal_64 i hm]
  exact (nativeAC i).npBool _ _

theorem h60_bool : ∀ s < 512, rdA E 60 s = 0 ∨ rdA E 60 s = 1 := fun s hs => by
  obtain ⟨-, -, -, -, -, -, -, -, h60, -⟩ := (a_bound (program := program))
  rw [rdA_honest (i := i) (x := x) (c := c) (π := π) (by decide) (by rw [h60]; exact hs), aVal_60 i hs]
  exact (nativeAC i).cBool _ _

theorem offset_nat : ∀ m < 1024, ∃ k : ℕ, k < 262144 ∧ rdA E 65 m = k :=
  fun m hm => ⟨_, offN_lt i (fm m hm), rdA_65 hm⟩

theorem slack_nat : ∀ m < 1024, ∃ k : ℕ, k < 262144 ∧ rdA E 66 m = k :=
  fun m hm => ⟨_, slN_lt i (fm m hm), rdA_66 hm⟩

/-- **`hint.interval` holds** at the honest values. -/
theorem interval_honest : program.HoldsWith (program.reader E) (program.predicate 3).body :=
  interval3_of _ (w1Bits_bool i) (h59_bool i) (h64_bool i) (offset_nat i) (slack_nat i)
    fun _ hm => (useHint_at i hm).interval

/-- **`hint.offset` holds** at the honest values. -/
theorem offset_honest : program.HoldsWith (program.reader E) (program.predicate 12).body :=
  offset12_of _ (offset_nat i)

/-- **`hint.slack` holds** at the honest values. -/
theorem slack_honest : program.HoldsWith (program.reader E) (program.predicate 13).body :=
  slack13_of _ (slack_nat i)

/-- **The type checks of `A` hold** at the honest values (`h`, `c`, `w1`, the signs). -/
theorem bools_honest {q : ℕ} (hq : q ∈ [6, 7, 8, 9]) :
    program.HoldsWith (program.reader E) (program.predicate q).body := by
  obtain ⟨-, -, -, -, -, -, -, h59, h60, -, h63, h64, -⟩ := (a_bound (program := program))
  obtain ⟨b6, b7, b8, b9⟩ := boolChecks (program := program)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact boolA_of _ b6 fun j hj => h59_bool i j (h59 ▸ hj)
  · exact boolA_of _ b7 fun j hj => h60_bool i j (h60 ▸ hj)
  · refine boolA_of _ b8 fun j hj => ?_
    rw [h63] at hj
    have := w1Bits_bool i (x := x) (c := c) (π := π) (j / 6) (by omega) (j % 6) (by omega)
    rwa [Nat.div_add_mod] at this
  · exact boolA_of _ b9 fun j hj => h64_bool i j (h64 ▸ hj)

theorem zN_le (m : Fin (Rows.nCols * Rows.deg)) : zN i m ≤ 261986 := by
  unfold zN MLDSA44.NativeAlgebraCircuit.flat
  dsimp only
  have := Native.zCentered_natAbs_lt (y := i.y) i.valid (finProdFinEquiv.symm m).1
    (finProdFinEquiv.symm m).2
  change _ < 130994 at this
  omega

theorem zN_cast (m : Fin (Rows.nCols * Rows.deg)) :
    ((zN i m : ℕ) : F0.K) =
      ((MLDSA44.NativeAlgebraCircuit.flat (MLDSA44.NativeAlgebraCircuit.Honest.zCentered i.y.z) m : ℤ) : F0.K) +
        ((130993 : ℕ) : F0.K) := by
  unfold zN MLDSA44.NativeAlgebraCircuit.flat
  have := Native.zCentered_natAbs_lt (y := i.y) i.valid (finProdFinEquiv.symm m).1
    (finProdFinEquiv.symm m).2
  change _ < 130994 at this
  have h0 : 0 ≤ MLDSA44.NativeAlgebraCircuit.Honest.zCentered i.y.z (finProdFinEquiv.symm m).1
      (finProdFinEquiv.symm m).2 + 130993 := by omega
  rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]
  push_cast
  ring

/-- **`z` reads its centered coefficient** at the honest values. -/
theorem rdA_58 {m : ℕ} (hm : m < 1024) :
    rdA E 58 m = ((MLDSA44.NativeAlgebraCircuit.flat (MLDSA44.NativeAlgebraCircuit.Honest.zCentered i.y.z) (fmz m hm) : ℤ) :
      (interp 0).K) := by
  obtain ⟨h58, -, -⟩ := (a_kinds (program := program))
  obtain ⟨hf, -, -, hl, -, -, hs, -⟩ := (a_bound (program := program))
  rw [rdA_bound h58 hf hl, evalE_add, evalE_add, evalE_scale_const, evalE_scale_const, decode_fq6,
    decode_fq6]
  change rdA _ 576 m + _ * rdA _ 577 m + _ * rdA _ 62 m = _
  rw [rdA_honest (i := i) (x := x) (c := c) (π := π) (by decide) (by rw [hs 576 (by decide)]; exact hm),
    rdA_honest (i := i) (x := x) (c := c) (π := π) (by decide) (by rw [hs 577 (by decide)]; exact hm), rdA_62 _ hm,
    (aVal_digits i hm).1, (aVal_digits i hm).2.1]
  have hz := zN_cast (F0 := F0) i (fmz m hm)
  have hd : ((zN i (fmz m hm) % 512 : ℕ) : (interp 0).K) + ((512 : ℕ) : (interp 0).K) *
      ((zN i (fmz m hm) / 512 : ℕ) : (interp 0).K) = ((zN i (fmz m hm) : ℕ) : (interp 0).K) := by
    rw [← Nat.cast_mul, ← Nat.cast_add]
    congr 1
    omega
  have hq : ((8380417 : ℕ) : (interp 0).K) = 0 := CharP.cast_eq_zero _ _
  push_cast at hz hd hq ⊢
  linear_combination hd + hz + 130993 * hq

/-- **`norm.z` holds** at the honest values. -/
theorem norm_honest : program.HoldsWith (program.reader E) (program.predicate 11).body :=
  norm11_of _ fun m hm => ⟨zN i (fmz m hm), by have := zN_le i (fmz m hm); omega, by
    rw [rdA_58 i hm, zN_cast]⟩

theorem wtN_le : wtN i ≤ 80 := by
  have h := MLDSA44.NativeAlgebraCircuit.Honest.card_hintBool_le i.y.h
    (i.valid.checks.2.2)
  unfold wtN
  rw [Finset.card_filter] at h
  refine le_of_eq_of_le (Finset.sum_congr rfl fun m _ => ?_) h
  cases MLDSA44.NativeAlgebraCircuit.flat (MLDSA44.NativeAlgebraCircuit.Honest.hintBool i.y.h) m <;> rfl

/-- **`hint_weight.weight` holds** at the honest values. -/
theorem weight_honest : program.HoldsWith (program.reader E) (program.predicate 14).body := by
  obtain ⟨-, -, -, -, -, -, -, h59, -⟩ := (a_bound (program := program))
  refine weight14_of _ ⟨wtN i, by have := wtN_le i; omega, ?_⟩
  unfold wtN
  rw [Nat.cast_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [rdA_honest (i := i) (x := x) (c := c) (π := π) (by decide) (by rw [h59]; exact t.isLt), aVal_59 i t.isLt]
  rfl

end HoldsA

/-! ## `signature.relation` at the honest values -/

section Sig

variable (i : MLDSA44.HonestInput) {x : program.Valuation interp} {c : ∀ k, (program.layout interp).Ch k}
  {π : (program.layout interp).Pads}

set_option hygiene false in
local notation "E" => program.srcEnv interp x (honestVal program F0 FH i) c π

theorem zOf_honest : zOf (program.reader E) = i.y.z := by
  refine Eq.trans ?_ (MLDSA44.NativeAlgebraCircuit.Honest.ofFn_ofCoeff_coeff i.y.z)
  unfold zOf
  refine congrArg Vector.ofFn (funext fun j => congrArg MLDSA44.ofCoeff (funext fun k => ?_))
  have hj4 : (j : ℕ) < 4 := j.isLt
  have hk4 : (k : ℕ) < 256 := k.isLt
  have hm : (j : ℕ) * 256 + k < 1024 := by omega
  have h58 := rdA_58 i (x := x) (c := c) (π := π) hm
  unfold rdA at h58
  unfold zVals
  rw [h58]
  rw [MLDSA44.NativeAlgebraCircuit.coeffRep_eq_intCast rfl]
  have he : fmz ((j : ℕ) * 256 + k) hm = finProdFinEquiv (j, k) :=
    Fin.ext (by simp only [fmz, finProdFinEquiv_apply_val, show MLDSA.ringDegree = 256 from rfl]; ring)
  rw [he, MLDSA44.NativeAlgebraCircuit.flat_apply]
  exact (LatticeCrypto.centeredRepr_intCast _).symm

theorem wOf_honest : wOf (program.reader E) = MLDSA44.PoP.Compose.honestWApprox i.y.key i.y.c i.y.z := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h61, -⟩ := (a_bound (program := program))
  refine Eq.trans ?_ (MLDSA44.NativeAlgebraCircuit.Honest.ofFn_ofCoeff_coeff _)
  unfold wOf
  refine congrArg Vector.ofFn (funext fun j => congrArg MLDSA44.ofCoeff (funext fun k => ?_))
  have hj4 : (j : ℕ) < 4 := j.isLt
  have hk4 : (k : ℕ) < 256 := k.isLt
  have hm : (j : ℕ) * 256 + k < 1024 := by omega
  have h61' := rdA_honest (i := i) (x := x) (c := c) (π := π) (v := 61) (by decide)
    (by rw [h61]; exact hm)
  unfold rdA at h61'
  unfold wVals
  rw [h61', aVal_61 i hm]
  have he : fm ((j : ℕ) * 256 + k) hm = finProdFinEquiv (j, k) :=
    Fin.ext (by simp only [fm, finProdFinEquiv_apply_val, show MLDSA.ringDegree = 256 from rfl]; ring)
  rw [he, MLDSA44.NativeAlgebraCircuit.flat_apply]
  change MLDSA44.NativeAlgebraCircuit.coeffRep
    (((MLDSA44.NativeAlgebraCircuit.Honest.wCoeff i.y.key i.y.c i.y.z j k).val : ℕ) : F0.K) = _
  rw [MLDSA44.NativeAlgebraCircuit.coeffRep_eq_intCast
    (n := ((MLDSA44.NativeAlgebraCircuit.Honest.wCoeff i.y.key i.y.c i.y.z j k).val : ℤ)) (Int.cast_natCast _)]
  push_cast
  rw [ZMod.natCast_zmod_val]
  rfl

theorem cPolyA_honest : cPolyA (program.reader E) = MLDSA44.ofCoeff fun k => (i.y.c k : _root_.MLDSA.Coeff) := by
  obtain ⟨-, -, -, -, -, -, -, -, h60, -⟩ := (a_bound (program := program))
  unfold cPolyA
  congr 1
  funext k
  have hc : ∀ t : Fin 2, cABits (program.reader E) k t = (nativeA F0 i).cA k t := fun t => by
    have ht := t.isLt
    have hk : (k : ℕ) < 256 := k.isLt
    change rdA E 60 (2 * k + t) = _
    rw [rdA_honest (i := i) (x := x) (c := c) (π := π) (by decide) (by rw [h60]; omega),
      aVal_60 i (by omega)]
    congr 1
    · exact Fin.ext (by simp only; omega)
    · exact Fin.ext (by simp only; omega)
  rw [hc 0, hc 1]
  change Rows.bitCoeff (HashCircuit.ternaryBits (K := (interp 0).K) (i.y.c k)).1 -
    2 * Rows.bitCoeff (HashCircuit.ternaryBits (K := (interp 0).K) (i.y.c k)).2 = _
  rcases Native.c_ternary i.y k with hk | hk | hk <;>
    norm_num [hk, HashCircuit.ternaryBits, Rows.bitCoeff]

/-- **`signature.relation` holds** at the honest values, at the key's statement. -/
theorem sig_honest (hx : x = hN.stmtOfKey i.y.key) :
    program.HoldsWith (program.reader E) (program.predicate 0).body := by
  obtain ⟨-, -, -, -, -, -, -, -, h60, h61, -⟩ := (a_bound (program := program))
  obtain ⟨hk56, hk57⟩ := kinds5657 (program := program)
  refine sig0_of _ (pk := i.y.key) ?_ (fun j hj => ?_) (fun j hj => ?_) (fun m hm => ?_)
    (h60_bool i) (fun m hm => ?_) fun j k => ?_
  · change KeyOf i.y.key x
    rw [hx]
    exact keyOf _
  · rw [RealizedProgram.reader_of_opaque_nil _ hk56]
    change castElt (x 56 j) ∈ _
    rw [hx]
    obtain ⟨n, hn⟩ := stmt56 (program := program) i.y.key j hj
    rw [hn]
    exact natCast_mem_primeS _
  · rw [RealizedProgram.reader_of_opaque_nil _ hk57]
    change castElt (x 57 j) ∈ _
    rw [hx]
    obtain ⟨n, hn⟩ := stmt57 (program := program) i.y.key j hj
    rw [hn]
    exact natCast_mem_primeS _
  · exact ⟨_, (rdA_58 i hm).symm⟩
  · rw [rdA_honest (i := i) (x := x) (c := c) (π := π) (by decide) (by rw [h61]; exact hm), aVal_61 i hm]
    exact ⟨_, Int.cast_natCast _⟩
  · rw [wOf_honest, zOf_honest, cPolyA_honest]
    exact MLDSA44.coeff_computeWApprox _ _ _ _ _ j k

end Sig

end GordieHowe.MLDSA44.Native.ROMParams
