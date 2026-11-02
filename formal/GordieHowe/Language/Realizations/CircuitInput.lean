-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.Embed
public import GordieHowe.Language.RealizedProgram.InputLayout
public import GordieHowe.Language.Realizations.RealizeLookup

@[expose] public section

/-!
# GordieHowe: the valuation decoded from a circuit's input vector

Facts about the valuation the trust bundle decodes from an input vector `v` of circuit `c`
(`GordieHowe.RealizedProgram.inputValuation`), which the circuit certificates read:

* **The leaves** (`GordieHowe.RealizedProgram.inputValuation_committed`, `inputValuation_view`,
  `inputValuation_pub`): a committed value's coordinate is the input its committed block holds, a
  bit view's the input its view block holds, a public value's the input its public block holds;
  the positions of a value with one block (`committedPos_eq_of_mem`, `viewPos_eq_of_mem`,
  `pubPos_eq_of_mem`); under the proof system's premises a bit view reads the bits of its decoded
  words (`inputValuation_view_bits`).
* **The decoded valuation is the semantics' reading** (`inputValuation_eq_inputBase`): on a vector
  whose public inputs are the verifier's and on which the proof system's premises hold
  (`GordieHowe.RealizedProgram.InputPremises`), in a layout whose public and pad blocks are placed
  as the plan places them (`GordieHowe.RealizedProgram.InputLayoutOk`), every coordinate reads as
  the reader at the realized assignment of the decoded committed assignment
  (`GordieHowe.RealizedProgram.inputBase`).
* **Bound values read their expressions** (`boundReads_inputValuation`): at the decoded valuation,
  whenever they do at the semantics' reading.
* **The reader premises of the expression templates' views** (definitions):
  `GordieHowe.RealizedProgram.LateModel` (a late value's coordinate is its message input minus its
  pad input) and `GordieHowe.RealizedProgram.ExprReads` (a public expression reads its expression).
-/

namespace GordieHowe.RealizedProgram

open Export

/-- **Whether `inputValuation` reads a value of this kind from a public block**: every kind but a
committed value, a pad copy, a late value and a bit view. -/
def Kind.readsPubBlock : Kind → Bool
  | .priv => false
  | .padCopy _ _ => false
  | .late => false
  | .bits _ _ => false
  | _ => true

section

variable (ir : RealizedProgram) (I : Interp)

/-- **The public and pad blocks of circuit `c` are placed as the plan places them**: the blocks are
contiguous from input `1`; the public inputs lie within the inputs; a public block holds public
inputs of a value of the circuit's field that is late or reads nothing of the committed assignment
(`pubB`); a pad block holds coordinates of a late value of the program. -/
structure InputLayoutOk (c : ℕ) : Prop where
  /-- The blocks are contiguous from input `1` to the input count. -/
  layout : InputBlock.layoutEnd 1 (ir.circuit c).inputs = some (ir.circuit c).inputCount
  /-- The public inputs lie within the inputs. -/
  pubLe : (ir.circuit c).publicInputs ≤ (ir.circuit c).inputCount
  /-- A public block holds public inputs of a public value of the circuit's field. -/
  pub : ∀ u a n, InputBlock.pub u a n ∈ (ir.circuit c).inputs →
    ir.valueField u = ir.circField c ∧ (ir.IsLate u ∨ ir.pubB ir.fuel u = true) ∧ 1 ≤ a ∧
      a + n ≤ (ir.circuit c).publicInputs
  /-- A pad block holds coordinates of a late value. -/
  pad : ∀ u a n, InputBlock.pad u a n ∈ (ir.circuit c).inputs →
    u < ir.values.length ∧ ir.IsLate u ∧ n ≤ (ir.value u).size

end

variable {ir : RealizedProgram} {I : Interp} {c : ℕ} {x : ir.Valuation I}
  {r : (ir.layout I).Run} {d : ℕ} {v : Fin (2 ^ d) → (I (ir.circField c)).K}

/-! ## The leaves -/

/-- **A committed coordinate of the decoded valuation is the input its committed block holds**
(a committed value or a pad copy). -/
theorem inputValuation_committed {u i q : ℕ}
    (hk : (ir.value u).kind = .priv ∨ ∃ s m, (ir.value u).kind = .padCopy s m)
    (hq : (ir.circuit c).committedPos u i = some q) :
    ir.inputValuation I c x r v u i = castElt (vecRead v q) := by
  unfold inputValuation
  rcases hk with hk | ⟨s, m, hk⟩ <;> simp only [hk, hq, Option.map_some, Option.getD_some]

/-- **A bit view's coordinate of the decoded valuation is the input its view block holds.** -/
theorem inputValuation_view {u i q w : ℕ} {sel : IndexMap} (hk : (ir.value u).kind = .bits w sel)
    (hq : (ir.circuit c).viewPos u i = some q) :
    ir.inputValuation I c x r v u i = castElt (vecRead v q) := by
  unfold inputValuation
  simp only [hk, hq, Option.map_some, Option.getD_some]

/-- **A public value's coordinate of the decoded valuation is the input its public block holds.** -/
theorem inputValuation_pub {u i q : ℕ} (hk : (ir.value u).kind.readsPubBlock = true)
    (hq : (ir.circuit c).pubPos u i = some q) :
    ir.inputValuation I c x r v u i = castElt (vecRead v q) := by
  unfold inputValuation
  rcases hk' : (ir.value u).kind with _ | _ | _ | _ | _ | _ | _ | _ | _ <;>
    rw [hk'] at hk <;> simp only [Kind.readsPubBlock, Bool.false_eq_true] at hk <;>
    simp only [hq, Option.map_some, Option.getD_some]

/-- **The position of a coordinate of a value with one committed block**: the block's. -/
theorem committedPos_eq_of_mem {u a n i : ℕ}
    (hb : InputBlock.committed u a n ∈ (ir.circuit c).inputs) (hi : i < n)
    (hu : ∀ a' n', InputBlock.committed u a' n' ∈ (ir.circuit c).inputs → a' = a) :
    (ir.circuit c).committedPos u i = some (a + i) := by
  cases hq : (ir.circuit c).committedPos u i with
  | none =>
    have := List.findSome?_eq_none_iff.1 hq _ hb
    simp only [InputBlock.committedPos, true_and, if_pos hi] at this
    cases this
  | some q =>
    obtain ⟨a', n', hb', -, rfl⟩ := exists_committed_block hq
    rw [hu a' n' hb']

/-- **The position of a coordinate of a bit view with one view block**: the block's. -/
theorem viewPos_eq_of_mem {u a n i : ℕ}
    (hb : InputBlock.view u a n ∈ (ir.circuit c).inputs) (hi : i < n)
    (hu : ∀ a' n', InputBlock.view u a' n' ∈ (ir.circuit c).inputs → a' = a) :
    (ir.circuit c).viewPos u i = some (a + i) := by
  cases hq : (ir.circuit c).viewPos u i with
  | none =>
    have := List.findSome?_eq_none_iff.1 hq _ hb
    simp only [InputBlock.viewPos, true_and, if_pos hi] at this
    cases this
  | some q =>
    obtain ⟨a', n', hb', -, rfl⟩ := exists_view_block hq
    rw [hu a' n' hb']

/-- **The public block holding a public coordinate.** -/
theorem exists_pub_block {u i q : ℕ} (hq : (ir.circuit c).pubPos u i = some q) :
    ∃ a n, InputBlock.pub u a n ∈ (ir.circuit c).inputs ∧ i < n ∧ q = a + i := by
  obtain ⟨b, hb, hbq⟩ := List.exists_of_findSome?_eq_some hq
  cases b <;> simp only [InputBlock.pubPos, reduceCtorEq] at hbq
  rename_i u' a n
  split_ifs at hbq with h'
  cases hbq
  obtain ⟨rfl, hi⟩ := h'
  exact ⟨a, n, hb, hi, rfl⟩

/-- **The position of a coordinate of a value with one public block**: the block's. -/
theorem pubPos_eq_of_mem {u a n i : ℕ}
    (hb : InputBlock.pub u a n ∈ (ir.circuit c).inputs) (hi : i < n)
    (hu : ∀ a' n', InputBlock.pub u a' n' ∈ (ir.circuit c).inputs → a' = a) :
    (ir.circuit c).pubPos u i = some (a + i) := by
  cases hq : (ir.circuit c).pubPos u i with
  | none =>
    have := List.findSome?_eq_none_iff.1 hq _ hb
    simp only [InputBlock.pubPos, true_and, if_pos hi] at this
    cases this
  | some q =>
    obtain ⟨a', n', hb', -, rfl⟩ := exists_pub_block hq
    rw [hu a' n' hb']

/-- **A committed value of the decoded valuation is the decoded committed assignment's**
(`inputAssignment`): its committed block's inputs, `0` where it has none. -/
theorem inputValuation_of_priv {w : ℕ} (hk : (ir.value w).kind = .priv) :
    ir.inputValuation I c x r v w = (ir.inputAssignment I c (vecRead v)).val w := by
  funext j
  unfold inputValuation
  simp only [hk]
  cases hq : (ir.circuit c).committedPos w j with
  | none =>
    simp [reader_of_priv _ hk, layoutEnv, ir.bindAsg_val_of_isBound (v := w) _ (by rw [hk]; rfl)]
  | some q => simp [inputAssignment, hq]

/-- **Under the proof system's premises, a bit view of the decoded valuation reads the bits of its
committed words there** (`InputPremises.views`): coordinate `i` is bit `i mod e` of word
`sel[i / e]` of `w` (`bitView`), `w` read by the decoded valuation. -/
theorem inputValuation_view_bits (hP : ir.InputPremises I c x r v) {u w : ℕ} {sel : IndexMap}
    (hk : (ir.value u).kind = .bits w sel) (hw : (ir.value w).kind = .priv) (i : ℕ) :
    ir.inputValuation I c x r v u i = ir.bitView (ir.inputValuation I c x r v) u w sel i := by
  rw [hP.views u w sel hk i]
  obtain ⟨m, hm⟩ : ∃ m, ir.fuel = m + 1 + 1 := ⟨ir.values.length - 1, by
    have := lt_of_kind_bits hk
    simp only [fuel]
    omega⟩
  have hrw : ir.read (ir.layoutEnv I x (ir.bindAsg (ir.inputAssignment I c (vecRead v))) r)
      (m + 1) w = ir.inputValuation I c x r v w := by
    rw [inputValuation_of_priv hw]
    funext j
    simp [read, hw, layoutEnv, ir.bindAsg_val_of_isBound (v := w) _ (by rw [hw]; rfl)]
  unfold inputBase reader
  rw [hm, read]
  simp only [hk, bitView]
  rw [hrw]

/-! ## The decoded valuation is the semantics' reading -/

/-- **The decoded committed assignment's pads are zero off the late values' coordinates**, when
every pad block holds coordinates of a late value. -/
theorem padsAgreeOff_inputAssignment (hL : ir.InputLayoutOk c) (w : ℕ → (I (ir.circField c)).K) :
    ir.PadsAgreeOff I ⟨0, 0⟩ (ir.bindAsg (ir.inputAssignment I c w)) := by
  intro u i hu
  change (0 : (I (ir.valueField u)).K) =
    (((ir.circuit c).padPos u i).map fun p => castElt (w p)).getD 0
  cases hq : (ir.circuit c).padPos u i with
  | none => rfl
  | some q =>
    obtain ⟨a, n, hb, hi, -⟩ := exists_pad_block hq
    obtain ⟨h1, h2, h3⟩ := hL.pad u a n hb
    exact absurd ⟨h1, h2, by omega⟩ hu

/-- **The decoded valuation is the semantics' reading** (`inputBase`): on a vector whose public
inputs are the verifier's and on which the proof system's premises hold, in a layout placed as the
plan places it. A committed coordinate is the decoded committed assignment's by definition; a bit
view's is the premise `InputPremises.views`; a public value's is the verifier's public input, the
value read at the zero committed assignment, which it does not read (`reader_eq_of_pubB`). -/
theorem inputValuation_eq_inputBase (hL : ir.InputLayoutOk c)
    (hfit : (ir.circuit c).inputCount ≤ 2 ^ d)
    (hpub : ∀ j : Fin (2 ^ d), (ir.circuit c).IsPublicPos j → v j = ir.publicInput I c x r j)
    (hP : ir.InputPremises I c x r v) :
    ir.inputValuation I c x r v = ir.inputBase I c x r v := by
  have hpub' : ∀ j, j < (ir.circuit c).publicInputs → vecRead v j = ir.publicInput I c x r j :=
    fun j hj => by
      have := hL.pubLe
      rw [vecRead, dif_pos (by omega)]
      exact hpub ⟨j, by omega⟩ hj
  funext u i
  rcases hk : (ir.value u).kind with _ | _ | _ | _ | _ | ⟨w, sel⟩ | _ | _ | _
  case bits => exact hP.views u w sel hk i
  case priv =>
    unfold inputValuation inputBase
    simp only [hk]
    cases hq : (ir.circuit c).committedPos u i with
    | none => rfl
    | some q =>
      simp [reader_of_priv _ hk, layoutEnv, ir.bindAsg_val_of_isBound (v := u) _ (by rw [hk]; rfl),
        inputAssignment, hq]
  case padCopy =>
    unfold inputValuation inputBase
    simp only [hk]
    cases hq : (ir.circuit c).committedPos u i with
    | none => rfl
    | some q =>
      simp [reader_of_padCopy _ hk, layoutEnv,
        ir.bindAsg_val_of_isBound (v := u) _ (by rw [hk]; rfl), inputAssignment, hq]
  case late =>
    unfold inputValuation inputBase
    simp only [hk]
  all_goals
    unfold inputValuation inputBase
    simp only [hk]
    cases hq : (ir.circuit c).pubPos u i with
    | none => rfl
    | some q =>
      obtain ⟨a, n, hb, hi, rfl⟩ := exists_pub_block hq
      obtain ⟨hf, hpb, ha, han⟩ := hL.pub u a n hb
      have hnl : ¬ ir.IsLate u := fun hl => by simp [IsLate, hk, Kind.isLate] at hl
      have hpb : ir.pubB ir.fuel u = true := hpb.resolve_left hnl
      have hval : ((InputBlock.pub u a n).pubValue?
          (fun u i => (castElt (ir.reader (ir.layoutEnv I x ⟨0, 0⟩ r) u i) :
            (I (ir.circField c)).K))
          (ir.realPubValue I c r) (a + i)) =
            some (castElt (ir.reader (ir.layoutEnv I x ⟨0, 0⟩ r) u i)) := by
        simp only [InputBlock.pubValue?]
        rw [if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel_left]
      have hfind := InputBlock.findSome_pubValue? hL.layout _ hb hval
      have hne : a + i ≠ 0 := by omega
      simp only [Option.map_some, Option.getD_some]
      rw [hpub' (a + i) (by omega), publicInput, if_neg hne, hfind, Option.getD_some,
        castElt_castElt_of_eq hf,
        reader_eq_of_pubB (padsAgreeOff_inputAssignment hL (vecRead v)) hpb]

/-- **Bound values read their expressions at the decoded valuation** (`BoundReads`) whenever they do
at the semantics' reading (`inputBase`, the reader at a realized assignment, where
`boundReads_of_boundRecs` gives it): the two valuations are equal (`inputValuation_eq_inputBase`),
by the premise on the bit views. -/
theorem boundReads_inputValuation (hL : ir.InputLayoutOk c)
    (hfit : (ir.circuit c).inputCount ≤ 2 ^ d)
    (hpub : ∀ j : Fin (2 ^ d), (ir.circuit c).IsPublicPos j → v j = ir.publicInput I c x r j)
    (hP : ir.InputPremises I c x r v) (hB : ir.BoundReads (ir.inputBase I c x r v)) :
    ir.BoundReads (ir.inputValuation I c x r v) := by
  rw [inputValuation_eq_inputBase hL hfit hpub hP]
  exact hB

/-! ## The reader premises of the views -/

section

variable (ir : RealizedProgram) {I : Interp}

/-- **Value `m` publishes the message of late value `u`**: `m` is `u` itself, whose public block
holds its message (a circuit's plan names a late value's message slot by the late value,
`lib/gordiehowe/compiler/program_builder.h`), or a value of kind `message u`. -/
def MessageOf (m u : ℕ) : Prop := m = u ∨ (ir.value m).kind = .message u

/-- **The late model** of circuit `c` at the reader `rd` and the node values `val`: a coordinate of
a late value `u` of the circuit's field is its message's input minus its pad's input, wherever a
value `m` publishing its message (`MessageOf`) has its coordinate in a public block and the pad in a
pad block, both below `inputs`. The emitter reads a late value as `sub(t, P)` of these two inputs
(`lib/gordiehowe/compiler/compiled_domain.h`, `CompiledDomain::view`). -/
def LateModel (rd : ir.Valuation I) (c : ℕ) (val : ℕ → (I (ir.circField c)).K) (inputs : ℕ) :
    Prop :=
  ∀ u m i qm qp, ir.MessageOf m u → ir.valueField u = ir.circField c →
    (ir.circuit c).pubPos m i = some qm → (ir.circuit c).padPos u i = some qp → qm < inputs →
    qp < inputs → (castElt (rd u i) : (I (ir.circField c)).K) = val qm - val qp

/-- **Every public expression reads its expression** at the reader `rd`: a value of kind
`pub (expr x)` (a derived value of the C++ builder, `lib/gordiehowe/compiler/program_builder.h`)
reads as `x`. A realization circuit reading a derived value through `.leaf` needs it. -/
def ExprReads (rd : ir.Valuation I) : Prop :=
  ∀ u < ir.values.length, ∀ x, (ir.value u).kind = .pub (.expr x) →
    rd u = ir.evalE rd (ir.valueField u) x

end

/-! ## The reader premises at the decoded valuation -/

/-- **A well-formed program reads its values in identifier order** (`ValuesOrdered`): a public
expression's or opaque function's arguments and a bit view's words have smaller identifiers
(`KindOk`). -/
theorem WellFormed.valuesOrdered (hwf : ir.WellFormed) : ir.ValuesOrdered := by
  intro v hv u hu
  have hk := (hwf.values v hv).2
  unfold valueDeps at hu
  rcases hkv : (ir.value v).kind with _ | ⟨_ | ⟨name, args⟩ | e⟩ | _ | _ | _ | ⟨w, sel⟩ | _ | _ | _ <;>
    rw [hkv] at hu hk <;> simp only [List.not_mem_nil] at hu
  · exact hk u hu
  · exact hk.2 u hu
  · rw [List.mem_singleton.1 hu]
    exact hk.1

/-- **The late model holds at the decoded valuation** (`LateModel`), at node values reading the
input vector: a late value's coordinate is the run's message minus its pad (`layoutEnv`), its
pad the pad block's input (`InputLayoutOk.pad`), and the public input of a value publishing its
message (`MessageOf`: the late value itself, or its message value) the run's message (`hpub`,
`InputLayoutOk.pub`). -/
theorem lateModel_inputValuation (hL : ir.InputLayoutOk c)
    (hfit : (ir.circuit c).inputCount ≤ 2 ^ d)
    (hpub : ∀ j : Fin (2 ^ d), (ir.circuit c).IsPublicPos j → v j = ir.publicInput I c x r j)
    {val : ℕ → (I (ir.circField c)).K} {inputs : ℕ} (hval : ∀ p < inputs, val p = vecRead v p) :
    ir.LateModel (ir.inputValuation I c x r v) c val inputs := by
  intro u m i qm qp hkm hf hqm hqp hqmI hqpI
  rw [hval qm hqmI, hval qp hqpI]
  obtain ⟨ap, np, hbp, hip, rfl⟩ := exists_pad_block hqp
  obtain ⟨hu, hlate, hnp⟩ := hL.pad u ap np hbp
  have hku : (ir.value u).kind = .late := by
    have h := hlate.1
    revert h
    cases (ir.value u).kind <;> simp [Kind.isLate]
  obtain ⟨am, nm, hbm, him, rfl⟩ := exists_pub_block hqm
  have hfm : ir.valueField m = ir.circField c := (hL.pub m am nm hbm).1
  have ham : 1 ≤ am := (hL.pub m am nm hbm).2.2.1
  have hamn : am + nm ≤ (ir.circuit c).publicInputs := (hL.pub m am nm hbm).2.2.2
  have hpm : vecRead v (am + i) = ir.publicInput I c x r (am + i) := by
    have := hL.pubLe
    rw [vecRead, dif_pos (by omega)]
    exact hpub ⟨am + i, by omega⟩ (show am + i < _ by omega)
  have hvm : ((InputBlock.pub m am nm).pubValue?
      (fun u i => (castElt (ir.reader (ir.layoutEnv I x ⟨0, 0⟩ r) u i) :
        (I (ir.circField c)).K))
      (ir.realPubValue I c r) (am + i)) =
        some (castElt (ir.reader (ir.layoutEnv I x ⟨0, 0⟩ r) m i)) := by
    simp only [InputBlock.pubValue?]
    rw [if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel_left]
  have hcond : u < ir.values.length ∧ ir.IsLate u ∧ i < (ir.value u).size :=
    ⟨hu, hlate, by omega⟩
  rw [hpm, publicInput, if_neg (by omega), InputBlock.findSome_pubValue? hL.layout _ hbm hvm,
    Option.getD_some]
  rcases hkm with rfl | hkm
  · rw [reader_of_late _ hku]
    unfold inputValuation
    simp only [hku]
    rw [reader_of_late _ hku]
    simp only [layoutEnv, if_pos hcond, bindAsg, inputAssignment, hqp, Option.map_some,
      Option.getD_some]
    rw [castElt_sub, castElt_sub, castElt_castElt_of_eq hf.symm]
    simp
  · rw [reader, fuel, read]
    simp only [hkm]
    unfold inputValuation
    simp only [hku]
    rw [reader_of_late _ hku]
    simp only [layoutEnv, if_pos hcond, bindAsg, inputAssignment, hqp, Option.map_some,
      Option.getD_some]
    rw [castElt_sub, castElt_castElt_of_eq hf.symm, castElt_castElt_eq,
      if_pos (hf.trans hfm.symm), castElt_add]
    simp

/-- **Every public expression reads its expression at the decoded valuation** (`ExprReads`): the
decoded valuation is the semantics' reading (`inputValuation_eq_inputBase`), where a public
expression reads its expression one level down (`reader_of_pubExpr`), at values of smaller
identifier, whose readings the extra level does not change (`read_stable`). -/
theorem exprReads_inputValuation (hwf : ir.WellFormed) (hL : ir.InputLayoutOk c)
    (hfit : (ir.circuit c).inputCount ≤ 2 ^ d)
    (hpub : ∀ j : Fin (2 ^ d), (ir.circuit c).IsPublicPos j → v j = ir.publicInput I c x r j)
    (hP : ir.InputPremises I c x r v) : ir.ExprReads (ir.inputValuation I c x r v) := by
  rw [inputValuation_eq_inputBase hL hfit hpub hP]
  intro u hu e hk
  funext i
  have hdep := (hwf.values u hu).2
  rw [hk] at hdep
  unfold inputBase
  conv_lhs => rw [reader, fuel, read]
  simp only [hk]
  refine congrFun (evalE_congr fun w hw => ?_) i
  have hw' : w < u := hdep.2 w hw
  show ir.read _ ir.values.length w = ir.read _ ir.fuel w
  exact (read_stable hwf.valuesOrdered _ (by omega) (by omega) (by simp [fuel])).symm

end GordieHowe.RealizedProgram
