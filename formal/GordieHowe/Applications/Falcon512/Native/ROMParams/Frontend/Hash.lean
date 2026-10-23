-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Library.Keccak
public import GordieHowe.Applications.Falcon512.Native.ROMParams.Frontend.HashData
public import GordieHowe.Language.RealizedProgram.Encoding

@[expose] public section

/-!
# GordieHowe frontend: native Falcon, the SHAKE256 call

The instance of the frontend's hash view (`GordieHowe.Falcon512.Native.ROMParams.FalconHashView`) for a native Falcon
program (`falconHashView`), generic in the program and its fields (`falconInterpOf FH FA`) at the
program facts `FalconHHash` (decided per program): the program's `h2p.shake` is SHAKE256 of the
nonce and the message, at the private length `L ≤ 32` its in-message flags encode, over a batch of
ten Keccak-f permutations (one absorb, nine squeezes; `240` round predicates):

* **the rounds** (`permRelation`): permutation `p`'s round `t` is the round relation
  (`GordieHowe.RealizedProgram.roundRelation_of_shapes` at the decided shapes `roundShapes` and index maps
  `keccakMaps`, `GordieHowe/Applications/Falcon512/Native/ROMParams/Frontend/HashData.lean`) between its states `permStates p t`;
* **the squeezes' inputs** (`permStates_one_zero`, `permStates_succ_zero`): the first squeeze reads
  `h2p.shake.state`, the absorb permutation's output by `h2p.shake.padding.output`
  (`evalE_state`), every later one the previous permutation's output;
* **the absorbed block** (`absorbed_eq`): the buffer `nonce ‖ message part` is the input's
  `40 + L` bytes (`bufInput`) followed by FIPS 202's `pad10*1` with SHAKE256's suffix: the
  in-message flags are the prefix of length `40 + L` (`flag_iff`: `padding.monotone`, `min`,
  `max`), and `padding.suffix` and `padding.zeros` fix the bytes past it through their packing in
  the subfield basis `g^0, …, g^7` of `FH`'s selection field (`bufBit_pad`, `bits_eq_of_packed`);
* **the hash's soundness** (`squeeze_sound`): `Shake256.squeezeOut_sound` at those permutations;
* **the stream** (`selSample_eq`): the selection's samples are the squeezed bytes two per sample,
  read off the output views (`evalE_stream`: the stream's index maps as segments, `idx_stream`;
  `evalE_view`: the views are bit views of the permutation outputs' words).
-/

namespace GordieHowe.Falcon512.Native.ROMParams

open Generated.Falcon512.Native.ROMParams.Program hiding program
open GordieHowe.Bits GordieHowe.Keccak GordieHowe.KeccakTrace

variable {program : RealizedProgram} {FH FA : RealizedProgram.FieldInterp}

set_option hygiene false in
local notation "interp" => RealizedProgram.falconInterpOf FH FA

/-- **The program facts of `h2p.shake`'s inputs, padding and output views** (each program
instantiates them by `decide`): the hash's predicates `0 … 245` source predicates, the squeezes'
inputs, the in-message flags and the padding predicates, the absorbed block and the padding
constants, the stream `489` and the output views. -/
class FalconHHash (program : RealizedProgram) : Prop extends FalconHHashData program where
  /-- The predicates of `h2p.shake` are source predicates, decided. -/
  shake_source : ∀ q < 246, q < program.predicates.length ∧
      program.inSource (program.predicate q) = true
  /-- expr_squeezeIn. -/
  expr_squeezeIn : program.expr 53 = .reindex idx24 (.concat (.leaf 26) (.leaf 0)) ∧
      program.expr 54 = .add (.reindex idx25 (.ref 53)) (.reindex idx26 (.ref 53)) ∧
      program.expr 55 = .reindex idx7 (.leaf 95) ∧ program.expr 56 = .reindex idx7 (.leaf 97) ∧
      program.predicate 29 = «p.h2p.shake.padding.output»
  /-- Facts of the absorbed block's selector and the squeezes' inputs, decided. -/
  squeezeIn_facts : idx24.entry 0 = 0 ∧ idx24.entry 1 = 1 ∧ idx25.entry 0 = 0 ∧
      idx26.entry 0 = 1 ∧ (∀ j < 1600, idx27.entry j = 0) ∧ (∀ j < 1600, idx7.entry j = j) ∧
      idx27.size = 1600 ∧ (program.value 26).size = 1 ∧ program.isConstant 26 = true ∧
      program.isConstant 0 = true ∧ program.valueField 26 = 0 ∧ program.valueField 0 = 0 ∧
      (program.constEntries 26).getD 0 0 = 1 ∧ (program.constEntries 0).getD 0 0 = 0 ∧
      29 < program.predicates.length ∧ program.inSource (program.predicate 29) = true ∧
      56 < program.exprs.length
  /-- pred_padding. -/
  pred_padding : program.predicate 24 = «p.h2p.shake.padding.monotone» ∧
      program.predicate 25 = «p.h2p.shake.padding.max» ∧
      program.predicate 26 = «p.h2p.shake.padding.min» ∧
      program.predicate 27 = «p.h2p.shake.padding.suffix» ∧
      program.predicate 28 = «p.h2p.shake.padding.zeros»
  /-- Facts of the flags and the padding predicates, decided. -/
  flag_facts : (47 < program.values.length ∧ program.IsSourceValue 47 ∧
        (program.value 47).typeSource = .node ∧ (program.value 47).type = .bit) ∧
      (program.value 47).size = 136 ∧
      (∀ i < 135, idx16.entry i = i + 1) ∧ (∀ i < 135, idx17.entry i = i) ∧
      (∀ i < 135, idx18.entry i = 0) ∧ idx19.entry 0 = 72 ∧ idx20.entry 0 = 39 ∧
      idx16.size = 135 ∧ idx19.size = 1 ∧ idx20.size = 1 ∧
      program.isConstant 27 = true ∧ program.valueField 27 = 0 ∧
      (∀ i < 135, (program.constEntries 27).getD i 0 = 0) ∧
      (∀ p ∈ [24, 25, 26, 27, 28], p < program.predicates.length ∧
        program.inSource (program.predicate p) = true)
  /-- Facts of the absorbed block and the padding's constants, decided. -/
  absorb_facts :
    (∀ j < 1088, idx4.entry j = if j < 320 then j else 320) ∧
    (∀ j < 1088, idx5.entry j = if j < 320 then 768 else j - 320) ∧
    (∀ j < 1088, idx6.entry j = j) ∧ idx6.size = 1088 ∧
    (∀ i < 136, idx21.entry i = i) ∧ (∀ i < 136, ∀ t < 8, idx22.entry (i * 8 + t) = t) ∧
    (∀ i < 136, idx23.entry i = 0) ∧ idx21.size = 136 ∧ idx17.size = 135 ∧
    (program.value 45).size = 320 ∧ (program.value 46).size = 768 ∧ (program.value 0).size = 1 ∧
    program.constEntries 1 = List.replicate 512 0 ∧
    (∀ t < 8, (program.constEntries 28).getD t 0 = (program.constEntries 39).getD t 0) ∧
    (∀ i < 135, (program.constEntries 29).getD i 0 =
      (program.constEntries 39).getD 0 0 ^^^ (program.constEntries 39).getD 1 0 ^^^
      (program.constEntries 39).getD 2 0 ^^^ (program.constEntries 39).getD 3 0 ^^^
      (program.constEntries 39).getD 4 0) ∧
    (∀ i < 136, (program.constEntries 30).getD i 0 = 0) ∧
    (∀ i < 135, (program.constEntries 31).getD i 0 = 0) ∧
    (program.constEntries 31).getD 135 0 = (program.constEntries 39).getD 7 0 ∧
    (∀ v ∈ [1, 28, 29, 30, 31], program.isConstant v = true ∧ program.valueField v = 0)
  /-- expr_absorb. -/
  expr_absorb : program.expr 0 =
        .add (.reindex idx4 (.concat (.leaf 45) (.leaf 0)))
          (.reindex idx5 (.concat (.leaf 46) (.leaf 0))) ∧
      program.expr 1 = .reindex idx6 (.ref 0) ∧
      program.expr 2 =
        .reindex idx7 (.reindex idx7 (.concat (.reindex idx6 (.reindex idx6 (.ref 1))) (.leaf 1))) ∧
      program.expr 51 = .reindex idx21 (.concat (.leaf 26) (.reindex idx17 (.leaf 47))) ∧
      program.expr 52 = .apply (.sum 8) (.mul (.reindex idx6 (.reindex idx6 (.ref 1)))
        (.reindex idx22 (.leaf 28)))
  /-- expr489. -/
  expr489 : program.expr 489 =
      .add (.add (.add (.add (.add (.add (.add (.add (.add
        (.reindex idx30 (.concat (.leaf 97) (.leaf 0)))
        (.reindex idx31 (.concat (.leaf 146) (.leaf 0))))
        (.reindex idx32 (.concat (.leaf 195) (.leaf 0))))
        (.reindex idx33 (.concat (.leaf 244) (.leaf 0))))
        (.reindex idx34 (.concat (.leaf 293) (.leaf 0))))
        (.reindex idx35 (.concat (.leaf 342) (.leaf 0))))
        (.reindex idx36 (.concat (.leaf 391) (.leaf 0))))
        (.reindex idx37 (.concat (.leaf 440) (.leaf 0))))
        (.reindex idx38 (.concat (.leaf 489) (.leaf 0))))
        (.reindex idx39 (.concat (.leaf 538) (.leaf 0)))
  /-- The views' sizes, decided. -/
  view_sizes : (program.value 97).size = 1600 ∧ (program.value 146).size = 1088 ∧
      (program.value 195).size = 1088 ∧ (program.value 244).size = 1088 ∧
      (program.value 293).size = 1088 ∧ (program.value 342).size = 1088 ∧
      (program.value 391).size = 1088 ∧ (program.value 440).size = 1088 ∧
      (program.value 489).size = 1088 ∧ (program.value 538).size = 432 ∧
      489 < program.exprs.length
  /-- **The output views and the permutation outputs** are bit views of the same committed words:
  view `k ≥ 1` (`h2p.shake.out.p_k`) with the selection `idx1` (`idx2` for the last), the output
  state of permutation `k` with `idx0`. -/
  view_kinds : ∀ k : Fin 9,
      (program.value (viewVal (k + 1))).kind =
          .bits (outVal (k + 1) 23 - 1) (if (k : ℕ) + 1 = 9 then idx2 else idx1) ∧
        (program.value (outVal (k + 1) 23)).kind = .bits (outVal (k + 1) 23 - 1) idx0 ∧
        (program.value (outVal (k + 1) 23 - 1)).kind = .priv
  /-- Facts of the views' selections, decided. -/
  view_sel : idx0.size = 100 ∧ idx1.size = 68 ∧ idx2.size = 27 ∧
      (∀ j < 100, idx0.entry j = j) ∧ (∀ j < 68, idx1.entry j = j) ∧ (∀ j < 27, idx2.entry j = j) ∧
      ∀ k : Fin 9, program.valueField (viewVal (k + 1)) = 0 ∧
        program.valueField (outVal (k + 1) 23) = 0 ∧ (program.value (outVal (k + 1) 23)).size = 1600 ∧
        (program.value (viewVal (k + 1))).size = zslot (k + 1)
  /-- Facts of the nonce and the message part, decided: bit-typed source values. -/
  buf_facts : (45 < program.values.length ∧ program.IsSourceValue 45 ∧
        (program.value 45).typeSource = .node ∧ (program.value 45).type = .bit) ∧
      (46 < program.values.length ∧ program.IsSourceValue 46 ∧
        (program.value 46).typeSource = .node ∧ (program.value 46).type = .bit)

open FalconHHash FalconHHashData

variable [HField FH] [AField FA] [FalconHBase program] [FalconHConsts program FH]
  [FalconSelField program FH FA] [FalconHHash program]

/-! ## The rounds -/

/-- `0` decodes to `0` in `FH`. -/
theorem decodeH_zero : (interp 0).decode 0 = 0 := HField.decode_zero

/-- `1` decodes to `1` in `FH`. -/
theorem decodeH_one : (interp 0).decode 1 = 1 := HField.decode_one

/-- Decoding in `FH` is additive on xors. -/
theorem decodeH_xor (a b : ℕ) :
    (interp 0).decode (a ^^^ b) = (interp 0).decode a + (interp 0).decode b :=
  HField.decode_xor a b

/-- A `0`/`1` entry decodes to itself in `FH`. -/
theorem decode_bit (c : Prop) [Decidable c] : (interp 0).decode (if c then 1 else 0) =
    (if c then 1 else 0 : (interp 0).K) := by
  by_cases hc : c
  · rw [if_pos hc, if_pos hc]
    exact decodeH_one
  · rw [if_neg hc, if_neg hc]
    exact decodeH_zero

theorem evalE_ones (e : program.Env interp) {j : ℕ} (hj : j < 1600) :
    program.evalE (program.reader e) 0 (.leaf 2) j = 1 := by
  rw [RealizedProgram.evalE_leaf_of_isConstant e (const_states (program := program)).2.2.1,
    RealizedProgram.constRead_of_valueField (const_states (program := program)).2.2.2.2.1, (const_states (program := program)).1,
    List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos hj, Option.getD_some]
  exact decodeH_one

theorem evalE_zeros (e : program.Env interp) {j : ℕ} (hj : j < 1600) :
    program.evalE (program.reader e) 0 (.leaf 4) j = 0 := by
  rw [RealizedProgram.evalE_leaf_of_isConstant e (const_states (program := program)).2.2.2.1,
    RealizedProgram.constRead_of_valueField (const_states (program := program)).2.2.2.2.2, (const_states (program := program)).2.1,
    List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos hj, Option.getD_some]
  exact decodeH_zero

theorem evalE_rc (e : program.Env interp) (t : Fin 24) (x y : Fin 5) (z : Fin 64) :
    program.evalE (program.reader e) 0 (.leaf (rcLeaf t)) (RealizedProgram.keccakIdx x y z) =
      iotaVec t (x, y, z) := by
  obtain ⟨hent, hc, hf⟩ := (const_rc (program := program)) t
  rw [RealizedProgram.evalE_leaf_of_isConstant e hc, RealizedProgram.constRead_of_valueField hf, hent,
    List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact RealizedProgram.keccakIdx_lt x y z),
    List.getElem_ofFn]
  have hiff : (RealizedProgram.keccakIdx x y z < 64 ∧ (rc t).testBit (RealizedProgram.keccakIdx x y z)) ↔
      (x = 0 ∧ y = 0 ∧ (rc t).testBit z) := by
    unfold RealizedProgram.keccakIdx
    constructor
    · rintro ⟨h1, h2⟩
      have hx : (x : ℕ) = 0 := by omega
      have hy : (y : ℕ) = 0 := by omega
      refine ⟨Fin.ext hx, Fin.ext hy, ?_⟩
      rw [hx, hy] at h2
      simpa using h2
    · rintro ⟨rfl, rfl, h2⟩
      refine ⟨by simp, ?_⟩
      simpa using h2
  unfold iotaVec
  rw [decode_bit]
  exact if_congr hiff rfl rfl

instance : CharP (interp (program.domainField 0)).K 2 :=
  fieldAt_transfer (fun J => CharP J.K 2) FalconHBase.domainField0 HField.charTwo

/-- **The states of permutation `p`** (`roundSrc`), read in `FH`. -/
def permStates (e : program.Env interp) (p : Fin 10) (t : Fin 25) :
    State (interp 0).K :=
  RealizedProgram.stateOf (program.evalE (program.reader e) 0 (roundSrc p t).expr)

/-- **What the hash's lemmas read of the program**: the predicates of `h2p.shake` (`0 … 245`)
hold, and the nonce, the message part and the in-message flags (values `45`, `46`, `47`) read bits.
The source program gives it (`SourceSatAt.hashSat`); so does the honest prover directly. -/
structure HashSat (e : program.Env interp) : Prop where
  /-- The predicates of `h2p.shake` hold. -/
  preds : ∀ q < 246, program.HoldsAt e (program.predicate q).body
  /-- The nonce, the message part and the flags read bits. -/
  bits : ∀ v, (v = 45 ∨ v = 46 ∨ v = 47) → ∀ i < (program.value v).size,
    program.evalE (program.reader e) 0 (.leaf v) i = 0 ∨
      program.evalE (program.reader e) 0 (.leaf v) i = 1


/-- The predicate of round `t` of permutation `p` is one of `h2p.shake`'s. -/
theorem roundPred_lt (p : Fin 10) (t : Fin 24) : roundPred p t < 246 := by
  have := p.isLt
  have := t.isLt
  unfold roundPred
  split_ifs <;> omega

/-- **Every permutation's round relations hold** where the source program holds
(`RealizedProgram.roundRelation_of_shapes` at `(roundShapes (program := program))`). -/
theorem permRelation {e : program.Env interp} (hs : HashSat e) (p : Fin 10) :
    PermRelation (permStates e p) := by
  intro t
  obtain ⟨hb, hlin, hcol⟩ := (roundShapes (program := program)) p t
  obtain ⟨-, -, hL, hC, hsize⟩ := (round_facts (program := program)) p t
  have h := hs.preds _ (roundPred_lt p t)
  have hrel := RealizedProgram.roundRelation_of_shapes_at (r := t) (FalconHBase.refsOrdered (program := program))
    (FalconHBase.domainField0 (program := program)) hb hlin hcol hL hC keccakMaps
    hsize (fun j hj => evalE_ones e hj) (fun j hj => evalE_zeros e hj) (evalE_rc e t) h
  have hout : roundSrc p t.succ = .leaf (outVal p t) := by
    unfold roundSrc
    rw [if_neg (by simp)]
    simp
  unfold permStates
  rw [hout]
  exact hrel

/-! ## The squeezes' inputs -/

/-- A constant of domain `H` read in `FH`: its entry decoded. -/
theorem evalE_const0 (e : program.Env interp) {v : ℕ} (hc : program.isConstant v = true)
    (hf : program.valueField v = 0) (j : ℕ) :
    program.evalE (program.reader e) 0 (.leaf v) j =
      (interp 0).decode ((program.constEntries v).getD j 0) := by
  rw [RealizedProgram.evalE_leaf_of_isConstant e hc, RealizedProgram.constRead_of_valueField hf]



/-- **The absorbed block's selector is `1`** (`ref 54`: the one block of the buffer). -/
theorem evalE_selector (e : program.Env interp) :
    program.evalE (program.reader e) 0 (.ref 54) 0 = 1 := by
  obtain ⟨h0, h1, h25, h26, -, -, -, hs26, hc26, hc0, hf26, hf0, he26, he0, -, -, hlen⟩ :=
    (squeezeIn_facts (program := program))
  rw [RealizedProgram.evalE_ref (FalconHBase.refsOrdered (program := program)) _ _ (by omega), (expr_squeezeIn (program := program)).2.1, RealizedProgram.evalE_add,
    RealizedProgram.evalE_reindex, RealizedProgram.evalE_reindex, h25, h26,
    RealizedProgram.evalE_ref (FalconHBase.refsOrdered (program := program)) _ _ (by omega), (expr_squeezeIn (program := program)).1, RealizedProgram.evalE_reindex,
    RealizedProgram.evalE_reindex, h0, h1, RealizedProgram.evalE_concat, RealizedProgram.evalE_concat, RealizedProgram.exprLen_leaf,
    hs26, if_pos (by norm_num), if_neg (by norm_num), evalE_const0 e hc26 hf26,
    evalE_const0 e hc0 hf0, he26, show 1 - 1 = 0 from rfl, he0, decodeH_one,
    decodeH_zero]
  exact add_zero (1 : (interp 0).K)

/-- **The squeezes start from the absorb permutation's output** (`h2p.shake.padding.output`):
`h2p.shake.state` is the last absorb round's output (value `95`). -/
theorem evalE_state {e : program.Env interp} (hs : HashSat e) {j : ℕ} (hj : j < 1600) :
    program.evalE (program.reader e) 0 (.leaf 97) j =
      program.evalE (program.reader e) 0 (.leaf 95) j := by
  obtain ⟨-, -, -, -, h27, h7, hsz, -, -, -, -, -, -, -, -, -, hlen⟩ := (squeezeIn_facts (program := program))
  have h := hs.preds 29 (by norm_num)
  rw [(expr_squeezeIn (program := program)).2.2.2.2] at h
  have := holdsAt_equal0 h j (by
    rw [RealizedProgram.exprLen_mul, RealizedProgram.exprLen_reindex, hsz]
    exact hj)
  change program.evalE _ 0 _ j = program.evalE _ 0 (.leaf 4) j at this
  rw [evalE_zeros e hj, RealizedProgram.evalE_mul, RealizedProgram.evalE_reindex, h27 j hj, evalE_selector,
    one_mul, RealizedProgram.evalE_add, RealizedProgram.evalE_reindex, RealizedProgram.evalE_reindex, h7 j hj,
    RealizedProgram.evalE_ref (FalconHBase.refsOrdered (program := program)) _ _ (by omega), (expr_squeezeIn (program := program)).2.2.1, RealizedProgram.evalE_reindex,
    h7 j hj] at this
  exact (eq_neg_of_add_eq_zero_left this).trans (CharTwo.neg_eq _)

/-- **The first squeeze's input is the absorb permutation's output.** -/
theorem permStates_one_zero {e : program.Env interp} (hs : HashSat e) :
    permStates e 1 0 = permStates e 0 (Fin.last 24) := by
  have h1 : roundSrc 1 0 = .ref 56 := by decide
  have h2 : roundSrc 0 (Fin.last 24) = .leaf 95 := by decide
  unfold permStates
  rw [h1, h2]
  funext x y z
  have hj := RealizedProgram.keccakIdx_lt x y z
  obtain ⟨-, -, -, -, -, h7, -, -, -, -, -, -, -, -, -, -, hlen⟩ := (squeezeIn_facts (program := program))
  simp only [RealizedProgram.stateOf, RealizedProgram.StateSrc.expr]
  rw [RealizedProgram.evalE_ref (FalconHBase.refsOrdered (program := program)) _ _ hlen, (expr_squeezeIn (program := program)).2.2.2.1, RealizedProgram.evalE_reindex,
    h7 _ hj]
  exact evalE_state hs hj

/-- **A later squeeze's input is the previous permutation's output.** -/
theorem permStates_succ_zero (e : program.Env interp) {p : Fin 10} (hp : 2 ≤ (p : ℕ)) :
    permStates e p 0 = permStates e ⟨p - 1, by omega⟩ (Fin.last 24) := by
  unfold permStates roundSrc
  simp only [Fin.val_zero, Fin.val_last, if_true, show (p : ℕ) ≠ 0 by omega,
    show (p : ℕ) ≠ 1 by omega, if_false, show (24 : ℕ) ≠ 0 by decide]

/-! ## The in-message flags -/

/-- **In-message flag `i`** (value `47`), read in `FH`. -/
def flag (e : program.Env interp) (i : ℕ) : (interp 0).K :=
  program.evalE (program.reader e) 0 (.leaf 47) i

/-- A bit-typed source value of domain `H` (by its node) is `0` or `1` where the source program
holds. -/
theorem bool_of_bitTyped {e : program.Env interp} (hs : program.SourceSatAt e) {v : ℕ}
    (hv : v < program.values.length ∧ program.IsSourceValue v ∧
      (program.value v).typeSource = .node ∧ (program.value v).type = .bit)
    {i : ℕ} (hi : i < (program.value v).size) :
    program.evalE (program.reader e) 0 (.leaf v) i = 0 ∨
      program.evalE (program.reader e) 0 (.leaf v) i = 1 := by
  obtain ⟨hvl, hsrc, hts, hty⟩ := hv
  have h := hs.types v hvl hsrc hts i hi
  rw [hty] at h
  exact RealizedProgram.castElt_bool h



theorem flag_bool {e : program.Env interp} (hs : HashSat e) {i : ℕ} (hi : i < 136) :
    flag e i = 0 ∨ flag e i = 1 :=
  hs.bits 47 (by simp) i (by rw [(flag_facts (program := program)).2.1]; exact hi)

/-- In characteristic two, `x + 1 = 0` is `x = 1`. -/
theorem eq_one_of_add_one {x : (interp 0).K} (h : x + 1 = 0) : x = 1 :=
  (eq_neg_of_add_eq_zero_left h).trans (CharTwo.neg_eq 1)

/-- **`h2p.shake.padding.monotone`**: a set flag's predecessor is set. -/
theorem flag_mono {e : program.Env interp} (hs : HashSat e) {i : ℕ} (hi : i < 135)
    (h : flag e (i + 1) = 1) : flag e i = 1 := by
  obtain ⟨-, -, h16, h17, h18, -, -, hs16, -, -, hc27, hf27, he27, hp⟩ := (flag_facts (program := program))
  have hh := hs.preds 24 (by norm_num)
  rw [(pred_padding (program := program)).1] at hh
  have := holdsAt_equal0 hh i (by rw [RealizedProgram.exprLen_mul, RealizedProgram.exprLen_reindex, hs16]; exact hi)
  change program.evalE _ 0 _ i = program.evalE _ 0 (.leaf 27) i at this
  rw [evalE_const0 e hc27 hf27, he27 i hi, decodeH_zero, RealizedProgram.evalE_mul,
    RealizedProgram.evalE_add, RealizedProgram.evalE_reindex, RealizedProgram.evalE_reindex, RealizedProgram.evalE_reindex,
    h16 i hi, h17 i hi, h18 i hi, evalE_const0 e (squeezeIn_facts (program := program)).2.2.2.2.2.2.2.2.1
      (squeezeIn_facts (program := program)).2.2.2.2.2.2.2.2.2.2.1, (squeezeIn_facts (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.1,
    decodeH_one] at this
  change flag e (i + 1) * (flag e i + 1) = 0 at this
  rw [h, one_mul] at this
  exact eq_one_of_add_one this

/-- **`h2p.shake.padding.min`**: flag `39` (the nonce's last byte) is set. -/
theorem flag_39 {e : program.Env interp} (hs : HashSat e) : flag e 39 = 1 := by
  obtain ⟨-, -, -, -, -, -, h20, -, -, hs20, -, -, -, hp⟩ := (flag_facts (program := program))
  have hh := hs.preds 26 (by norm_num)
  rw [(pred_padding (program := program)).2.2.1] at hh
  have := holdsAt_equal0 hh 0 (by rw [RealizedProgram.exprLen_add, RealizedProgram.exprLen_reindex, hs20]; norm_num)
  change program.evalE _ 0 _ 0 = program.evalE _ 0 (.leaf 0) 0 at this
  rw [evalE_const0 e (squeezeIn_facts (program := program)).2.2.2.2.2.2.2.2.2.1 (squeezeIn_facts (program := program)).2.2.2.2.2.2.2.2.2.2.2.1,
    (squeezeIn_facts (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.1, decodeH_zero, RealizedProgram.evalE_add,
    RealizedProgram.evalE_reindex, h20, evalE_const0 e (squeezeIn_facts (program := program)).2.2.2.2.2.2.2.2.1
      (squeezeIn_facts (program := program)).2.2.2.2.2.2.2.2.2.2.1, (squeezeIn_facts (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.1,
    decodeH_one] at this
  exact eq_one_of_add_one this

/-- **`h2p.shake.padding.max`**: flag `72` (past the maximum message) is clear. -/
theorem flag_72 {e : program.Env interp} (hs : HashSat e) : flag e 72 = 0 := by
  obtain ⟨-, -, -, -, -, h19, -, -, hs19, -, -, -, -, hp⟩ := (flag_facts (program := program))
  have hh := hs.preds 25 (by norm_num)
  rw [(pred_padding (program := program)).2.1] at hh
  have := holdsAt_equal0 hh 0 (by rw [RealizedProgram.exprLen_reindex, hs19]; norm_num)
  change program.evalE _ 0 _ 0 = program.evalE _ 0 (.leaf 0) 0 at this
  rw [evalE_const0 e (squeezeIn_facts (program := program)).2.2.2.2.2.2.2.2.2.1 (squeezeIn_facts (program := program)).2.2.2.2.2.2.2.2.2.2.2.1,
    (squeezeIn_facts (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.1, decodeH_zero, RealizedProgram.evalE_reindex, h19]
    at this
  exact this

/-- The set flags are downward closed. -/
theorem flag_down {e : program.Env interp} (hs : HashSat e) {i j : ℕ} (hij : i ≤ j)
    (hj : j < 136) (h : flag e j = 1) : flag e i = 1 := by
  induction j, hij using Nat.le_induction with
  | base => exact h
  | succ k hik ih => exact ih (by omega) (flag_mono hs (by omega) h)

/-- **The in-message flags are the prefix of length `40 + lenOf`** (`padding.monotone`, `min`,
`max`): flag `i` is set exactly below `40 + L`, `L ≤ 32` the length the flags encode. -/
theorem flag_iff {e : program.Env interp} (hs : HashSat e) {i : ℕ} (hi : i < 136) :
    flag e i = 1 ↔ i < 40 + lenOf (program.reader e) := by
  have hex : ∃ k, k < 136 ∧ flag e k ≠ 1 := ⟨72, by norm_num, by rw [flag_72 hs]; exact zero_ne_one⟩
  classical
  set m := Nat.find hex with hm
  have hm136 : m < 136 := (Nat.find_spec hex).1
  have hmclear : flag e m ≠ 1 := (Nat.find_spec hex).2
  have hbelow : ∀ k < m, flag e k = 1 := fun k hk => by
    have := Nat.find_min hex hk
    exact not_not.1 (not_and.1 this (by omega))
  have habove : ∀ k, m ≤ k → k < 136 → flag e k ≠ 1 := fun k hk hk' h =>
    hmclear (flag_down hs hk hk' h)
  have hm72 : m ≤ 72 := Nat.find_min' hex ⟨by norm_num, by rw [flag_72 hs]; exact zero_ne_one⟩
  have hm40 : 40 ≤ m := by
    by_contra hlt
    exact hmclear (flag_down hs (by omega) (by norm_num) (flag_39 hs))
  have hcard : (Finset.univ.filter fun k : Fin 136 => flag e k = 1).card = m := by
    have hset : (Finset.univ.filter fun k : Fin 136 => flag e k = 1) =
        Finset.univ.filter fun k : Fin 136 => (k : ℕ) < m := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        by_contra hk
        exact habove k (by omega) k.isLt h
      · exact hbelow k
    rw [hset, Fin.card_filter_val_lt]
    omega
  have hlen : lenOf (program.reader e) = m - 40 := by
    unfold lenOf
    change min 32 ((Finset.univ.filter fun k : Fin 136 => flag e k = 1).card - 40) = _
    rw [hcard]
    omega
  rw [hlen]
  constructor
  · intro h
    by_contra hk
    exact habove i (by omega) hi h
  · intro h
    exact hbelow i (by omega)

/-! ## The absorbed block -/



/-- **Bit `j` of the hash buffer**: the nonce's `320` bits (value `45`), then the message part's
`768` (value `46`). -/
def bufBit (e : program.Env interp) (j : ℕ) : (interp 0).K :=
  if j < 320 then program.evalE (program.reader e) 0 (.leaf 45) j
  else program.evalE (program.reader e) 0 (.leaf 46) (j - 320)

/-- A constant of domain `H` padding a value reads `0` past it. -/
theorem evalE_concat0 (e : program.Env interp) {v n : ℕ} (hn : (program.value v).size = n)
    {j : ℕ} (hj : n ≤ j) (hj' : j ≤ n) :
    program.evalE (program.reader e) 0 (.concat (.leaf v) (.leaf 0)) j = 0 := by
  rw [RealizedProgram.evalE_concat, RealizedProgram.exprLen_leaf, hn, if_neg (by omega),
    show j - n = 0 by omega, evalE_const0 e (squeezeIn_facts (program := program)).2.2.2.2.2.2.2.2.2.1
      (squeezeIn_facts (program := program)).2.2.2.2.2.2.2.2.2.2.2.1, (squeezeIn_facts (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.1]
  exact decodeH_zero

theorem evalE_ref0 (e : program.Env interp) {j : ℕ} (hj : j < 1088) :
    program.evalE (program.reader e) 0 (.ref 0) j = bufBit e j := by
  obtain ⟨h4, h5, -, -, -, -, -, -, -, hs45, hs46, -⟩ := (absorb_facts (program := program))
  have hlen := (squeezeIn_facts (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rw [RealizedProgram.evalE_ref (FalconHBase.refsOrdered (program := program)) _ _ (by omega), (expr_absorb (program := program)).1, RealizedProgram.evalE_add,
    RealizedProgram.evalE_reindex, RealizedProgram.evalE_reindex, h4 j hj, h5 j hj, bufBit]
  by_cases h : j < 320
  · rw [if_pos h, if_pos h, if_pos h, evalE_concat0 e hs46 le_rfl le_rfl, add_zero,
      RealizedProgram.evalE_concat, RealizedProgram.exprLen_leaf, hs45, if_pos h]
  · rw [if_neg h, if_neg h, if_neg h, evalE_concat0 e hs45 le_rfl le_rfl, zero_add,
      RealizedProgram.evalE_concat, RealizedProgram.exprLen_leaf, hs46, if_pos (by omega)]

theorem evalE_ref1 (e : program.Env interp) {j : ℕ} (hj : j < 1088) :
    program.evalE (program.reader e) 0 (.ref 1) j = bufBit e j := by
  have hlen := (squeezeIn_facts (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rw [RealizedProgram.evalE_ref (FalconHBase.refsOrdered (program := program)) _ _ (by omega), (expr_absorb (program := program)).2.1, RealizedProgram.evalE_reindex,
    (absorb_facts (program := program)).2.2.1 j hj, evalE_ref0 e hj]

/-- **The absorbed block** (`ref 2`): the buffer's `1088` bits, then the capacity's zeros. -/
theorem evalE_ref2 (e : program.Env interp) {j : ℕ} (hj : j < 1600) :
    program.evalE (program.reader e) 0 (.ref 2) j = if j < 1088 then bufBit e j else 0 := by
  have hlen := (squeezeIn_facts (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨-, -, h6, hs6, -, -, -, -, -, -, -, -, h1, -, -, -, -, -, hc⟩ := (absorb_facts (program := program))
  rw [RealizedProgram.evalE_ref (FalconHBase.refsOrdered (program := program)) _ _ (by omega), (expr_absorb (program := program)).2.2.1, RealizedProgram.evalE_reindex,
    RealizedProgram.evalE_reindex, (squeezeIn_facts (program := program)).2.2.2.2.2.1 j hj, (squeezeIn_facts (program := program)).2.2.2.2.2.1 j hj,
    RealizedProgram.evalE_concat, RealizedProgram.exprLen_reindex, hs6]
  split_ifs with h
  · rw [RealizedProgram.evalE_reindex, RealizedProgram.evalE_reindex, h6 j h, h6 j h, evalE_ref1 e h]
  · rw [evalE_const0 e (hc 1 (by simp)).1 (hc 1 (by simp)).2, h1, List.getD_eq_getElem?_getD,
      List.getElem?_replicate,
      if_pos (by omega), Option.getD_some]
    exact decodeH_zero

/-- **The shifted flags** (`ref 51`): `1` at byte `0`, then flag `i − 1`. -/
theorem evalE_ref51 (e : program.Env interp) {i : ℕ} (hi : i < 136) :
    program.evalE (program.reader e) 0 (.ref 51) i = if i = 0 then 1 else flag e (i - 1) := by
  have hlen := (squeezeIn_facts (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rw [RealizedProgram.evalE_ref (FalconHBase.refsOrdered (program := program)) _ _ (by omega), (expr_absorb (program := program)).2.2.2.1, RealizedProgram.evalE_reindex,
    (absorb_facts (program := program)).2.2.2.2.1 i hi, RealizedProgram.evalE_concat, RealizedProgram.exprLen_leaf,
    (squeezeIn_facts (program := program)).2.2.2.2.2.2.2.1]
  split_ifs with h1 h2 h2
  · rw [h2, evalE_const0 e (squeezeIn_facts (program := program)).2.2.2.2.2.2.2.2.1
      (squeezeIn_facts (program := program)).2.2.2.2.2.2.2.2.2.2.1, (squeezeIn_facts (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.1]
    exact decodeH_one
  · omega
  · omega
  · rw [RealizedProgram.evalE_reindex, (flag_facts (program := program)).2.2.2.1 (i - 1) (by omega)]
    rfl

/-- **The subfield's generator** `g` of `FH`'s selection field (`HField.sel`). -/
abbrev gH : FH.K := (HField.sel (FH := FH)).g

/-- **Entry `j` of the constant `39` decodes to `g^j`** (`FalconHConsts.gpow`). -/
theorem decodeH_gpow : ∀ j < 512,
    (interp 0).decode ((program.constEntries 39).getD j 0) = (gH (FH := FH)) ^ j :=
  FalconHConsts.gpow

/-- **The packed buffer byte `i`** (`ref 52`): `Σ_t bit(8 i + t) g^t`, `g` the subfield's
generator (the constant `28`, the first entries of `39`). -/
theorem evalE_ref52 (e : program.Env interp) {i : ℕ} (hi : i < 136) :
    program.evalE (program.reader e) 0 (.ref 52) i =
      ∑ t : Fin 8, bufBit e (8 * i + t) * gH ^ (t : ℕ) := by
  have hlen := (squeezeIn_facts (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨-, -, h6, -, -, h22, -, -, -, -, -, -, -, h28, -, -, -, -, hc⟩ := (absorb_facts (program := program))
  rw [RealizedProgram.evalE_ref (FalconHBase.refsOrdered (program := program)) _ _ (by omega), (expr_absorb (program := program)).2.2.2.2, RealizedProgram.evalE_apply_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  have ht := t.isLt
  rw [RealizedProgram.evalE_mul, RealizedProgram.evalE_reindex, RealizedProgram.evalE_reindex, RealizedProgram.evalE_reindex,
    h6 (i * 8 + t) (by omega), h6 (i * 8 + t) (by omega), evalE_ref1 e (by omega), h22 i hi t ht,
    evalE_const0 e (hc 28 (by simp)).1 (hc 28 (by simp)).2, h28 t ht,
    decodeH_gpow t (by omega), show i * 8 + (t : ℕ) = 8 * i + t by ring]

variable (program) in
/-- **Entry `i` of a constant of domain `H`**, decoded in `FH`. -/
abbrev constH (v i : ℕ) : (interp 0).K :=
  (interp 0).decode ((program.constEntries v).getD i 0)

/-- **The packed byte of the suffix**: `0x1F` packed (`g^0 + … + g^4`), entry `i < 135` of the
constant `29`. -/
theorem const29 {i : ℕ} (hi : i < 135) :
    constH program 29 i =
      ∑ t : Fin 8, Bits.constBit (K := (interp 0).K) 0x1F t * gH ^ (t : ℕ) := by
  rw [constH, (absorb_facts (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i hi, decodeH_xor, decodeH_xor,
    decodeH_xor, decodeH_xor, decodeH_gpow 0 (by norm_num),
    decodeH_gpow 1 (by norm_num), decodeH_gpow 2 (by norm_num),
    decodeH_gpow 3 (by norm_num), decodeH_gpow 4 (by norm_num)]
  simp only [Fin.sum_univ_eight, Bits.constBit]
  norm_num

/-- **The packed byte `0x80`** (`g^7`), entry `135` of the constant `31`; its other entries `0`. -/
theorem const31 {i : ℕ} (hi : i < 136) :
    constH program 31 i =
      ∑ t : Fin 8,
        Bits.constBit (K := (interp 0).K) (if i = 135 then 0x80 else 0) t * gH ^ (t : ℕ) := by
  by_cases h : i = 135
  · subst h
    rw [constH, (absorb_facts (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, decodeH_gpow 7 (by norm_num),
      if_pos rfl]
    simp only [Fin.sum_univ_eight, Bits.constBit]
    norm_num
  · rw [constH, (absorb_facts (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i (by omega), decodeH_zero,
      if_neg h]
    simp [Bits.constBit]

/-- **`h2p.shake.padding.suffix`** at byte `i`: where the shifted flag and the flag differ, the
packed byte is `0x1F`. -/
theorem suffix_eq {e : program.Env interp} (hs : HashSat e) {i : ℕ} (hi : i < 136) :
    ((if i = 0 then 1 else flag e (i - 1)) + flag e i) *
      ((∑ t : Fin 8, bufBit e (8 * i + t) * gH ^ (t : ℕ)) + constH program 29 i) = 0 := by
  obtain ⟨-, -, -, -, -, -, -, h21, -, -, -, -, -, -, -, h30, -, -, hc⟩ := (absorb_facts (program := program))
  have hh := hs.preds 27 (by norm_num)
  rw [(pred_padding (program := program)).2.2.2.1] at hh
  have hlen := (squeezeIn_facts (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have := holdsAt_equal0 hh i (by
    rw [RealizedProgram.exprLen_mul, RealizedProgram.exprLen_add, RealizedProgram.exprLen_ref (FalconHBase.refsOrdered (program := program)) (by omega),
      (expr_absorb (program := program)).2.2.2.1, RealizedProgram.exprLen_reindex, h21]
    exact hi)
  change program.evalE _ 0 _ i = program.evalE _ 0 (.leaf 30) i at this
  rw [evalE_const0 e (hc 30 (by simp)).1 (hc 30 (by simp)).2, h30 i hi, decodeH_zero,
    RealizedProgram.evalE_mul, RealizedProgram.evalE_add, RealizedProgram.evalE_add, evalE_ref51 e hi, evalE_ref52 e hi,
    evalE_const0 e (hc 29 (by simp)).1 (hc 29 (by simp)).2] at this
  exact this

/-- **`h2p.shake.padding.zeros`** at byte `i`: where the shifted flag is clear, the packed byte is
`0`, or `0x80` at the last byte. -/
theorem zeros_eq {e : program.Env interp} (hs : HashSat e) {i : ℕ} (hi : i < 136) :
    ((if i = 0 then 1 else flag e (i - 1)) + 1) *
      ((∑ t : Fin 8, bufBit e (8 * i + t) * gH ^ (t : ℕ)) + constH program 31 i) = 0 := by
  obtain ⟨-, -, -, -, -, -, h23, h21, -, -, -, -, -, -, -, h30, -, -, hc⟩ := (absorb_facts (program := program))
  have hh := hs.preds 28 (by norm_num)
  rw [(pred_padding (program := program)).2.2.2.2] at hh
  have hlen := (squeezeIn_facts (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have := holdsAt_equal0 hh i (by
    rw [RealizedProgram.exprLen_mul, RealizedProgram.exprLen_add, RealizedProgram.exprLen_ref (FalconHBase.refsOrdered (program := program)) (by omega),
      (expr_absorb (program := program)).2.2.2.1, RealizedProgram.exprLen_reindex, h21]
    exact hi)
  change program.evalE _ 0 _ i = program.evalE _ 0 (.leaf 30) i at this
  rw [evalE_const0 e (hc 30 (by simp)).1 (hc 30 (by simp)).2, h30 i hi, decodeH_zero,
    RealizedProgram.evalE_mul, RealizedProgram.evalE_add, RealizedProgram.evalE_add, evalE_ref51 e hi, evalE_ref52 e hi,
    RealizedProgram.evalE_reindex, RealizedProgram.evalE_mul, RealizedProgram.evalE_reindex, h23 i hi, evalE_selector,
    one_mul, evalE_const0 e (squeezeIn_facts (program := program)).2.2.2.2.2.2.2.2.1
      (squeezeIn_facts (program := program)).2.2.2.2.2.2.2.2.2.2.1, (squeezeIn_facts (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.1,
    decodeH_one, evalE_const0 e (hc 31 (by simp)).1 (hc 31 (by simp)).2] at this
  exact this

/-- **Bytes packed in the subfield basis are injective** (`g^0, …, g^7` linearly independent over
`GF(2)`, `HField.e_li`): two Boolean bytes with the same packing are equal. -/
theorem bits_eq_of_packed {u v : Fin 8 → (interp 0).K} (hu : ∀ t, u t = 0 ∨ u t = 1)
    (hv : ∀ t, v t = 0 ∨ v t = 1)
    (h : ∑ t : Fin 8, u t * gH ^ (t : ℕ) = ∑ t : Fin 8, v t * gH ^ (t : ℕ)) : u = v := by
  let : Algebra (ZMod 2) (interp 0).K := ZMod.algebra _ 2
  have hli : LinearIndependent (ZMod 2) fun t : Fin 8 => (HField.sel (FH := FH)).e
      (Fin.castLE (by norm_num) t) :=
    (HField.e_li (FH := FH)).comp _ (Fin.castLE_injective _)
  have hsum : ∀ w : Fin 8 → (interp 0).K, (∀ t, w t = 0 ∨ w t = 1) →
      ∑ t : Fin 8, w t * gH ^ (t : ℕ) = ∑ t : Fin 8,
        if decide (w t = 1) then (HField.sel (FH := FH)).e (Fin.castLE (by norm_num) t)
        else 0 := by
    intro w hw
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [HField.e_eq]
    rcases hw t with h0 | h1
    · rw [h0, zero_mul, if_neg (by simp)]
    · rw [h1, one_mul, if_pos (by simp)]
      rfl
  have hb := boolSum_injective hli (((hsum u hu).symm.trans h).trans (hsum v hv))
  funext t
  have ht := congrFun hb t
  rcases hu t with h0 | h1 <;> rcases hv t with h0' | h1'
  · rw [h0, h0']
  · simp [h0, h1'] at ht
  · simp [h1, h0'] at ht
  · rw [h1, h1']


/-- **The source program gives what the hash's lemmas read** (`HashSat`). -/
theorem _root_.GordieHowe.RealizedProgram.SourceSatAt.hashSat {e : program.Env interp}
    (hs : program.SourceSatAt e) : HashSat e where
  preds q hq := hs.preds _ (RealizedProgram.predicate_mem ((shake_source (program := program)) q hq).1) ((shake_source (program := program)) q hq).2
  bits v hv i hi := by
    rcases hv with rfl | rfl | rfl
    · exact bool_of_bitTyped hs (buf_facts (program := program)).1 hi
    · exact bool_of_bitTyped hs (buf_facts (program := program)).2 hi
    · exact bool_of_bitTyped hs (flag_facts (program := program)).1 hi

/-- **The buffer's bits are bits** where the source program holds. -/
theorem bufBit_bool {e : program.Env interp} (hs : HashSat e) {j : ℕ} (hj : j < 1088) :
    bufBit e j = 0 ∨ bufBit e j = 1 := by
  unfold bufBit
  split_ifs with h
  · exact hs.bits 45 (by simp) _ (by rw [(absorb_facts (program := program)).2.2.2.2.2.2.2.2.2.1]; exact h)
  · exact hs.bits 46 (by simp) _ (by rw [(absorb_facts (program := program)).2.2.2.2.2.2.2.2.2.2.1]; omega)

/-- **The padding byte at buffer byte `i ≥ 40 + L`**: the suffix `0x1F` at `40 + L`, `0x80` at the
last byte, `0` between. -/
def padConst (len i : ℕ) : ℕ := if i = len then 0x1F else if i = 135 then 0x80 else 0

theorem constBit_bool (c t : ℕ) : Bits.constBit (K := (interp 0).K) c t = 0 ∨
    Bits.constBit (K := (interp 0).K) c t = 1 := by
  unfold Bits.constBit
  split_ifs
  · exact .inr rfl
  · exact .inl rfl

/-- In characteristic two, `a + b = 0` is `a = b`. -/
theorem eq_of_add_eq_zero {a b : (interp 0).K} (h : a + b = 0) : a = b :=
  (eq_neg_of_add_eq_zero_left h).trans (CharTwo.neg_eq b)

/-- **The buffer past the message is the padding** (`padding.suffix`, `padding.zeros`): byte
`i ≥ 40 + L` of the buffer has the bits of `padConst`. -/
theorem bufBit_pad {e : program.Env interp} (hs : HashSat e) {i : ℕ} (hi : i < 136)
    (hle : 40 + lenOf (program.reader e) ≤ i) (t : Fin 8) :
    bufBit e (8 * i + t) = Bits.constBit (padConst (40 + lenOf (program.reader e)) i) t := by
  set len := 40 + lenOf (program.reader e) with hlen
  have hL := lenOf_le (program.reader e)
  have hfi : flag e i = 0 := by
    rcases flag_bool hs hi with h | h
    · exact h
    · exact absurd ((flag_iff hs hi).1 h) (by omega)
  have hbits : ∀ c : ℕ, (∑ s : Fin 8, bufBit e (8 * i + s) * gH ^ (s : ℕ)) =
      (∑ s : Fin 8, Bits.constBit (K := (interp 0).K) c s * gH ^ (s : ℕ)) →
      bufBit e (8 * i + t) = Bits.constBit c t := fun c h =>
    congrFun (bits_eq_of_packed (fun s => bufBit_bool hs (by have := s.isLt; omega))
      (fun s => constBit_bool c s) h) t
  by_cases heq : i = len
  · have hprev : flag e (i - 1) = 1 := (flag_iff hs (by omega)).2 (by omega)
    have h := suffix_eq hs hi
    rw [if_neg (by omega), hprev, hfi, add_zero, one_mul, const29 (by omega)] at h
    rw [show padConst len i = 0x1F by unfold padConst; rw [if_pos heq]]
    exact hbits _ (eq_of_add_eq_zero h)
  · have hprev : flag e (i - 1) = 0 := by
      rcases flag_bool hs (show i - 1 < 136 by omega) with h | h
      · exact h
      · exact absurd ((flag_iff hs (by omega)).1 h) (by omega)
    have h := zeros_eq hs hi
    rw [if_neg (by omega), hprev, zero_add, one_mul, const31 hi] at h
    rw [show padConst len i = if i = 135 then 0x80 else 0 by unfold padConst; rw [if_neg heq]]
    exact hbits _ (eq_of_add_eq_zero h)

/-- **The hash's input bytes**: the first `40 + L` bytes of the buffer, the nonce's then the
message's (`L = lenOf`), byte `i` the bits `8 i, …, 8 i + 7`. -/
def bufInput (e : program.Env interp) :
    Fin (40 + lenOf (program.reader e)) → BitWires (interp 0).K 8 :=
  fun i b => bufBit e (8 * i + b)

/-- `0` xor a bit is the bit. -/
theorem bxor_zero_left {K : Type*} [Field K] (b : K) : Bits.bxor 0 b = b := by
  unfold Bits.bxor
  ring

/-- **The absorbed block is the padded input** (`Shake256.xorinBlock` of the padded bytes into the
zero state): the buffer's first `40 + L` bytes are the input, the padding predicates make the rest
FIPS 202's `pad10*1` with SHAKE256's suffix (`bufBit_pad`), and the capacity is zero. -/
theorem absorbed_eq {e : program.Env interp} (hs : HashSat e) :
    permStates e 0 0 = Shake256.xorinBlock Shake256.SpongeSpec.shake256 (fun _ _ _ => 0)
      (Shake256.paddedByte Shake256.SpongeSpec.shake256 (bufInput e) 0) := by
  have hsrc : roundSrc 0 0 = .ref 2 := by decide
  have hL := lenOf_le (program.reader e)
  funext x y z
  have hk := RealizedProgram.keccakIdx_lt x y z
  unfold permStates
  rw [hsrc]
  simp only [RealizedProgram.stateOf, RealizedProgram.StateSrc.expr]
  rw [evalE_ref2 e hk]
  unfold Shake256.xorinBlock
  dsimp only
  have hkL : RealizedProgram.keccakIdx x y z = 8 * (8 * ((x : ℕ) + 5 * y) + (z : ℕ) / 8) + (z : ℕ) % 8 := by
    unfold RealizedProgram.keccakIdx
    omega
  have hrate : Shake256.SpongeSpec.shake256.rate = 136 := rfl
  have hsuf : Shake256.SpongeSpec.shake256.suffix = 31 := rfl
  have habs : Shake256.absorbBlocks Shake256.SpongeSpec.shake256
      (40 + lenOf (program.reader e)) = 1 := by
    unfold Shake256.absorbBlocks
    rw [hrate]
    omega
  simp only [hrate]
  split_ifs with h1 h2 h2
  · rw [bxor_zero_left (K := (interp 0).K)]
    set i := 8 * ((x : ℕ) + 5 * y) + (z : ℕ) / 8 with hi
    have hi136 : i < 136 := by omega
    unfold Shake256.paddedByte
    simp only [habs, hrate, hsuf, Nat.mul_zero, Nat.zero_add, Nat.sub_self, and_true]
    rw [hkL]
    by_cases hlt : i < 40 + lenOf (program.reader e)
    · rw [if_neg (by omega), dif_pos hlt]
      simp only [bufInput, hi]
    · have hpad := bufBit_pad hs hi136 (by omega) ⟨(z : ℕ) % 8, Nat.mod_lt _ (by norm_num)⟩
      rw [hpad]
      unfold padConst
      by_cases heq : i = 40 + lenOf (program.reader e)
      · rw [if_pos heq, if_neg (by omega), dif_neg hlt, if_pos heq]
        rfl
      · rw [if_neg heq]
        by_cases h135 : i = 135
        · rw [if_pos h135, if_pos h135, dif_neg hlt, if_neg heq]
          change _ = Bits.bxor (Bits.constBit 0 _) (Bits.constBit 128 _)
          rw [show Bits.constBit (K := (interp 0).K) 0 ((z : ℕ) % 8) = 0 by
            simp [Bits.constBit], bxor_zero_left]
        · rw [if_neg h135, if_neg h135, dif_neg hlt, if_neg heq]
          rfl
  · exfalso
    unfold RealizedProgram.keccakIdx at h1
    omega
  · exfalso
    unfold RealizedProgram.keccakIdx at h1
    omega
  · rfl

/-! ## The squeezed stream -/

/-- **The byte order of a sample**: Falcon reads sample `i` from bytes `2 i`, `2 i + 1` big-endian,
so bit `b < 8` of the sample is bit `b` of the second byte (`8 + b` of the pair), bit `b ≥ 8` bit
`b − 8` of the first. -/
def swapBit (b : ℕ) : ℕ := if b < 8 then b + 8 else b - 8

/-- **The pattern of a sample's two bytes** in the stream's index maps. -/
def swapPat : List RealizedProgram.RepRun := [⟨(8, 1, 8), (16, 0, 0)⟩, ⟨(0, 1, 8), (16, 0, 0)⟩]

theorem expand_swap_succ (n : ℕ) : (RealizedProgram.IdxSeg.rep swapPat (n + 1)).expand =
    (RealizedProgram.IdxSeg.rep swapPat n).expand ++ [(8 + 16 * n, 1, 8), (16 * n, 1, 8)] := by
  simp only [RealizedProgram.IdxSeg.expand, List.range_succ, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, swapPat, List.map_cons, List.map_nil, RealizedProgram.IdxSeg.shift]
  congr 2 <;> simp <;> omega

theorem size_expand_swap : ∀ n : ℕ, RealizedProgram.IndexMap.size (RealizedProgram.IdxSeg.rep swapPat n).expand = 16 * n
  | 0 => rfl
  | n + 1 => by
    rw [expand_swap_succ, RealizedProgram.IndexMap.size_append, size_expand_swap n]
    simp [RealizedProgram.IndexMap.size]
    ring

/-- **Entry `16 r + b` of the repeated sample pattern** is position `16 r + swapBit b`. -/
theorem entry_expand_swap : ∀ {n r b : ℕ}, r < n → b < 16 →
    RealizedProgram.IndexMap.entry (RealizedProgram.IdxSeg.rep swapPat n).expand (16 * r + b) = 16 * r + swapBit b
  | 0, _, _, h, _ => absurd h (by omega)
  | n + 1, r, b, hr, hb => by
    rw [expand_swap_succ, RealizedProgram.IndexMap.entry_append, size_expand_swap]
    by_cases hrn : r < n
    · rw [if_pos (by omega)]
      exact entry_expand_swap hrn hb
    · obtain rfl : r = n := by omega
      rw [if_neg (by omega), show 16 * r + b - 16 * r = b by omega]
      unfold swapBit
      by_cases hb8 : b < 8
      · rw [RealizedProgram.IndexMap.entry, if_pos hb8, if_pos hb8]
        omega
      · rw [RealizedProgram.IndexMap.entry, if_neg hb8, RealizedProgram.IndexMap.entry, if_pos (by omega), if_neg hb8]
        omega

/-- **Entry `s` of view `k`'s map of the stream**: sample `s / 16`'s bit `s mod 16` when the sample
is in block `k`, the zero slot otherwise. -/
def streamIdx (k s : ℕ) : ℕ :=
  if s / 16 / 68 = k then 16 * (s / 16 % 68) + swapBit (s % 16) else zslot k

/-- Entry of the sample pattern at a stream position inside its window. -/
theorem entry_swap_window {n s : ℕ} (hs : s < 16 * n) :
    RealizedProgram.IndexMap.entry (RealizedProgram.IdxSeg.rep swapPat n).expand s = 16 * (s / 16) + swapBit (s % 16) := by
  have h := entry_expand_swap (n := n) (r := s / 16) (b := s % 16) (by omega)
    (Nat.mod_lt _ (by norm_num))
  rwa [show 16 * (s / 16) + s % 16 = s by omega] at h

/-- **A view's map of the stream with zero runs on both sides**: the sample pattern in the window
`[a, a + 1088)`, the zero slot `Z` elsewhere. -/
theorem entry_mid {zs a c s : ℕ} (hs : s < a + 1088 + c) :
    RealizedProgram.IndexMap.entry (RealizedProgram.IndexMap.ofSegs [.run (zs, 0, a), .rep swapPat 68, .run (zs, 0, c)]) s =
      if a ≤ s ∧ s < a + 1088 then 16 * ((s - a) / 16) + swapBit ((s - a) % 16) else zs := by
  simp only [RealizedProgram.IndexMap.ofSegs_cons, RealizedProgram.IndexMap.ofSegs_nil, List.append_nil]
  rw [show (RealizedProgram.IdxSeg.run (zs, 0, a)).expand = [(zs, 0, a)] from rfl,
    show (RealizedProgram.IdxSeg.run (zs, 0, c)).expand = [(zs, 0, c)] from rfl]
  rw [RealizedProgram.IndexMap.entry_append, RealizedProgram.IndexMap.size_single, RealizedProgram.IndexMap.entry_append, size_expand_swap]
  by_cases h1 : s < a
  · rw [if_pos h1, RealizedProgram.IndexMap.entry_step_zero h1, if_neg (by omega)]
  · rw [if_neg h1]
    by_cases h2 : s - a < 16 * 68
    · rw [if_pos h2, entry_swap_window h2, if_pos (by omega)]
    · rw [if_neg h2, RealizedProgram.IndexMap.entry_step_zero (by omega), if_neg (by omega)]

theorem entry_stream_mid {k s : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ 8) (hs : s < 10224) :
    RealizedProgram.IndexMap.entry (RealizedProgram.IndexMap.ofSegs [.run (1088, 0, 1088 * k), .rep swapPat 68,
      .run (1088, 0, 10224 - 1088 * (k + 1))]) s = streamIdx k s := by
  rw [entry_mid (by omega), streamIdx]
  by_cases hw : 1088 * k ≤ s ∧ s < 1088 * k + 1088
  · rw [if_pos hw, if_pos (by omega), show (s - 1088 * k) / 16 = s / 16 % 68 by omega,
      show (s - 1088 * k) % 16 = s % 16 by omega]
  · rw [if_neg hw, if_neg (by omega), zslot, if_neg (by omega), if_neg (by omega)]

theorem entry_stream_first {s : ℕ} (hs : s < 10224) :
    RealizedProgram.IndexMap.entry (RealizedProgram.IndexMap.ofSegs [.rep swapPat 68, .run (1600, 0, 9136)]) s = streamIdx 0 s := by
  simp only [RealizedProgram.IndexMap.ofSegs_cons, RealizedProgram.IndexMap.ofSegs_nil, List.append_nil]
  rw [show (RealizedProgram.IdxSeg.run (1600, 0, 9136)).expand = [(1600, 0, 9136)] from rfl,
    RealizedProgram.IndexMap.entry_append, size_expand_swap, streamIdx]
  by_cases hw : s < 16 * 68
  · rw [if_pos hw, entry_swap_window hw, if_pos (by omega), show s / 16 % 68 = s / 16 by omega]
  · rw [if_neg hw, RealizedProgram.IndexMap.entry_step_zero (by omega), if_neg (by omega)]
    rfl

theorem entry_stream_last {s : ℕ} (hs : s < 10224) :
    RealizedProgram.IndexMap.entry (RealizedProgram.IndexMap.ofSegs [.run (432, 0, 9792), .rep swapPat 27]) s = streamIdx 9 s := by
  simp only [RealizedProgram.IndexMap.ofSegs_cons, RealizedProgram.IndexMap.ofSegs_nil, List.append_nil]
  rw [show (RealizedProgram.IdxSeg.run (432, 0, 9792)).expand = [(432, 0, 9792)] from rfl,
    RealizedProgram.IndexMap.entry_append, RealizedProgram.IndexMap.size_single, streamIdx]
  by_cases hw : s < 9792
  · rw [if_pos hw, RealizedProgram.IndexMap.entry_step_zero hw, if_neg (by omega)]
    rfl
  · rw [if_neg hw, entry_swap_window (by omega), if_pos (by omega),
      show (s - 9792) / 16 = s / 16 % 68 by omega, show (s - 9792) % 16 = s % 16 by omega]

/-- The stream's index maps, as segments. -/
theorem idx_stream : idx30 = RealizedProgram.IndexMap.ofSegs [.rep swapPat 68, .run (1600, 0, 9136)] ∧
    idx31 = RealizedProgram.IndexMap.ofSegs [.run (1088, 0, 1088 * 1), .rep swapPat 68,
      .run (1088, 0, 10224 - 1088 * (1 + 1))] ∧
    idx32 = RealizedProgram.IndexMap.ofSegs [.run (1088, 0, 1088 * 2), .rep swapPat 68,
      .run (1088, 0, 10224 - 1088 * (2 + 1))] ∧
    idx33 = RealizedProgram.IndexMap.ofSegs [.run (1088, 0, 1088 * 3), .rep swapPat 68,
      .run (1088, 0, 10224 - 1088 * (3 + 1))] ∧
    idx34 = RealizedProgram.IndexMap.ofSegs [.run (1088, 0, 1088 * 4), .rep swapPat 68,
      .run (1088, 0, 10224 - 1088 * (4 + 1))] ∧
    idx35 = RealizedProgram.IndexMap.ofSegs [.run (1088, 0, 1088 * 5), .rep swapPat 68,
      .run (1088, 0, 10224 - 1088 * (5 + 1))] ∧
    idx36 = RealizedProgram.IndexMap.ofSegs [.run (1088, 0, 1088 * 6), .rep swapPat 68,
      .run (1088, 0, 10224 - 1088 * (6 + 1))] ∧
    idx37 = RealizedProgram.IndexMap.ofSegs [.run (1088, 0, 1088 * 7), .rep swapPat 68,
      .run (1088, 0, 10224 - 1088 * (7 + 1))] ∧
    idx38 = RealizedProgram.IndexMap.ofSegs [.run (1088, 0, 1088 * 8), .rep swapPat 68,
      .run (1088, 0, 10224 - 1088 * (8 + 1))] ∧
    idx39 = RealizedProgram.IndexMap.ofSegs [.run (432, 0, 9792), .rep swapPat 27] := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem swapBit_lt {b : ℕ} (hb : b < 16) : swapBit b < 16 := by
  unfold swapBit
  split_ifs <;> omega

/-- **A view's term of the stream**: the view's bit of sample `s / 16` when the sample is in the
view's block, `0` otherwise. -/
theorem evalE_streamTerm (e : program.Env interp) {idx : RealizedProgram.IndexMap} {V k : ℕ}
    (hent : ∀ s < 10224, idx.entry s = streamIdx k s) (hsz : (program.value V).size = zslot k)
    {s : ℕ} (hs : s < 10224) :
    program.evalE (program.reader e) 0 (.reindex idx (.concat (.leaf V) (.leaf 0))) s =
      if s / 16 / 68 = k then
        program.evalE (program.reader e) 0 (.leaf V) (16 * (s / 16 % 68) + swapBit (s % 16))
      else 0 := by
  rw [RealizedProgram.evalE_reindex, hent s hs, streamIdx]
  have hsw := swapBit_lt (b := s % 16) (Nat.mod_lt _ (by norm_num))
  split_ifs with h
  · rw [RealizedProgram.evalE_concat, RealizedProgram.exprLen_leaf, hsz, if_pos]
    unfold zslot
    split_ifs <;> omega
  · exact evalE_concat0 e hsz le_rfl le_rfl



/-- **The stream** (`ref 489`): bit `b` of sample `i` is bit `16 (i mod 68) + swapBit b` of block
`i / 68`'s view. -/
theorem evalE_stream (e : program.Env interp) {i b : ℕ} (hi : i < 639) (hb : b < 16) :
    program.evalE (program.reader e) 0 (.ref 489) (16 * i + b) =
      program.evalE (program.reader e) 0 (.leaf (viewVal (i / 68)))
        (16 * (i % 68) + swapBit b) := by
  obtain ⟨h30, h31, h32, h33, h34, h35, h36, h37, h38, h39⟩ := idx_stream
  obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, hlen⟩ := (view_sizes (program := program))
  have hs : 16 * i + b < 10224 := by omega
  rw [RealizedProgram.evalE_ref (FalconHBase.refsOrdered (program := program)) _ _ hlen, (expr489 (program := program))]
  simp only [RealizedProgram.evalE_add]
  rw [evalE_streamTerm e (k := 0) (fun s hs => by rw [h30]; exact entry_stream_first hs)
      (by rw [s0]; rfl) hs,
    evalE_streamTerm e (k := 1)
      (fun s hs => by rw [h31]; exact entry_stream_mid (by norm_num) (by norm_num) hs)
      (by rw [s1]; rfl) hs,
    evalE_streamTerm e (k := 2)
      (fun s hs => by rw [h32]; exact entry_stream_mid (by norm_num) (by norm_num) hs)
      (by rw [s2]; rfl) hs,
    evalE_streamTerm e (k := 3)
      (fun s hs => by rw [h33]; exact entry_stream_mid (by norm_num) (by norm_num) hs)
      (by rw [s3]; rfl) hs,
    evalE_streamTerm e (k := 4)
      (fun s hs => by rw [h34]; exact entry_stream_mid (by norm_num) (by norm_num) hs)
      (by rw [s4]; rfl) hs,
    evalE_streamTerm e (k := 5)
      (fun s hs => by rw [h35]; exact entry_stream_mid (by norm_num) (by norm_num) hs)
      (by rw [s5]; rfl) hs,
    evalE_streamTerm e (k := 6)
      (fun s hs => by rw [h36]; exact entry_stream_mid (by norm_num) (by norm_num) hs)
      (by rw [s6]; rfl) hs,
    evalE_streamTerm e (k := 7)
      (fun s hs => by rw [h37]; exact entry_stream_mid (by norm_num) (by norm_num) hs)
      (by rw [s7]; rfl) hs,
    evalE_streamTerm e (k := 8)
      (fun s hs => by rw [h38]; exact entry_stream_mid (by norm_num) (by norm_num) hs)
      (by rw [s8]; rfl) hs,
    evalE_streamTerm e (k := 9) (fun s hs => by rw [h39]; exact entry_stream_last hs)
      (by rw [s9]; rfl) hs]
  have hdiv : (16 * i + b) / 16 = i := by omega
  have hmod : (16 * i + b) % 16 = b := by omega
  rw [hdiv, hmod]
  have hk : i / 68 < 10 := by omega
  generalize hq : i / 68 = q at hk ⊢
  interval_cases q <;> simp [viewVal, outVal]

/-- A bit read in an equal field identifier is the bit there. -/
theorem castElt_ofBool {a b : ℕ} (h : a = b) (c : Bool) :
    (RealizedProgram.castElt ((interp a).ofBool c) : (interp b).K) = (interp b).ofBool c := by
  subst h
  exact RealizedProgram.castElt_self _



/-- **A view reads the permutation's output**: bit `j` of view `k` is bit `j` of permutation
`k`'s output state (`h2p.shake.state` is the absorb permutation's, `evalE_state`). -/
theorem evalE_view {e : program.Env interp} (hs : HashSat e) {k : ℕ} (hk : k < 10)
    {j : ℕ} (hj : j < zslot k) :
    program.evalE (program.reader e) 0 (.leaf (viewVal k)) j =
      program.evalE (program.reader e) 0 (.leaf (outVal k 23)) j := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · exact evalE_state hs (by simpa [zslot] using hj)
  · obtain ⟨k', rfl⟩ : ∃ k' : ℕ, k = k' + 1 := ⟨k - 1, by omega⟩
    have hk' : k' < 9 := by omega
    obtain ⟨hV, hS, hW⟩ := (view_kinds (program := program)) ⟨k', hk'⟩
    obtain ⟨h0, h1, h2, e0, e1, e2, hf⟩ := (view_sel (program := program))
    obtain ⟨hfV, hfS, hszS, hszV⟩ := hf ⟨k', hk'⟩
    simp only at hV hS hW hfV hfS hszS hszV
    have hz : zslot (k' + 1) ≤ 1088 := by
      unfold zslot
      rw [if_neg (by omega)]
      split_ifs
      · norm_num
      · norm_num
    rw [RealizedProgram.evalE_leaf, RealizedProgram.evalE_leaf, RealizedProgram.reader_of_bits_of_priv e hV hW,
      RealizedProgram.reader_of_bits_of_priv e hS hW, castElt_ofBool hfV, castElt_ofBool hfS, hszS, h0,
      show 1600 / 100 = 16 from rfl, hszV, e0 _ (by omega)]
    by_cases h9 : k' + 1 = 9
    · rw [if_pos h9, h2, show zslot (k' + 1) = 432 by unfold zslot; simp [h9]] at *
      rw [show 432 / 27 = 16 from rfl, e2 _ (by omega)]
    · rw [if_neg h9, h1, show zslot (k' + 1) = 1088 by unfold zslot; simp [h9]] at *
      rw [show 1088 / 68 = 16 from rfl, e1 _ (by omega)]

/-! ## The sponge view -/

/-- **The output state of permutation `j`** (`0` past the tenth). -/
def finOf (e : program.Env interp) (j : ℕ) : State (interp 0).K :=
  if h : j < 10 then permStates e ⟨j, h⟩ (Fin.last 24) else fun _ _ _ => 0

/-- **SHAKE256 of `40 + L ≤ 72` bytes, squeezing `1278`, runs ten permutations**: one absorb, nine
squeezes. -/
theorem numBlocks_eq {L : ℕ} (hL : L ≤ 32) :
    Shake256.numBlocks Shake256.SpongeSpec.shake256 (40 + L) (2 * falcon512.S) = 10 := by
  have hsq : Shake256.squeezeBlocks Shake256.SpongeSpec.shake256 (2 * falcon512.S) = 9 := by
    decide
  unfold Shake256.numBlocks Shake256.absorbBlocks
  rw [hsq]
  change (40 + L) / 136 + 1 + 9 = 10
  omega

/-- **The input of permutation `j` is the sponge's**: the padded block xored into the zero state
for the absorb permutation (`absorbed_eq`), the previous permutation's output for a squeeze. -/
theorem inputOf_eq {e : program.Env interp} (hs : HashSat e) {n j : ℕ}
    (hn : n = 10) (hj : j < 10) :
    Shake256.inputOf Shake256.SpongeSpec.shake256 (bufInput e) (fun k : Fin n => finOf e k) j =
      permStates e ⟨j, hj⟩ 0 := by
  have hL := lenOf_le (program.reader e)
  have habs : Shake256.absorbBlocks Shake256.SpongeSpec.shake256
      (40 + lenOf (program.reader e)) = 1 := by
    unfold Shake256.absorbBlocks
    change (40 + lenOf (program.reader e)) / 136 + 1 = 1
    omega
  unfold Shake256.inputOf
  rw [habs]
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · rw [if_pos (by norm_num)]
    change _ = permStates e 0 0
    rw [absorbed_eq hs]
    congr 1
  · rw [if_neg (by omega)]
    unfold Shake256.priorOf
    rw [dif_pos ⟨hj0, by omega⟩]
    change finOf e (j - 1) = _
    unfold finOf
    rw [dif_pos (by omega)]
    rcases Nat.lt_or_ge j 2 with h2 | h2
    · obtain rfl : j = 1 := by omega
      exact (permStates_one_zero hs).symm
    · exact (permStates_succ_zero e (p := ⟨j, hj⟩) h2).symm

theorem bufInput_bool {e : program.Env interp} (hs : HashSat e)
    (i : Fin (40 + lenOf (program.reader e))) : Bits.AllBool (bufInput e i) := fun b => by
  have hL := lenOf_le (program.reader e)
  exact bufBit_bool hs (by have := i.isLt; have := b.isLt; omega)

/-- **The hash's soundness**: every squeezed byte is SHAKE256 of the input bytes
(`Shake256.squeezeOut_sound` at the permutations' round relations, `permRelation`, and their
inputs, `inputOf_eq`). -/
theorem squeeze_sound {e : program.Env interp} (hs : HashSat e)
    (o : Fin (2 * falcon512.S)) :
    natOfBits (Shake256.squeezeOut (sp := Shake256.SpongeSpec.shake256)
        (len := 40 + lenOf (program.reader e)) (fun j => finOf e j) o) =
      xofFin Shake256.SpongeSpec.shake256.xof (Shake256.inputBytes (bufInput e))
        (2 * falcon512.S) o := by
  have hn := numBlocks_eq (lenOf_le (program.reader e))
  refine Shake256.squeezeOut_sound (bufInput_bool hs) (fun j h => ?_) o
  have hj : (j : ℕ) < 10 := by have := j.isLt; omega
  rw [inputOf_eq hs hn hj] at h
  change Shake256.Encodes (finOf e j) _
  unfold finOf
  rw [dif_pos hj]
  exact (permRelation hs ⟨j, hj⟩).encodes h

/-- **The SHAKE256 call of a native Falcon program** (`SpongeView`): the input the buffer's first
`40 + L` bytes (`bufInput`), the output read off the ten permutations' output states
(`Shake256.squeezeOut`), sound by `squeeze_sound`. -/
def falconSponge : RealizedProgram.SpongeView program interp 0 (2 * falcon512.S) where
  len e := 40 + lenOf (program.reader e)
  input := bufInput
  out e := Shake256.squeezeOut (sp := Shake256.SpongeSpec.shake256)
    (len := 40 + lenOf (program.reader e)) fun j => finOf e j
  sound _ hs o := squeeze_sound hs.hashSat o

/-- **A squeezed byte's bit** is bit `8 (o mod 136) + j` of permutation `o / 136`'s output
state. -/
theorem squeezeOut_bit (e : program.Env interp) {o j : ℕ} (ho : o < 2 * falcon512.S) (hj : j < 8) :
    Shake256.squeezeOut (sp := Shake256.SpongeSpec.shake256) (len := 40 + lenOf (program.reader e))
        (fun k => finOf e k) ⟨o, ho⟩ ⟨j, hj⟩ =
      program.evalE (program.reader e) 0 (.leaf (outVal (o / 136) 23)) (8 * (o % 136) + j) := by
  have hL := lenOf_le (program.reader e)
  have habs : Shake256.absorbBlocks Shake256.SpongeSpec.shake256
      (40 + lenOf (program.reader e)) = 1 := by
    unfold Shake256.absorbBlocks
    change (40 + lenOf (program.reader e)) / 136 + 1 = 1
    omega
  have hn := numBlocks_eq hL
  have ho' : o < 1278 := ho
  unfold Shake256.squeezeOut
  simp only [habs, show Shake256.SpongeSpec.shake256.rate = 136 from rfl, Nat.sub_self,
    Nat.zero_add]
  rw [dif_pos (by rw [hn]; omega)]
  change finOf e (o / 136) _ _ _ = _
  unfold finOf
  rw [dif_pos (by omega)]
  have hsrc : roundSrc ⟨o / 136, by omega⟩ (Fin.last 24) = .leaf (outVal (o / 136) 23) := by
    unfold roundSrc
    simp
  unfold permStates
  rw [hsrc]
  simp only [RealizedProgram.stateOf, RealizedProgram.StateSrc.expr]
  congr 1
  unfold RealizedProgram.keccakIdx
  simp only
  omega

/-- **An expression read at a field identifier equal to `0`**, cast to field `0`, is its reading
at `0`. -/
theorem castElt_evalE_of_eq {rd : program.Valuation interp} {f : ℕ} (hf : f = 0) (x : RealizedProgram.Expr)
    (i : ℕ) : (RealizedProgram.castElt (program.evalE rd f x i) : (interp 0).K) = program.evalE rd 0 x i := by
  subst hf
  exact RealizedProgram.castElt_self _

/-- **The selection's samples are the squeezed bytes, two per sample** (`evalE_stream`,
`evalE_view`, `squeezeOut_bit`). -/
theorem selSample_eq {e : program.Env interp} (hs : HashSat e) (i : Fin falcon512.S) :
    selSample0 e i = HashCircuit.sampleAt (falconSponge.out e) i := by
  funext b
  have hi : (i : ℕ) < 639 := i.isLt
  have hb : (b : ℕ) < 16 := b.isLt
  change RealizedProgram.castElt (program.evalE (program.reader e) (program.domainField 0) (.ref 489)
    (i * 16 + b)) = _
  rw [castElt_evalE_of_eq FalconHBase.domainField0]
  rw [show (i : ℕ) * 16 + b = 16 * i + b by ring, evalE_stream e hi hb,
    evalE_view hs (by omega) (by
      unfold zslot
      have := swapBit_lt hb
      split_ifs <;> omega)]
  unfold HashCircuit.sampleAt
  split_ifs with h8
  · change _ = Shake256.squeezeOut (sp := Shake256.SpongeSpec.shake256)
      (len := 40 + lenOf (program.reader e)) (fun k => finOf e k) ⟨2 * i + 1, _⟩ ⟨b, h8⟩
    rw [squeezeOut_bit e _ h8, show (2 * (i : ℕ) + 1) / 136 = i / 68 by omega]
    congr 1
    unfold swapBit
    rw [if_pos h8]
    omega
  · change _ = Shake256.squeezeOut (sp := Shake256.SpongeSpec.shake256)
      (len := 40 + lenOf (program.reader e)) (fun k => finOf e k) ⟨2 * i, _⟩ ⟨b - 8, _⟩
    rw [squeezeOut_bit e _ (by omega), show 2 * (i : ℕ) / 136 = i / 68 by omega]
    congr 1
    unfold swapBit
    rw [if_neg h8]
    omega

/-- **The input bytes are the nonce's then the message's** at the flags' length (`messageBytes`):
the buffer's first `40` bytes are the nonce, the next `L` the message. -/
theorem inputBytes_eq (e : program.Env interp) :
    Shake256.inputBytes (bufInput e) =
      Emulated.bytesOf (nonceBits (program.reader e)) ++ messageBytes (program.reader e) := by
  unfold Shake256.inputBytes messageBytes Emulated.bytesOf
  rw [List.ofFn_add]
  refine congrArg₂ (· ++ ·) ?_ ?_
  · refine List.ofFn_inj.2 (funext fun i => ?_)
    refine congrArg Bits.natOfBits (funext fun b => ?_)
    have hi : (i : ℕ) < 40 := i.isLt
    have hb := b.isLt
    simp only [bufInput, bufBit, HashCircuit.byteWires, nonceBits, Fin.val_castLE]
    rw [if_pos (by omega)]
  · refine List.ofFn_inj.2 (funext fun i => ?_)
    refine congrArg Bits.natOfBits (funext fun b => ?_)
    have hb := b.isLt
    simp only [bufInput, bufBit, HashCircuit.byteWires, messageBits, Fin.val_natAdd]
    rw [if_neg (by omega), show 8 * (40 + (i : ℕ)) + b - 320 = 8 * i + b by omega]

/-- **The hash view of a native Falcon program** (`FalconHashView`): the SHAKE256 call
`falconSponge`, whose input bytes are the nonce's and the message's at the flags' length, and whose
output, two bytes per sample, is the selection's stream. -/
def falconHashView : FalconHashView (program := program) (FH := FH) (FA := FA) where
  sponge := falconSponge
  input_bytes e _ := inputBytes_eq e
  samples e hs i :=
    (natOfBits_selSample0 e i).symm.trans (congrArg Bits.natOfBits (selSample_eq hs.hashSat i))

end GordieHowe.Falcon512.Native.ROMParams
