-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Native.ROMParams.Frontend.HashData
public import GordieHowe.Applications.MLDSA44.Native.ROMParams.Frontend.Select

@[expose] public section

/-!
# GordieHowe frontend: `MLDSA44.Native.ROMParams`, the three SHAKE256 calls

The instance of the frontend's hash view (`GordieHowe.MLDSA44.Native.ROMParams.HashView`) for the native
ML-DSA-44 proof of possession at the ROM parameters (`hashView`), over the ten Keccak-f permutations of domain `H`
(`GordieHowe/Applications/MLDSA44/Native/ROMParams/Frontend/HashData.lean`):

* **the rounds** (`permRelation`): permutation `p`'s round `t` is the round relation
  (`GordieHowe.RealizedProgram.roundRelation_of_shapes` at the decided shapes `roundShapes`) between its states;
* **`μ`** (`muSponge`): one absorb of the buffer `tr ‖ 0x00 ‖ 0x00 ‖ M`, the message at the length
  its in-message flags encode (`flag_iff`: `h2c.mu.padding.monotone`, `min`, `max`), the bytes
  past it FIPS 202's `pad10*1` with SHAKE256's suffix (`h2c.mu.padding.suffix`, `zeros`, through
  the bytes' packing in the subfield basis, `SelectionField.embedBits_eq`), the output `h2c.mu.out`
  by `h2c.mu.padding.output`;
* **`c̃'`** (`cTildeSponge`): seven absorbs of `μ ‖ w1` and its constant padding, the output the
  bit view `h2c.c_tilde.out` of the last permutation's words;
* **the SampleInBall stream** (`sibSponge`): one absorb of `c̃'` and its constant padding and one
  squeeze, the output the bit views `h2c.sib.out.p0`, `p1`.

Each call's soundness is `Shake256.squeezeOut_sound`. `μ`'s needs the statement's `tr` to be bits:
the program does not range-check that public value, so `muSponge` reads the permutations only
where `tr` is bits (`HashView.mu_out`'s premise).
-/

namespace GordieHowe.MLDSA44.Native.ROMParams

open Generated.MLDSA44.Native.ROMParams.Program
open GordieHowe.Bits GordieHowe.Keccak GordieHowe.KeccakTrace

/-- **The index map of `c̃'`'s absorbed block `p − 1`** (`p = 2, …, 7`). -/
def blkIdx (p : ℕ) : RealizedProgram.IndexMap := [idx41, idx42, idx43, idx44, idx45, idx46].getD (p - 2) []

/-- **The program facts of domain `H`'s three SHAKE256 calls** (`MldsaHHashData`, `MldsaHSelect` and): the views' kinds and sizes, the absorbs' shared expressions (with the index maps of the program at the ROM parameters), and `μ`'s padding's predicates and constants. Each program instantiates it by `decide`. -/
class MldsaHHash (program : RealizedProgram) : Prop extends MldsaHHashData program, MldsaHSelect program where
  /-- The kinds of the output views and of the permutation outputs they share words with (generated
  data). -/
  view_kinds : (program.value 458).kind = .bits 456 idx3 ∧ (program.value 457).kind = .bits 456 idx1 ∧ (program.value 456).kind = .priv ∧ (program.value 555).kind = .bits 505 idx4 ∧ (program.value 506).kind = .bits 505 idx1 ∧ (program.value 505).kind = .priv ∧ (program.value 556).kind = .bits 553 idx4 ∧ (program.value 554).kind = .bits 553 idx1 ∧ (program.value 553).kind = .priv
  /-- Facts of the views' sizes and fields, decided. -/
  view_facts : (program.value 458).size = 256 ∧ (program.value 457).size = 1600 ∧ (program.value 555).size = 1088 ∧ (program.value 506).size = 1600 ∧ (program.value 556).size = 1088 ∧ (program.value 554).size = 1600 ∧ RealizedProgram.IndexMap.size idx3 = 16 ∧ RealizedProgram.IndexMap.size idx1 = 100 ∧ RealizedProgram.IndexMap.size idx4 = 68 ∧ (∀ v ∈ [458, 457, 555, 506, 556, 554], program.valueField v = 1)
  /-- The shared expressions of the permutations' inputs (generated data). -/
  hash_exprs : program.expr 11 = .reindex idx16 (.concat (.reindex idx14 (.concat (.reindex idx13 (.leaf 67)) (.leaf 9))) (.reindex idx15 (.leaf 68))) ∧ program.expr 12 = .reindex idx17 (.reindex idx17 (.concat (.reindex idx16 (.reindex idx16 (.ref 11))) (.leaf 10))) ∧ program.expr 66 = .reindex idx40 (.concat (.reindex idx39 (.reindex idx39 (.concat (.reindex idx13 (.leaf 121)) (.reindex idx38 (.leaf 71))))) (.leaf 41)) ∧ program.expr 67 = .reindex idx17 (.reindex idx17 (.concat (.reindex idx16 (.ref 66)) (.leaf 10))) ∧ program.expr 410 = .reindex idx17 (.reindex idx17 (.concat (.reindex idx16 (.reindex idx16 (.concat (.reindex idx47 (.reindex idx47 (.leaf 458))) (.leaf 42)))) (.leaf 10))) ∧ program.expr 459 = .reindex idx17 (.reindex idx17 (.leaf 506))
  /-- The inputs of `c̃'`'s later absorbs: the previous output plus the absorbed block
  (generated data). -/
  expr_blk : ∀ p : Fin 10, 2 ≤ (p : ℕ) → (p : ℕ) ≤ 7 → program.expr (linRef p 0 - 2) = .reindex idx17 (.add (.reindex idx17 (.leaf (outVal (p - 1) 23))) (.reindex idx17 (.concat (.reindex (blkIdx p) (.ref 66)) (.leaf 10)))) ∧ blkIdx p = ([(1088 * ((p : ℕ) - 1), 1, 1088)] : RealizedProgram.IndexMap)
  /-- Facts of the inputs' sizes and constants, decided. -/
  hash_sizes : program.exprs.length = 526 ∧ RealizedProgram.IndexMap.size idx13 = 512 ∧ RealizedProgram.IndexMap.size idx14 = 528 ∧ RealizedProgram.IndexMap.size idx15 = 560 ∧ RealizedProgram.IndexMap.size idx16 = 1088 ∧ RealizedProgram.IndexMap.size idx17 = 1600 ∧ RealizedProgram.IndexMap.size idx38 = 6144 ∧ RealizedProgram.IndexMap.size idx39 = 6656 ∧ RealizedProgram.IndexMap.size idx40 = 7616 ∧ RealizedProgram.IndexMap.size idx47 = 256 ∧ (program.value 9).size = 16 ∧ (program.value 10).size = 512 ∧ (program.value 41).size = 960 ∧ (program.value 42).size = 832 ∧ program.constEntries 9 = List.replicate 16 0 ∧ program.constEntries 10 = List.replicate 512 0 ∧ program.constEntries 41 = List.ofFn (fun r : Fin 960 => if (r : ℕ) < 5 ∨ (r : ℕ) = 959 then 1 else 0) ∧ program.constEntries 42 = List.ofFn (fun r : Fin 832 => if (r : ℕ) < 5 ∨ (r : ℕ) = 831 then 1 else 0) ∧ (∀ v ∈ [9, 10, 41, 42], program.isConstant v = true ∧ program.valueField v = 1)
  /-- `μ`'s padding predicates and shared expressions (generated data). -/
  pad_exprs : program.predicate 42 = «p.h2c.mu.padding.monotone» ∧ program.predicate 43 = «p.h2c.mu.padding.max» ∧ program.predicate 44 = «p.h2c.mu.padding.min» ∧ program.predicate 45 = «p.h2c.mu.padding.suffix» ∧ program.predicate 46 = «p.h2c.mu.padding.zeros» ∧ program.predicate 47 = «p.h2c.mu.padding.output» ∧ program.expr 61 = .reindex idx31 (.concat (.leaf 7) (.reindex idx27 (.leaf 69))) ∧ program.expr 62 = .apply (.sum 8) (.mul (.reindex idx16 (.reindex idx16 (.ref 11))) (.reindex idx32 (.leaf 37))) ∧ program.expr 63 = .reindex idx34 (.concat (.leaf 7) (.leaf 36)) ∧ program.expr 64 = .add (.reindex idx35 (.ref 63)) (.reindex idx36 (.ref 63)) ∧ program.expr 65 = .reindex idx13 (.leaf 119)
  /-- Facts of the flags and the padding's constants, decided. -/
  pad_facts : (69 < program.values.length ∧ program.IsSourceValue 69 ∧ (program.value 69).typeSource = .node ∧ (program.value 69).type = .bit) ∧ (68 < program.values.length ∧ program.IsSourceValue 68 ∧ (program.value 68).typeSource = .node ∧ (program.value 68).type = .bit) ∧ (program.value 69).size = 136 ∧ (program.value 68).size = 560 ∧ (program.value 7).size = 1 ∧ RealizedProgram.IndexMap.size idx26 = 135 ∧ RealizedProgram.IndexMap.size idx29 = 1 ∧ RealizedProgram.IndexMap.size idx30 = 1 ∧ RealizedProgram.IndexMap.size idx31 = 136 ∧ RealizedProgram.IndexMap.size idx37 = 512 ∧ idx29.entry 0 = 98 ∧ idx30.entry 0 = 65 ∧ idx34.entry 0 = 0 ∧ idx34.entry 1 = 1 ∧ idx35.entry 0 = 0 ∧ idx36.entry 0 = 1 ∧ (program.value 7).size = 1 ∧ program.constEntries 7 = [1] ∧ program.constEntries 36 = [0] ∧ program.constEntries 35 = List.replicate 135 0 ∧ program.constEntries 39 = List.replicate 136 0 ∧ (∀ i < 135, (program.constEntries 38).getD i 0 = RealizedProgram.xorSel 0x1F fun u => (program.constEntries 37).getD u 0) ∧ (∀ i < 135, (program.constEntries 40).getD i 0 = 0) ∧ (program.constEntries 40).getD 135 0 = RealizedProgram.xorSel 0x80 (fun u => (program.constEntries 37).getD u 0) ∧ (∀ v ∈ [7, 35, 36, 38, 39, 40], program.isConstant v = true ∧ program.valueField v = 1) ∧ (∀ q ∈ [42, 43, 44, 45, 46, 47], q < program.predicates.length ∧ program.inSource (program.predicate q) = true)
  /-- The kinds of `μ`'s output, `w1` and `c̃'` (bit views, generated data). -/
  bit_kinds : (program.value 121).kind = .bits 120 idx2 ∧ (program.value 71).kind = .bits 70 idx0
  /-- `kind458`. -/
  kind458 : (program.value 458).kind = .bits 456 idx3

set_option maxRecDepth 4096 in
/-- The native program at the ROM parameters has these facts. -/
instance : MldsaHHash program where
  view_kinds := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  view_facts := by
    decide +kernel
  hash_exprs := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  expr_blk := by
    intro p h2 h7
    fin_cases p <;> first | (exfalso; simp at h2 h7; done) | exact ⟨rfl, rfl⟩
  hash_sizes := by
    decide +kernel
  pad_exprs := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  pad_facts := by
    decide +kernel
  bit_kinds := ⟨rfl, rfl⟩
  kind458 := rfl

set_option linter.unusedSectionVars false

variable {program : RealizedProgram} [MldsaHHash program] {F0 FH : RealizedProgram.FieldInterp} [HField FH]
  [MldsaHConstsSelect program FH]

set_option hygiene false in
local notation "interp" => RealizedProgram.mldsaInterpOf F0 FH

/-! ## Sponge lemmas -/

/-- In characteristic two, `bxor` is addition. -/
theorem bxor_eq_add {K : Type*} [Field K] [CharP K 2] (a b : K) : Bits.bxor a b = a + b := by
  unfold Bits.bxor
  rw [show (2 : K) = 0 from CharTwo.two_eq_zero]
  ring

/-- **Xoring a block into a state read off coordinates** (`Shake256.xorinBlock` at SHAKE256's
rate): the state of the coordinates plus the block's bits on the first `1088`. -/
theorem xorinBlock_stateOf {K : Type*} [Field K] [CharP K 2] (a w : ℕ → K)
    (block : Fin Shake256.SpongeSpec.shake256.rate → BitWires K 8)
    (hb : ∀ (i : Fin Shake256.SpongeSpec.shake256.rate) (b : Fin 8), block i b = w (8 * i + b)) :
    Shake256.xorinBlock Shake256.SpongeSpec.shake256 (RealizedProgram.stateOf a) block =
      RealizedProgram.stateOf (fun j => if j < 1088 then a j + w j else a j) := by
  funext x y z
  unfold Shake256.xorinBlock RealizedProgram.stateOf
  have hr : Shake256.SpongeSpec.shake256.rate = 136 := rfl
  simp only [hr]
  have hk : RealizedProgram.keccakIdx x y z = 64 * ((x : ℕ) + 5 * y) + z := by
    unfold RealizedProgram.keccakIdx
    ring
  split_ifs with h1 h2 h2
  · rw [bxor_eq_add, hb]
    congr 2
    simp only
    rw [hk]
    omega
  · exfalso
    rw [hk] at h2
    have := z.isLt
    omega
  · exfalso
    rw [hk] at h2
    omega
  · rfl

/-- **A squeezed byte's bit read off coordinates**: bit `j` of byte `o` is coordinate
`8 (o mod 136) + j` of block `absorbBlocks − 1 + o / 136`. -/
theorem squeezeOut_stateOf {K : Type*} [Field K] [DecidableEq K] {len outLen : ℕ}
    {fin : ℕ → State K} (g : ℕ → ℕ → K) (hfin : ∀ k, fin k = RealizedProgram.stateOf (g k)) (o : Fin outLen)
    (j : Fin 8)
    (h : Shake256.absorbBlocks Shake256.SpongeSpec.shake256 len - 1 + (o : ℕ) / 136 <
      Shake256.numBlocks Shake256.SpongeSpec.shake256 len outLen) :
    Shake256.squeezeOut (sp := Shake256.SpongeSpec.shake256) (len := len)
        (fun k => fin k) o j =
      g (Shake256.absorbBlocks Shake256.SpongeSpec.shake256 len - 1 + (o : ℕ) / 136)
        (8 * ((o : ℕ) % 136) + j) := by
  unfold Shake256.squeezeOut
  simp only [show Shake256.SpongeSpec.shake256.rate = 136 from rfl]
  rw [dif_pos h, hfin]
  unfold RealizedProgram.stateOf RealizedProgram.keccakIdx
  congr 1
  dsimp only
  have := j.isLt
  have : (o : ℕ) % 136 < 136 := Nat.mod_lt _ (by norm_num)
  omega


/-- **A padded byte's bit** (`Shake256.paddedByte` at SHAKE256): the input's bit, the suffix
`0x1F` right after the input, `0` past it, plus `0x80` in the last absorbed block's last byte. -/
theorem paddedByte_bit {K : Type*} [Field K] [CharP K 2] [DecidableEq K] {len : ℕ}
    (input : Fin len → BitWires K 8) (k : ℕ) (i : Fin Shake256.SpongeSpec.shake256.rate)
    (b : Fin 8) :
    Shake256.paddedByte Shake256.SpongeSpec.shake256 input k i b =
      (if h : 136 * k + (i : ℕ) < len then input ⟨_, h⟩ b
        else if 136 * k + (i : ℕ) = len then constBit 0x1F b else 0) +
      (if (i : ℕ) = 135 ∧ k = Shake256.absorbBlocks Shake256.SpongeSpec.shake256 len - 1 then
        constBit 0x80 b else 0) := by
  unfold Shake256.paddedByte
  simp only [show Shake256.SpongeSpec.shake256.rate = 136 from rfl,
    show Shake256.SpongeSpec.shake256.suffix = 0x1F from rfl, show (136 : ℕ) - 1 = 135 from rfl]
  have h0 : constBit (K := K) 0 b = 0 := by
    simp [constBit]
  split_ifs <;> simp only [bxor_eq_add, Shake256.constByte, add_zero, zero_add, h0]

/-- **The bytes `shake256` returns are bytes.** -/
theorem xofFin_shake256_lt (input : List ℕ) (m : ℕ) (i : Fin m) :
    xofFin GordieHowe.shake256 input m i < 256 := by
  rw [xofFin_shake256_eq_getElem]
  simp only [GordieHowe.shake256, List.getElem_map]
  exact UInt8.toNat_lt _

/-- **A state read off coordinates** depends only on the first `1600`. -/
theorem stateOf_congr {K : Type*} {f g : ℕ → K} (h : ∀ j < 1600, f j = g j) :
    RealizedProgram.stateOf f = RealizedProgram.stateOf g := by
  funext x y z
  exact h _ (RealizedProgram.keccakIdx_lt x y z)

/-! ## The rounds -/

instance charP_domainH : CharP (interp (program.domainField 1)).K 2 := by
  rw [MldsaHCross.domainField1 (program := program)]
  exact HField.charTwo

/-- A `0`/`1` entry decodes to itself in domain `H`'s field. -/
theorem decode_bitH (c : Prop) [Decidable c] : (interp 1).decode (if c then 1 else 0) =
    (if c then 1 else 0 : (interp 1).K) := by
  by_cases hc : c
  · rw [if_pos hc, if_pos hc]
    exact HField.decode_one
  · rw [if_neg hc, if_neg hc]
    exact HField.decode_zero

theorem evalE_ones (e : program.Env interp) {j : ℕ} (hj : j < 1600) :
    program.evalE (program.reader e) 1 (.leaf 11) j = 1 := by
  rw [RealizedProgram.evalE_leaf_of_isConstant e (const_states (program := program)).2.2.1,
    RealizedProgram.constRead_of_valueField (const_states (program := program)).2.2.2.2.1, (const_states (program := program)).1,
    List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos hj, Option.getD_some]
  exact HField.decode_one

theorem evalE_zeros (e : program.Env interp) {j : ℕ} (hj : j < 1600) :
    program.evalE (program.reader e) 1 (.leaf 13) j = 0 := by
  rw [RealizedProgram.evalE_leaf_of_isConstant e (const_states (program := program)).2.2.2.1,
    RealizedProgram.constRead_of_valueField (const_states (program := program)).2.2.2.2.2.1, (const_states (program := program)).2.1,
    List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos hj, Option.getD_some]
  exact HField.decode_zero

theorem evalE_rc (e : program.Env interp) (t : Fin 24) (x y : Fin 5) (z : Fin 64) :
    program.evalE (program.reader e) 1 (.leaf (rcLeaf t)) (RealizedProgram.keccakIdx x y z) =
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
  rw [decode_bitH]
  exact if_congr hiff rfl rfl

/-- **The states of permutation `p`** (`roundSrc`), read in domain `H`'s field. -/
def permStates (e : program.Env interp) (p : Fin 10) (t : Fin 25) :
    State (interp 1).K :=
  RealizedProgram.stateOf (program.evalE (program.reader e) 1 (roundSrc p t).expr)

/-- **Every permutation's round relations hold** where the source program holds
(`RealizedProgram.roundRelation_of_shapes` at `(roundShapes (program := program))`). -/
theorem permRelation {e : program.Env interp} (hs : HSat e) (p : Fin 10) :
    PermRelation (permStates e p) := by
  intro t
  obtain ⟨hb, hlin, hcol⟩ := (roundShapes (program := program)) p t
  obtain ⟨-, -, hL, hC, hsize⟩ := (round_facts (program := program)) p t
  have h := hs.preds _ (roundPred_ge p t) (roundPred_le p t)
  have key : ∀ D, program.domainField 1 = D →
      (∀ j < 1600, program.evalE (program.reader e) D (.leaf 11) j = 1) →
      (∀ j < 1600, program.evalE (program.reader e) D (.leaf 13) j = 0) →
      (∀ x y z, program.evalE (program.reader e) D (.leaf (rcLeaf t)) (RealizedProgram.keccakIdx x y z) =
        iotaVec t (x, y, z)) →
      RoundRelation t (RealizedProgram.stateOf (program.evalE (program.reader e) D (roundSrc p t.castSucc).expr))
        (RealizedProgram.stateOf (program.evalE (program.reader e) D (.leaf (outVal p t)))) := by
    intro D hD hones hzeros hrc
    subst hD
    have h1 := @RealizedProgram.roundRelation_of_shapes program interp MldsaHCross.refsOrdered (program.reader e)
      _ _ _ _ t charP_domainH hb hlin hcol hL hC keccakMaps hsize
    have h2 := h1 hones
    have h3 := h2 hzeros
    have h4 := h3 hrc
    exact h4 h
  have hrel := key 1 MldsaHCross.domainField1 (fun j hj => evalE_ones e hj)
    (fun j hj => evalE_zeros e hj) (evalE_rc e t)
  have hout : roundSrc p t.succ = .leaf (outVal p t) := by
    unfold roundSrc
    rw [if_neg (by simp)]
    simp
  unfold permStates
  rw [hout]
  exact hrel

/-- **The output state of permutation `p`** is its last round's output value. -/
theorem permStates_last (e : program.Env interp) (p : Fin 10) :
    permStates e p (Fin.last 24) =
      RealizedProgram.stateOf (program.evalE (program.reader e) 1 (.leaf (outVal p 23))) := by
  unfold permStates roundSrc
  simp [RealizedProgram.StateSrc.expr]

/-- **The input state of permutation `p`** is the shared expression two before its first linear
part. -/
theorem permStates_zero (e : program.Env interp) (p : Fin 10) :
    permStates e p 0 = RealizedProgram.stateOf (program.evalE (program.reader e) 1 (.ref (linRef p 0 - 2))) := by
  unfold permStates roundSrc
  simp [RealizedProgram.StateSrc.expr]

/-! ## The output views -/

/-- A bit read in an equal field identifier is the bit there. -/
theorem castElt_ofBool {a b : ℕ} (h : a = b) (c : Bool) :
    (RealizedProgram.castElt ((interp a).ofBool c) : (interp b).K) = (interp b).ofBool c := by
  subst h
  exact RealizedProgram.castElt_self _

/-- **An index map of one run of step `1`** reads `a + t` below its count. -/
theorem entry_run_one {m : RealizedProgram.IndexMap} {a n : ℕ} (h : m = [(a, 1, n)]) {t : ℕ} (ht : t < n) :
    m.entry t = a + t := by
  rw [h]
  exact RealizedProgram.IndexMap.entry_step_one ht

/-- **An index map of one run of step `0`** reads `a` below its count. -/
theorem entry_run_zero {m : RealizedProgram.IndexMap} {a n : ℕ} (h : m = [(a, 0, n)]) {t : ℕ} (ht : t < n) :
    m.entry t = a := by
  rw [h]
  exact RealizedProgram.IndexMap.entry_step_zero ht

set_option maxRecDepth 4096 in
/-- The kinds of the output views and of the permutation outputs they share words with (generated
data). -/
theorem view_kinds : (program.value 458).kind = .bits 456 idx3 ∧ (program.value 457).kind = .bits 456 idx1 ∧ (program.value 456).kind = .priv ∧ (program.value 555).kind = .bits 505 idx4 ∧ (program.value 506).kind = .bits 505 idx1 ∧ (program.value 505).kind = .priv ∧ (program.value 556).kind = .bits 553 idx4 ∧ (program.value 554).kind = .bits 553 idx1 ∧ (program.value 553).kind = .priv :=
  MldsaHHash.view_kinds

/-- Facts of the views' sizes and fields, decided. -/
theorem view_facts : (program.value 458).size = 256 ∧ (program.value 457).size = 1600 ∧ (program.value 555).size = 1088 ∧ (program.value 506).size = 1600 ∧ (program.value 556).size = 1088 ∧ (program.value 554).size = 1600 ∧ RealizedProgram.IndexMap.size idx3 = 16 ∧ RealizedProgram.IndexMap.size idx1 = 100 ∧ RealizedProgram.IndexMap.size idx4 = 68 ∧ (∀ v ∈ [458, 457, 555, 506, 556, 554], program.valueField v = 1) :=
  MldsaHHash.view_facts

/-- **Two bit views of the same words** read alike where their selections agree. -/
theorem reader_view_eq (e : program.Env interp) {v v' w : ℕ} {s s' : RealizedProgram.IndexMap}
    (hk : (program.value v).kind = .bits w s) (hk' : (program.value v').kind = .bits w s')
    (hw : (program.value w).kind = .priv) (hf : program.valueField v = 1)
    (hf' : program.valueField v' = 1)
    (hsz : (program.value v).size / s.size = 16) (hsz' : (program.value v').size / s'.size = 16)
    {j : ℕ} (hs : s.entry (j / 16) = s'.entry (j / 16)) :
    program.evalE (program.reader e) 1 (.leaf v) j =
      program.evalE (program.reader e) 1 (.leaf v') j := by
  rw [RealizedProgram.evalE_leaf, RealizedProgram.evalE_leaf, RealizedProgram.reader_of_bits_of_priv e hk hw,
    RealizedProgram.reader_of_bits_of_priv e hk' hw, castElt_ofBool hf, castElt_ofBool hf', hsz, hsz', hs]

theorem evalE_458 (e : program.Env interp) {j : ℕ} (hj : j < 256) :
    program.evalE (program.reader e) 1 (.leaf 458) j =
      program.evalE (program.reader e) 1 (.leaf 457) j := by
  obtain ⟨k1, k2, k3, -⟩ := (view_kinds (program := program))
  obtain ⟨s1, s2, -, -, -, -, i3, i1, -, hf⟩ := (view_facts (program := program))
  refine reader_view_eq e k1 k2 k3 (hf 458 (by simp)) (hf 457 (by simp)) (by rw [s1, i3])
    (by rw [s2, i1]) ?_
  rw [entry_run_one (m := idx3) (a := 0) (n := 16) rfl (by omega),
    entry_run_one (m := idx1) (a := 0) (n := 100) rfl (by omega)]

theorem evalE_555 (e : program.Env interp) {j : ℕ} (hj : j < 1088) :
    program.evalE (program.reader e) 1 (.leaf 555) j =
      program.evalE (program.reader e) 1 (.leaf 506) j := by
  obtain ⟨-, -, -, k1, k2, k3, -⟩ := (view_kinds (program := program))
  obtain ⟨-, -, s1, s2, -, -, -, i1, i4, hf⟩ := (view_facts (program := program))
  refine reader_view_eq e k1 k2 k3 (hf 555 (by simp)) (hf 506 (by simp)) (by rw [s1, i4])
    (by rw [s2, i1]) ?_
  rw [entry_run_one (m := idx4) (a := 0) (n := 68) rfl (by omega),
    entry_run_one (m := idx1) (a := 0) (n := 100) rfl (by omega)]

theorem evalE_556 (e : program.Env interp) {j : ℕ} (hj : j < 1088) :
    program.evalE (program.reader e) 1 (.leaf 556) j =
      program.evalE (program.reader e) 1 (.leaf 554) j := by
  obtain ⟨-, -, -, -, -, -, k1, k2, k3⟩ := (view_kinds (program := program))
  obtain ⟨-, -, -, -, s1, s2, -, i1, i4, hf⟩ := (view_facts (program := program))
  refine reader_view_eq e k1 k2 k3 (hf 556 (by simp)) (hf 554 (by simp)) (by rw [s1, i4])
    (by rw [s2, i1]) ?_
  rw [entry_run_one (m := idx4) (a := 0) (n := 68) rfl (by omega),
    entry_run_one (m := idx1) (a := 0) (n := 100) rfl (by omega)]

/-! ## The permutations' inputs -/

theorem idx13_id {t : ℕ} (ht : t < 512) : idx13.entry t = t :=
  (entry_run_one (m := idx13) (a := 0) (n := 512) rfl ht).trans (Nat.zero_add t)

theorem idx14_id {t : ℕ} (ht : t < 528) : idx14.entry t = t :=
  (entry_run_one (m := idx14) (a := 0) (n := 528) rfl ht).trans (Nat.zero_add t)

theorem idx15_id {t : ℕ} (ht : t < 560) : idx15.entry t = t :=
  (entry_run_one (m := idx15) (a := 0) (n := 560) rfl ht).trans (Nat.zero_add t)

theorem idx16_id {t : ℕ} (ht : t < 1088) : idx16.entry t = t :=
  (entry_run_one (m := idx16) (a := 0) (n := 1088) rfl ht).trans (Nat.zero_add t)

theorem idx17_id {t : ℕ} (ht : t < 1600) : idx17.entry t = t :=
  (entry_run_one (m := idx17) (a := 0) (n := 1600) rfl ht).trans (Nat.zero_add t)

theorem idx38_id {t : ℕ} (ht : t < 6144) : idx38.entry t = t :=
  (entry_run_one (m := idx38) (a := 0) (n := 6144) rfl ht).trans (Nat.zero_add t)

theorem idx39_id {t : ℕ} (ht : t < 6656) : idx39.entry t = t :=
  (entry_run_one (m := idx39) (a := 0) (n := 6656) rfl ht).trans (Nat.zero_add t)

theorem idx40_id {t : ℕ} (ht : t < 7616) : idx40.entry t = t :=
  (entry_run_one (m := idx40) (a := 0) (n := 7616) rfl ht).trans (Nat.zero_add t)

theorem idx47_id {t : ℕ} (ht : t < 256) : idx47.entry t = t :=
  (entry_run_one (m := idx47) (a := 0) (n := 256) rfl ht).trans (Nat.zero_add t)

set_option maxRecDepth 4096 in
/-- The shared expressions of the permutations' inputs (generated data). -/
theorem hash_exprs : program.expr 11 = .reindex idx16 (.concat (.reindex idx14 (.concat (.reindex idx13 (.leaf 67)) (.leaf 9))) (.reindex idx15 (.leaf 68))) ∧ program.expr 12 = .reindex idx17 (.reindex idx17 (.concat (.reindex idx16 (.reindex idx16 (.ref 11))) (.leaf 10))) ∧ program.expr 66 = .reindex idx40 (.concat (.reindex idx39 (.reindex idx39 (.concat (.reindex idx13 (.leaf 121)) (.reindex idx38 (.leaf 71))))) (.leaf 41)) ∧ program.expr 67 = .reindex idx17 (.reindex idx17 (.concat (.reindex idx16 (.ref 66)) (.leaf 10))) ∧ program.expr 410 = .reindex idx17 (.reindex idx17 (.concat (.reindex idx16 (.reindex idx16 (.concat (.reindex idx47 (.reindex idx47 (.leaf 458))) (.leaf 42)))) (.leaf 10))) ∧ program.expr 459 = .reindex idx17 (.reindex idx17 (.leaf 506)) :=
  MldsaHHash.hash_exprs


set_option maxRecDepth 4096 in
/-- The inputs of `c̃'`'s later absorbs: the previous output plus the absorbed block
(generated data). -/
theorem expr_blk : ∀ p : Fin 10, 2 ≤ (p : ℕ) → (p : ℕ) ≤ 7 → program.expr (linRef p 0 - 2) = .reindex idx17 (.add (.reindex idx17 (.leaf (outVal (p - 1) 23))) (.reindex idx17 (.concat (.reindex (blkIdx p) (.ref 66)) (.leaf 10)))) ∧ blkIdx p = ([(1088 * ((p : ℕ) - 1), 1, 1088)] : RealizedProgram.IndexMap) :=
  MldsaHHash.expr_blk

/-- Facts of the inputs' sizes and constants, decided. -/
theorem hash_sizes : program.exprs.length = 526 ∧ RealizedProgram.IndexMap.size idx13 = 512 ∧ RealizedProgram.IndexMap.size idx14 = 528 ∧ RealizedProgram.IndexMap.size idx15 = 560 ∧ RealizedProgram.IndexMap.size idx16 = 1088 ∧ RealizedProgram.IndexMap.size idx17 = 1600 ∧ RealizedProgram.IndexMap.size idx38 = 6144 ∧ RealizedProgram.IndexMap.size idx39 = 6656 ∧ RealizedProgram.IndexMap.size idx40 = 7616 ∧ RealizedProgram.IndexMap.size idx47 = 256 ∧ (program.value 9).size = 16 ∧ (program.value 10).size = 512 ∧ (program.value 41).size = 960 ∧ (program.value 42).size = 832 ∧ program.constEntries 9 = List.replicate 16 0 ∧ program.constEntries 10 = List.replicate 512 0 ∧ program.constEntries 41 = List.ofFn (fun r : Fin 960 => if (r : ℕ) < 5 ∨ (r : ℕ) = 959 then 1 else 0) ∧ program.constEntries 42 = List.ofFn (fun r : Fin 832 => if (r : ℕ) < 5 ∨ (r : ℕ) = 831 then 1 else 0) ∧ (∀ v ∈ [9, 10, 41, 42], program.isConstant v = true ∧ program.valueField v = 1) :=
  MldsaHHash.hash_sizes

/-- A constant of `H` that is all zeros reads `0`. -/
theorem evalE_zeroConst (e : program.Env interp) {v n : ℕ} (hc : program.isConstant v = true)
    (hf : program.valueField v = 1) (he : program.constEntries v = List.replicate n 0) (j : ℕ) :
    program.evalE (program.reader e) 1 (.leaf v) j = 0 := by
  rw [evalE_constH e hc hf, he, getD_replicate_zero]
  exact HField.decode_zero

/-- A constant of `H` of `0`/`1` entries reads them. -/
theorem evalE_bitConst (e : program.Env interp) {v n : ℕ} (hc : program.isConstant v = true)
    (hf : program.valueField v = 1) {c : Fin n → Prop} [DecidablePred c]
    (he : program.constEntries v = List.ofFn (fun r => if c r then 1 else 0)) {j : ℕ}
    (hj : j < n) :
    program.evalE (program.reader e) 1 (.leaf v) j = if c ⟨j, hj⟩ then 1 else 0 := by
  rw [evalE_constH e hc hf, he, List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hj),
    List.getElem_ofFn]
  exact decode_bitH _

/-- **`μ`'s buffer** (`ref 11`): `tr`'s `512` bits, two zero bytes, the message part's `560`. -/
theorem evalE_ref11 (e : program.Env interp) {j : ℕ} (hj : j < 1088) :
    program.evalE (program.reader e) 1 (.ref 11) j =
      if j < 512 then program.evalE (program.reader e) 1 (.leaf 67) j
      else if j < 528 then 0 else program.evalE (program.reader e) 1 (.leaf 68) (j - 528) := by
  obtain ⟨hlen, s13, s14, -, -, -, -, -, -, -, s9, -, -, -, e9, -, -, -, hc⟩ := (hash_sizes (program := program))
  rw [RealizedProgram.evalE_ref MldsaHCross.refsOrdered _ _ (by omega), (hash_exprs (program := program)).1, RealizedProgram.evalE_reindex,
    idx16_id hj, RealizedProgram.evalE_concat, RealizedProgram.exprLen_reindex, s14]
  by_cases h1 : j < 528
  · rw [if_pos h1, RealizedProgram.evalE_reindex, idx14_id h1, RealizedProgram.evalE_concat,
      RealizedProgram.exprLen_reindex, s13]
    by_cases h2 : j < 512
    · rw [if_pos h2, if_pos h2, RealizedProgram.evalE_reindex, idx13_id h2]
    · rw [if_neg h2, if_neg h2, if_pos h1,
        evalE_zeroConst e (hc 9 (by simp)).1 (hc 9 (by simp)).2 e9]
  · rw [if_neg h1, if_neg (by omega), if_neg h1, RealizedProgram.evalE_reindex, idx15_id (by omega)]

/-- **`μ`'s absorbed state** (`ref 12`): the buffer, then the capacity's zeros. -/
theorem evalE_ref12 (e : program.Env interp) {j : ℕ} (hj : j < 1600) :
    program.evalE (program.reader e) 1 (.ref 12) j =
      if j < 1088 then program.evalE (program.reader e) 1 (.ref 11) j else 0 := by
  obtain ⟨hlen, -, -, -, s16, -, -, -, -, -, -, -, -, -, -, e10, -, -, hc⟩ := (hash_sizes (program := program))
  rw [RealizedProgram.evalE_ref MldsaHCross.refsOrdered _ _ (by omega), (hash_exprs (program := program)).2.1, RealizedProgram.evalE_reindex,
    RealizedProgram.evalE_reindex, idx17_id hj, idx17_id hj, RealizedProgram.evalE_concat,
    RealizedProgram.exprLen_reindex, s16]
  split_ifs with h
  · rw [RealizedProgram.evalE_reindex, RealizedProgram.evalE_reindex, idx16_id h, idx16_id h]
  · exact evalE_zeroConst e (hc 10 (by simp)).1 (hc 10 (by simp)).2 e10 _

/-- **`c̃'`'s padded input** (`ref 66`): `μ`'s `512` bits, `w1`'s `6144`, the padding's `960`. -/
theorem evalE_ref66 (e : program.Env interp) {j : ℕ} (hj : j < 7616) :
    program.evalE (program.reader e) 1 (.ref 66) j =
      if j < 512 then program.evalE (program.reader e) 1 (.leaf 121) j
      else if j < 6656 then program.evalE (program.reader e) 1 (.leaf 71) (j - 512)
      else if j - 6656 < 5 ∨ j - 6656 = 959 then 1 else 0 := by
  obtain ⟨hlen, s13, -, -, -, -, -, s39, -, -, -, -, -, -, -, -, e41, -, hc⟩ := (hash_sizes (program := program))
  rw [RealizedProgram.evalE_ref MldsaHCross.refsOrdered _ _ (by omega), (hash_exprs (program := program)).2.2.1, RealizedProgram.evalE_reindex,
    idx40_id hj, RealizedProgram.evalE_concat, RealizedProgram.exprLen_reindex, s39]
  by_cases h1 : j < 6656
  · rw [if_pos h1, RealizedProgram.evalE_reindex, RealizedProgram.evalE_reindex, idx39_id h1, idx39_id h1,
      RealizedProgram.evalE_concat, RealizedProgram.exprLen_reindex, s13]
    by_cases h2 : j < 512
    · rw [if_pos h2, if_pos h2, RealizedProgram.evalE_reindex, idx13_id h2]
    · rw [if_neg h2, if_neg h2, if_pos h1, RealizedProgram.evalE_reindex, idx38_id (by omega)]
  · rw [if_neg h1, if_neg (by omega), if_neg h1,
      evalE_bitConst e (hc 41 (by simp)).1 (hc 41 (by simp)).2 e41 (by omega)]

/-- **`c̃'`'s first absorbed state** (`ref 67`): block `0` of the padded input, then zeros. -/
theorem evalE_ref67 (e : program.Env interp) {j : ℕ} (hj : j < 1600) :
    program.evalE (program.reader e) 1 (.ref 67) j =
      if j < 1088 then program.evalE (program.reader e) 1 (.ref 66) j else 0 := by
  obtain ⟨hlen, -, -, -, s16, -, -, -, -, -, -, -, -, -, -, e10, -, -, hc⟩ := (hash_sizes (program := program))
  rw [RealizedProgram.evalE_ref MldsaHCross.refsOrdered _ _ (by omega), (hash_exprs (program := program)).2.2.2.1, RealizedProgram.evalE_reindex,
    RealizedProgram.evalE_reindex, idx17_id hj, idx17_id hj, RealizedProgram.evalE_concat,
    RealizedProgram.exprLen_reindex, s16]
  split_ifs with h
  · rw [RealizedProgram.evalE_reindex, idx16_id h]
  · exact evalE_zeroConst e (hc 10 (by simp)).1 (hc 10 (by simp)).2 e10 _

/-- **`c̃'`'s later absorbed states** (permutations `2 … 7`): the previous output plus block
`p − 1` of the padded input. -/
theorem evalE_blk (e : program.Env interp) {p : Fin 10} (h2 : 2 ≤ (p : ℕ)) (h7 : (p : ℕ) ≤ 7)
    {j : ℕ} (hj : j < 1600) :
    program.evalE (program.reader e) 1 (.ref (linRef p 0 - 2)) j =
      program.evalE (program.reader e) 1 (.leaf (outVal (p - 1) 23)) j +
        if j < 1088 then program.evalE (program.reader e) 1 (.ref 66) (1088 * (p - 1) + j)
        else 0 := by
  obtain ⟨hlen, -, -, -, -, -, -, -, -, -, -, -, -, -, -, e10, -, -, hc⟩ := (hash_sizes (program := program))
  obtain ⟨hex, hb⟩ := (expr_blk (program := program)) p h2 h7
  have hl : linRef p 0 - 2 < program.exprs.length := by
    rw [hlen]
    unfold linRef
    simp only [Fin.val_zero, show (p : ℕ) ≠ 0 by omega, if_false]
    omega
  rw [RealizedProgram.evalE_ref MldsaHCross.refsOrdered _ _ hl, hex, RealizedProgram.evalE_reindex, idx17_id hj,
    RealizedProgram.evalE_add, RealizedProgram.evalE_reindex, RealizedProgram.evalE_reindex, idx17_id hj,
    RealizedProgram.evalE_concat, RealizedProgram.exprLen_reindex, hb, RealizedProgram.IndexMap.size_single]
  split_ifs with h
  · rw [RealizedProgram.evalE_reindex, RealizedProgram.IndexMap.entry_step_one h]
  · rw [evalE_zeroConst e (hc 10 (by simp)).1 (hc 10 (by simp)).2 e10]

/-- **The stream's absorbed state** (`ref 410`): `c̃'`'s `256` bits, the padding's `832`, then
zeros. -/
theorem evalE_ref410 (e : program.Env interp) {j : ℕ} (hj : j < 1600) :
    program.evalE (program.reader e) 1 (.ref 410) j =
      if j < 1088 then
        (if j < 256 then program.evalE (program.reader e) 1 (.leaf 458) j
        else if j - 256 < 5 ∨ j - 256 = 831 then 1 else 0)
      else 0 := by
  obtain ⟨hlen, -, -, -, s16, -, -, -, -, s47, -, -, -, -, -, e10, -, e42, hc⟩ := (hash_sizes (program := program))
  rw [RealizedProgram.evalE_ref MldsaHCross.refsOrdered _ _ (by omega), (hash_exprs (program := program)).2.2.2.2.1, RealizedProgram.evalE_reindex,
    RealizedProgram.evalE_reindex, idx17_id hj, idx17_id hj, RealizedProgram.evalE_concat,
    RealizedProgram.exprLen_reindex, s16]
  by_cases h : j < 1088
  · rw [if_pos h, if_pos h, RealizedProgram.evalE_reindex, RealizedProgram.evalE_reindex, idx16_id h, idx16_id h,
      RealizedProgram.evalE_concat, RealizedProgram.exprLen_reindex, s47]
    by_cases h' : j < 256
    · rw [if_pos h', if_pos h', RealizedProgram.evalE_reindex, RealizedProgram.evalE_reindex, idx47_id h',
        idx47_id h']
    · rw [if_neg h', if_neg h',
        evalE_bitConst e (hc 42 (by simp)).1 (hc 42 (by simp)).2 e42 (by omega)]
  · rw [if_neg h, if_neg h, evalE_zeroConst e (hc 10 (by simp)).1 (hc 10 (by simp)).2 e10]

/-- **The stream's squeeze reads the absorb's output** (`ref 459`). -/
theorem evalE_ref459 (e : program.Env interp) {j : ℕ} (hj : j < 1600) :
    program.evalE (program.reader e) 1 (.ref 459) j =
      program.evalE (program.reader e) 1 (.leaf 506) j := by
  rw [RealizedProgram.evalE_ref MldsaHCross.refsOrdered _ _ (by rw [(hash_sizes (program := program)).1]; omega), (hash_exprs (program := program)).2.2.2.2.2,
    RealizedProgram.evalE_reindex, RealizedProgram.evalE_reindex, idx17_id hj, idx17_id hj]

/-! ## `μ`'s padding -/

set_option maxRecDepth 4096 in
/-- `μ`'s padding predicates and shared expressions (generated data). -/
theorem pad_exprs : program.predicate 42 = «p.h2c.mu.padding.monotone» ∧ program.predicate 43 = «p.h2c.mu.padding.max» ∧ program.predicate 44 = «p.h2c.mu.padding.min» ∧ program.predicate 45 = «p.h2c.mu.padding.suffix» ∧ program.predicate 46 = «p.h2c.mu.padding.zeros» ∧ program.predicate 47 = «p.h2c.mu.padding.output» ∧ program.expr 61 = .reindex idx31 (.concat (.leaf 7) (.reindex idx27 (.leaf 69))) ∧ program.expr 62 = .apply (.sum 8) (.mul (.reindex idx16 (.reindex idx16 (.ref 11))) (.reindex idx32 (.leaf 37))) ∧ program.expr 63 = .reindex idx34 (.concat (.leaf 7) (.leaf 36)) ∧ program.expr 64 = .add (.reindex idx35 (.ref 63)) (.reindex idx36 (.ref 63)) ∧ program.expr 65 = .reindex idx13 (.leaf 119) :=
  MldsaHHash.pad_exprs

/-- Facts of the flags and the padding's constants, decided. -/
theorem pad_facts : (69 < program.values.length ∧ program.IsSourceValue 69 ∧ (program.value 69).typeSource = .node ∧ (program.value 69).type = .bit) ∧ (68 < program.values.length ∧ program.IsSourceValue 68 ∧ (program.value 68).typeSource = .node ∧ (program.value 68).type = .bit) ∧ (program.value 69).size = 136 ∧ (program.value 68).size = 560 ∧ (program.value 7).size = 1 ∧ RealizedProgram.IndexMap.size idx26 = 135 ∧ RealizedProgram.IndexMap.size idx29 = 1 ∧ RealizedProgram.IndexMap.size idx30 = 1 ∧ RealizedProgram.IndexMap.size idx31 = 136 ∧ RealizedProgram.IndexMap.size idx37 = 512 ∧ idx29.entry 0 = 98 ∧ idx30.entry 0 = 65 ∧ idx34.entry 0 = 0 ∧ idx34.entry 1 = 1 ∧ idx35.entry 0 = 0 ∧ idx36.entry 0 = 1 ∧ (program.value 7).size = 1 ∧ program.constEntries 7 = [1] ∧ program.constEntries 36 = [0] ∧ program.constEntries 35 = List.replicate 135 0 ∧ program.constEntries 39 = List.replicate 136 0 ∧ (∀ i < 135, (program.constEntries 38).getD i 0 = RealizedProgram.xorSel 0x1F fun u => (program.constEntries 37).getD u 0) ∧ (∀ i < 135, (program.constEntries 40).getD i 0 = 0) ∧ (program.constEntries 40).getD 135 0 = RealizedProgram.xorSel 0x80 (fun u => (program.constEntries 37).getD u 0) ∧ (∀ v ∈ [7, 35, 36, 38, 39, 40], program.isConstant v = true ∧ program.valueField v = 1) ∧ (∀ q ∈ [42, 43, 44, 45, 46, 47], q < program.predicates.length ∧ program.inSource (program.predicate q) = true) :=
  MldsaHHash.pad_facts

theorem idx26_eq {i : ℕ} (hi : i < 135) : idx26.entry i = i + 1 :=
  (entry_run_one (m := idx26) (a := 1) (n := 135) rfl hi).trans (Nat.add_comm 1 i)
theorem idx27_id {i : ℕ} (hi : i < 135) : idx27.entry i = i :=
  (entry_run_one (m := idx27) (a := 0) (n := 135) rfl hi).trans (Nat.zero_add i)
theorem idx28_eq {i : ℕ} (hi : i < 135) : idx28.entry i = 0 :=
  entry_run_zero (m := idx28) (n := 135) rfl hi
theorem idx31_id {i : ℕ} (hi : i < 136) : idx31.entry i = i :=
  (entry_run_one (m := idx31) (a := 0) (n := 136) rfl hi).trans (Nat.zero_add i)
theorem idx33_eq {i : ℕ} (hi : i < 136) : idx33.entry i = 0 :=
  entry_run_zero (m := idx33) (n := 136) rfl hi
theorem idx37_eq {i : ℕ} (hi : i < 512) : idx37.entry i = 0 :=
  entry_run_zero (m := idx37) (n := 512) rfl hi
theorem idx32_eq {i u : ℕ} (hi : i < 136) (hu : u < 8) : idx32.entry (8 * i + u) = u := by
  unfold idx32
  rw [RealizedProgram.IndexMap.entry_rep (c := 8) (fun j => by simp [RealizedProgram.IndexMap.size, RealizedProgram.IdxSeg.shift]) hi hu]
  simp [RealizedProgram.IndexMap.entry, RealizedProgram.IdxSeg.shift, hu]

/-- A constant of `H` given by its entry list reads its entries. -/
theorem evalE_listConst (e : program.Env interp) {v : ℕ} {l : List ℕ}
    (hc : program.isConstant v = true) (hf : program.valueField v = 1)
    (he : program.constEntries v = l) (j : ℕ) :
    program.evalE (program.reader e) 1 (.leaf v) j = (interp 1).decode (l.getD j 0) := by
  rw [evalE_constH e hc hf, he]

/-- **In-message flag `i`** (value `69`). -/
def flag (e : program.Env interp) (i : ℕ) : (interp 1).K :=
  program.evalE (program.reader e) 1 (.leaf 69) i

/-- A bit-typed source value of domain `H` (by its node) is `0` or `1` where the source program
holds. -/
theorem bool_of_bitTyped {e : program.Env interp} (hs : HSat e) {v : ℕ} (hv : v ∈ hTyped)
    (hty : (program.value v).type = .bit) {i : ℕ} (hi : i < (program.value v).size) :
    program.evalE (program.reader e) 1 (.leaf v) i = 0 ∨
      program.evalE (program.reader e) 1 (.leaf v) i = 1 := by
  have h := hs.types v hv i hi
  rw [hty] at h
  exact RealizedProgram.castElt_bool h

theorem flag_bool {e : program.Env interp} (hs : HSat e) {i : ℕ} (hi : i < 136) :
    flag e i = 0 ∨ flag e i = 1 :=
  bool_of_bitTyped hs (by decide) (pad_facts (program := program)).1.2.2.2 (by rw [(pad_facts (program := program)).2.2.1]; exact hi)

/-- In characteristic two, `a + b = 0` is `a = b`. -/
theorem eq_of_add_eq_zeroH {a b : (interp 1).K} (h : a + b = 0) : a = b :=
  (eq_neg_of_add_eq_zero_left h).trans (CharTwo.neg_eq b)

theorem evalE_one7 (e : program.Env interp) (j : ℕ) (hj : j = 0) :
    program.evalE (program.reader e) 1 (.leaf 7) j = 1 := by
  have hc := (pad_facts (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 7 (by simp)
  rw [evalE_listConst e hc.1 hc.2 (pad_facts (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hj]
  exact HField.decode_one

/-- The `i`-th predicate of `μ`'s padding holds where the source program holds. -/
theorem pad_holds {e : program.Env interp} (hs : HSat e) {q : ℕ}
    (hq : q ∈ [42, 43, 44, 45, 46, 47]) : program.HoldsWith (program.reader e) (program.predicate q).body := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  exact hs.preds q (by omega) (by omega)

theorem constPad (v : ℕ) (hv : v ∈ [7, 35, 36, 38, 39, 40]) :
    program.isConstant v = true ∧ program.valueField v = 1 :=
  (pad_facts (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 v hv

/-- **`h2c.mu.padding.monotone`**: a set flag's predecessor is set. -/
theorem flag_mono {e : program.Env interp} (hs : HSat e) {i : ℕ} (hi : i < 135)
    (h : flag e (i + 1) = 1) : flag e i = 1 := by
  have hh := pad_holds hs (q := 42) (by simp)
  rw [(pad_exprs (program := program)).1] at hh
  have := hh i (by rw [RealizedProgram.exprLen_mul, RealizedProgram.exprLen_reindex, (pad_facts (program := program)).2.2.2.2.2.1]; exact hi)
  rw [RealizedProgram.evalWith_eq_iff MldsaHCross.domainField1] at this
  rw [evalE_zeroConst e (constPad 35 (by simp)).1 (constPad 35 (by simp)).2
      (pad_facts (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    RealizedProgram.evalE_mul, RealizedProgram.evalE_add, RealizedProgram.evalE_reindex, RealizedProgram.evalE_reindex,
    RealizedProgram.evalE_reindex, idx26_eq hi, idx27_id hi, idx28_eq hi, evalE_one7 e 0 rfl] at this
  change flag e (i + 1) * (flag e i + 1) = 0 at this
  rw [h, one_mul] at this
  exact eq_of_add_eq_zeroH this

/-- **`h2c.mu.padding.min`**: flag `65` (`tr ‖ 0x00 ‖ 0x00`'s last byte) is set. -/
theorem flag_65 {e : program.Env interp} (hs : HSat e) : flag e 65 = 1 := by
  have hh := pad_holds hs (q := 44) (by simp)
  rw [(pad_exprs (program := program)).2.2.1] at hh
  have := hh 0 (by rw [RealizedProgram.exprLen_add, RealizedProgram.exprLen_reindex, (pad_facts (program := program)).2.2.2.2.2.2.2.1]; norm_num)
  rw [RealizedProgram.evalWith_eq_iff MldsaHCross.domainField1] at this
  rw [evalE_listConst e (constPad 36 (by simp)).1 (constPad 36 (by simp)).2
      (pad_facts (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, RealizedProgram.evalE_add, RealizedProgram.evalE_reindex,
    (pad_facts (program := program)).2.2.2.2.2.2.2.2.2.2.2.1, evalE_one7 e 0 rfl] at this
  exact eq_of_add_eq_zeroH ((this.trans HField.decode_zero))

/-- **`h2c.mu.padding.max`**: flag `98` (past the maximum message) is clear. -/
theorem flag_98 {e : program.Env interp} (hs : HSat e) : flag e 98 = 0 := by
  have hh := pad_holds hs (q := 43) (by simp)
  rw [(pad_exprs (program := program)).2.1] at hh
  have := hh 0 (by rw [RealizedProgram.exprLen_reindex, (pad_facts (program := program)).2.2.2.2.2.2.1]; norm_num)
  rw [RealizedProgram.evalWith_eq_iff MldsaHCross.domainField1] at this
  rw [evalE_listConst e (constPad 36 (by simp)).1 (constPad 36 (by simp)).2
      (pad_facts (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, RealizedProgram.evalE_reindex,
    (pad_facts (program := program)).2.2.2.2.2.2.2.2.2.2.1] at this
  exact this.trans HField.decode_zero

/-- The set flags are downward closed. -/
theorem flag_down {e : program.Env interp} (hs : HSat e) {i j : ℕ} (hij : i ≤ j)
    (hj : j < 136) (h : flag e j = 1) : flag e i = 1 := by
  induction j, hij using Nat.le_induction with
  | base => exact h
  | succ k hik ih => exact ih (by omega) (flag_mono hs (by omega) h)

/-- **The in-message flags are the prefix of length `66 + lenOf`** (`padding.monotone`, `min`,
`max`): flag `i` is set exactly below `66 + L`, `L ≤ 32` the length the flags encode. -/
theorem flag_iff {e : program.Env interp} (hs : HSat e) {i : ℕ} (hi : i < 136) :
    flag e i = 1 ↔ i < 66 + lenOf (program.reader e) := by
  have hex : ∃ k, k < 136 ∧ flag e k ≠ 1 := ⟨98, by norm_num, by rw [flag_98 hs]; exact zero_ne_one⟩
  classical
  set m := Nat.find hex with hm
  have hm136 : m < 136 := (Nat.find_spec hex).1
  have hmclear : flag e m ≠ 1 := (Nat.find_spec hex).2
  have hbelow : ∀ k < m, flag e k = 1 := fun k hk => by
    have := Nat.find_min hex hk
    exact not_not.1 (not_and.1 this (by omega))
  have habove : ∀ k, m ≤ k → k < 136 → flag e k ≠ 1 := fun k hk hk' h =>
    hmclear (flag_down hs hk hk' h)
  have hm98 : m ≤ 98 := Nat.find_min' hex ⟨by norm_num, by rw [flag_98 hs]; exact zero_ne_one⟩
  have hm66 : 66 ≤ m := by
    by_contra hlt
    exact hmclear (flag_down hs (by omega) (by norm_num) (flag_65 hs))
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
  have hlen : lenOf (program.reader e) = m - 66 := by
    unfold lenOf
    change min 32 ((Finset.univ.filter fun k : Fin 136 => flag e k = 1).card - 66) = _
    rw [hcard]
    omega
  rw [hlen]
  constructor
  · intro h
    by_contra hk
    exact habove i (by omega) hi h
  · intro h
    exact hbelow i (by omega)

/-- **The shifted flags** (`ref 61`): `1` at byte `0`, then flag `i − 1`. -/
theorem evalE_ref61 (e : program.Env interp) {i : ℕ} (hi : i < 136) :
    program.evalE (program.reader e) 1 (.ref 61) i = if i = 0 then 1 else flag e (i - 1) := by
  rw [RealizedProgram.evalE_ref MldsaHCross.refsOrdered _ _ (by rw [(hash_sizes (program := program)).1]; omega), (pad_exprs (program := program)).2.2.2.2.2.2.1,
    RealizedProgram.evalE_reindex, idx31_id hi, RealizedProgram.evalE_concat, RealizedProgram.exprLen_leaf,
    (pad_facts (program := program)).2.2.2.2.1]
  split_ifs with h1 h2 h2
  · exact evalE_one7 e i (by omega)
  · omega
  · omega
  · rw [RealizedProgram.evalE_reindex, idx27_id (by omega)]
    rfl

/-- **`μ`'s buffer byte `i`**: bits `8 i, …, 8 i + 7` of `ref 11`. -/
def bufByte (e : program.Env interp) (i : ℕ) : BitWires (interp 1).K 8 :=
  fun u => program.evalE (program.reader e) 1 (.ref 11) (8 * i + u)

/-- **The packed buffer byte `i`** (`ref 62`): its bits embedded in the subfield basis. -/
theorem evalE_ref62 (e : program.Env interp) {i : ℕ} (hi : i < 136) :
    program.evalE (program.reader e) 1 (.ref 62) i = selF.embedBits (by decide) (bufByte e i) := by
  rw [RealizedProgram.evalE_ref MldsaHCross.refsOrdered _ _ (by rw [(hash_sizes (program := program)).1]; omega), (pad_exprs (program := program)).2.2.2.2.2.2.2.1]
  refine evalE_embed8 e hi (fun t ht => idx16_id ht) (fun u hu => idx32_eq hi hu) fun u => ?_
  rw [RealizedProgram.evalE_reindex, idx16_id (by have := u.isLt; omega)]
  rfl

/-- **The selector** (`ref 64`): `1`, the one block of `μ`'s buffer. -/
theorem evalE_ref64 (e : program.Env interp) : program.evalE (program.reader e) 1 (.ref 64) 0 = 1 := by
  have hl := (hash_sizes (program := program)).1
  rw [RealizedProgram.evalE_ref MldsaHCross.refsOrdered _ _ (by omega), (pad_exprs (program := program)).2.2.2.2.2.2.2.2.2.1,
    RealizedProgram.evalE_add, RealizedProgram.evalE_reindex, RealizedProgram.evalE_reindex,
    (pad_facts (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, (pad_facts (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    RealizedProgram.evalE_ref MldsaHCross.refsOrdered _ _ (by omega), (pad_exprs (program := program)).2.2.2.2.2.2.2.2.1,
    RealizedProgram.evalE_reindex, RealizedProgram.evalE_reindex, (pad_facts (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.1,
    (pad_facts (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.1, RealizedProgram.evalE_concat, RealizedProgram.evalE_concat,
    RealizedProgram.exprLen_leaf, (pad_facts (program := program)).2.2.2.2.1, if_pos (by norm_num), if_neg (by norm_num),
    evalE_one7 e 0 rfl, evalE_listConst e (constPad 36 (by simp)).1 (constPad 36 (by simp)).2
      (pad_facts (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
  rw [show 1 - 1 = 0 from rfl]
  change 1 + (interp 1).decode 0 = 1
  rw [HField.decode_zero, add_zero]

/-- **The embedding of a constant byte's `XOR` selection**: the packing of `c < 256`. -/
theorem decode_xorSel37 {c : ℕ} (hc : c < 256) :
    (interp 1).decode (RealizedProgram.xorSel c fun u => (program.constEntries 37).getD u 0) = selF.embed c := by
  rw [RealizedProgram.decode_xorSel, SelectionField.embed_of_lt_256 _ hc]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [MldsaHConstsSelect.c37 u u.isLt]

/-- **A Boolean byte packed as a constant byte is that byte** (`SelectionField.embedBits_eq`,
the embedding injective below `2^16`). -/
theorem natOfBits_of_embed {bits : BitWires (interp 1).K 8} (hb : AllBool bits) {c : ℕ}
    (hc : c < 256) (h : selF.embedBits (by decide) bits = selF.embed c) : natOfBits bits = c := by
  rw [selF.embedBits_eq _ hb] at h
  have hlt := natOfBits_lt bits
  exact selF.embed_injOn (show natOfBits bits < 2 ^ 16 by simp at hlt ⊢; omega)
    (show c < 2 ^ 16 by norm_num; omega) h

/-- **Entry `i` of a constant of domain `H`**, decoded in domain `H`'s field. -/
def cH (v i : ℕ) : (interp 1).K := (interp 1).decode ((program.constEntries v).getD i 0)

theorem cH_eq_zero {v i : ℕ} (h : (program.constEntries v).getD i 0 = 0) : cH (program := program) (F0 := F0) (FH := FH) v i = 0 := by
  rw [cH, h]
  exact HField.decode_zero

/-- **`h2c.mu.padding.suffix`** at byte `i`: where the shifted flag and the flag differ, the
packed byte is `0x1F`'s packing. -/
theorem suffix_eq {e : program.Env interp} (hs : HSat e) {i : ℕ} (hi : i < 136) :
    ((if i = 0 then 1 else flag e (i - 1)) + flag e i) *
      (selF.embedBits (by decide) (bufByte e i) +
        cH (program := program) (FH := FH) 38 i) = 0 := by
  have hh := pad_holds hs (q := 45) (by simp)
  rw [(pad_exprs (program := program)).2.2.2.1] at hh
  have := hh i (by
    rw [RealizedProgram.exprLen_mul, RealizedProgram.exprLen_add,
      RealizedProgram.exprLen_ref MldsaHCross.refsOrdered (by rw [(hash_sizes (program := program)).1]; norm_num), (pad_exprs (program := program)).2.2.2.2.2.2.1,
      RealizedProgram.exprLen_reindex, (pad_facts (program := program)).2.2.2.2.2.2.2.2.1]
    exact hi)
  rw [RealizedProgram.evalWith_eq_iff MldsaHCross.domainField1] at this
  rw [evalE_zeroConst e (constPad 39 (by simp)).1 (constPad 39 (by simp)).2
      (pad_facts (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    RealizedProgram.evalE_mul, RealizedProgram.evalE_add, RealizedProgram.evalE_add, evalE_ref61 e hi, evalE_ref62 e hi,
    evalE_constH e (constPad 38 (by simp)).1 (constPad 38 (by simp)).2] at this
  exact this

/-- **`h2c.mu.padding.zeros`** at byte `i`: where the shifted flag is clear, the packed byte is
`0`, or `0x80`'s packing at the last byte. -/
theorem zeros_eq {e : program.Env interp} (hs : HSat e) {i : ℕ} (hi : i < 136) :
    ((if i = 0 then 1 else flag e (i - 1)) + 1) *
      (selF.embedBits (by decide) (bufByte e i) +
        cH (program := program) (FH := FH) 40 i) = 0 := by
  have hh := pad_holds hs (q := 46) (by simp)
  rw [(pad_exprs (program := program)).2.2.2.2.1] at hh
  have := hh i (by
    rw [RealizedProgram.exprLen_mul, RealizedProgram.exprLen_add,
      RealizedProgram.exprLen_ref MldsaHCross.refsOrdered (by rw [(hash_sizes (program := program)).1]; norm_num), (pad_exprs (program := program)).2.2.2.2.2.2.1,
      RealizedProgram.exprLen_reindex, (pad_facts (program := program)).2.2.2.2.2.2.2.2.1]
    exact hi)
  rw [RealizedProgram.evalWith_eq_iff MldsaHCross.domainField1] at this
  rw [evalE_zeroConst e (constPad 39 (by simp)).1 (constPad 39 (by simp)).2
      (pad_facts (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    RealizedProgram.evalE_mul, RealizedProgram.evalE_add, RealizedProgram.evalE_add, evalE_ref61 e hi, evalE_ref62 e hi,
    RealizedProgram.evalE_reindex, idx33_eq hi, evalE_one7 e 0 rfl, RealizedProgram.evalE_mul,
    RealizedProgram.evalE_reindex, idx33_eq hi, evalE_ref64, one_mul,
    evalE_constH e (constPad 40 (by simp)).1 (constPad 40 (by simp)).2] at this
  exact this

/-- **`μ`'s buffer past its head is bits**: the message part (value `68`) is bit-typed. -/
theorem bufByte_bool {e : program.Env interp} (hs : HSat e) {i : ℕ} (hi : i < 136)
    (h66 : 66 ≤ i) : AllBool (bufByte e i) := fun u => by
  have hu := u.isLt
  change program.evalE _ 1 (.ref 11) (8 * i + u) = 0 ∨ program.evalE _ 1 (.ref 11) (8 * i + u) = 1
  rw [evalE_ref11 e (by omega), if_neg (by omega), if_neg (by omega)]
  exact bool_of_bitTyped hs (by decide) (pad_facts (program := program)).2.1.2.2.2 (by rw [(pad_facts (program := program)).2.2.2.1]; omega)

/-- **The padding byte at buffer byte `i ≥ 66 + L`**: the suffix `0x1F` at `66 + L`, `0x80` at
the last byte, `0` between. -/
def padConst (len i : ℕ) : ℕ := if i = len then 0x1F else if i = 135 then 0x80 else 0

/-- **The buffer past the message is the padding** (`padding.suffix`, `padding.zeros`). -/
theorem bufByte_pad {e : program.Env interp} (hs : HSat e) {i : ℕ} (hi : i < 136)
    (hle : 66 + lenOf (program.reader e) ≤ i) :
    natOfBits (bufByte e i) = padConst (66 + lenOf (program.reader e)) i := by
  set len := 66 + lenOf (program.reader e) with hlen
  have hL := lenOf_le (program.reader e)
  have hb := bufByte_bool hs hi (by omega)
  have hfi : flag e i = 0 := by
    rcases flag_bool hs hi with h | h
    · exact h
    · exact absurd ((flag_iff hs hi).1 h) (by omega)
  have hconst := (pad_facts (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  by_cases heq : i = len
  · have hprev : flag e (i - 1) = 1 := (flag_iff hs (by omega)).2 (by omega)
    have h := suffix_eq hs hi
    rw [if_neg (show i ≠ 0 by omega), hprev, hfi, add_zero, one_mul, cH, hconst.1 i (by omega),
      decode_xorSel37 (by norm_num)] at h
    rw [show padConst len i = 0x1F by unfold padConst; rw [if_pos heq]]
    exact natOfBits_of_embed hb (by norm_num) (eq_of_add_eq_zeroH h)
  · have hprev : flag e (i - 1) = 0 := by
      rcases flag_bool hs (show i - 1 < 136 by omega) with h | h
      · exact h
      · exact absurd ((flag_iff hs (by omega)).1 h) (by omega)
    have h := zeros_eq hs hi
    rw [if_neg (show i ≠ 0 by omega), hprev, zero_add, one_mul] at h
    by_cases h135 : i = 135
    · subst h135
      rw [cH, hconst.2.2.1, decode_xorSel37 (by norm_num)] at h
      rw [show padConst len 135 = 0x80 by unfold padConst; rw [if_neg heq, if_pos rfl]]
      exact natOfBits_of_embed hb (by norm_num) (eq_of_add_eq_zeroH h)
    · rw [cH_eq_zero (hconst.2.1 i (by omega)), add_zero] at h
      rw [show padConst len i = 0 by unfold padConst; rw [if_neg heq, if_neg h135]]
      refine natOfBits_of_embed hb (by norm_num) (h.trans ?_)
      unfold SelectionField.embed selectionEmbed
      simp

/-! ## `μ`'s call -/

/-- **`μ`'s input bytes**: the buffer's first `66 + L` bytes (`tr`, two zero bytes, the message
at the flags' length `L = lenOf`). -/
def muInput (e : program.Env interp) :
    Fin (66 + lenOf (program.reader e)) → BitWires (interp 1).K 8 :=
  fun i => bufByte e i

theorem absorbBlocks_mu (e : program.Env interp) :
    Shake256.absorbBlocks Shake256.SpongeSpec.shake256 (66 + lenOf (program.reader e)) = 1 := by
  have hL := lenOf_le (program.reader e)
  unfold Shake256.absorbBlocks
  change (66 + lenOf (program.reader e)) / 136 + 1 = 1
  omega

theorem numBlocks_mu (e : program.Env interp) :
    Shake256.numBlocks Shake256.SpongeSpec.shake256 (66 + lenOf (program.reader e)) 64 = 1 := by
  unfold Shake256.numBlocks Shake256.squeezeBlocks
  rw [absorbBlocks_mu]
  rfl

/-- **`μ`'s padded block is the buffer** (`bufByte_pad` past the message). -/
theorem paddedByte_mu {e : program.Env interp} (hs : HSat e)
    (i : Fin Shake256.SpongeSpec.shake256.rate) (b : Fin 8) :
    Shake256.paddedByte Shake256.SpongeSpec.shake256 (muInput e) 0 i b =
      program.evalE (program.reader e) 1 (.ref 11) (8 * i + b) := by
  have hi : (i : ℕ) < 136 := i.isLt
  have hL := lenOf_le (program.reader e)
  rw [paddedByte_bit, absorbBlocks_mu]
  simp only [Nat.mul_zero, Nat.zero_add, Nat.sub_self, and_true]
  by_cases hlt : (i : ℕ) < 66 + lenOf (program.reader e)
  · rw [dif_pos hlt, if_neg (by omega), add_zero]
    rfl
  · have hp := bufByte_pad hs hi (by omega)
    have hb := bufByte_bool hs hi (by omega)
    have hbit : program.evalE (program.reader e) 1 (.ref 11) (8 * i + b) =
        constBit (padConst (66 + lenOf (program.reader e)) i) b := by
      rw [← hp]
      exact (constBit_natOfBits hb b).symm
    rw [dif_neg hlt, hbit]
    unfold padConst
    by_cases heq : (i : ℕ) = 66 + lenOf (program.reader e)
    · rw [if_pos heq, if_pos heq, if_neg (by omega), add_zero]
    · rw [if_neg heq, if_neg heq, zero_add]
      by_cases h135 : (i : ℕ) = 135
      · rw [if_pos h135, if_pos h135]
      · rw [if_neg h135, if_neg h135]
        simp [constBit]

/-- **`μ`'s absorb permutation reads the padded input** xored into the zero state. -/
theorem absorbed_mu {e : program.Env interp} (hs : HSat e) :
    permStates e 0 0 = Shake256.xorinBlock Shake256.SpongeSpec.shake256 (fun _ _ _ => 0)
      (Shake256.paddedByte Shake256.SpongeSpec.shake256 (muInput e) 0) := by
  rw [show (fun _ _ _ => (0 : (interp 1).K)) = RealizedProgram.stateOf (fun _ => 0) from rfl,
    xorinBlock_stateOf _ (fun j => program.evalE (program.reader e) 1 (.ref 11) j) _
      (paddedByte_mu hs), permStates_zero]
  refine stateOf_congr fun j hj => ?_
  rw [show linRef 0 0 - 2 = 12 from rfl, evalE_ref12 e hj]
  split_ifs
  · exact (zero_add _).symm
  · rfl

/-- **`μ`'s buffer bytes are bits** where `tr`'s entries are. -/
theorem muInput_bool {e : program.Env interp} (hs : HSat e)
    (htr : AllBool (trBits (program.reader e))) (i : Fin (66 + lenOf (program.reader e))) :
    AllBool (muInput e i) := fun u => by
  have hL := lenOf_le (program.reader e)
  have hi := i.isLt
  have hu := u.isLt
  simp only [muInput, bufByte]
  rw [evalE_ref11 e (by omega)]
  split_ifs with h1 h2
  · exact htr ⟨8 * i + u, by omega⟩
  · exact .inl rfl
  · exact bool_of_bitTyped hs (by decide) (pad_facts (program := program)).2.1.2.2.2 (by rw [(pad_facts (program := program)).2.2.2.1]; omega)

/-- **`μ`'s output state**: the absorb permutation's last round output (value `119`). -/
def muFin (e : program.Env interp) (_ : ℕ) : State (interp 1).K :=
  RealizedProgram.stateOf (program.evalE (program.reader e) 1 (.leaf 119))

/-- **`μ`'s output bytes**: read off the absorb permutation where `tr` is bits; otherwise the
SHAKE256 bytes of the input as constant bits (the view reads the program only where `tr` is
bits). -/
noncomputable def muOut (e : program.Env interp) : Fin 64 → BitWires (interp 1).K 8 := by
  classical
  exact if AllBool (trBits (program.reader e)) then
    Shake256.squeezeOut (sp := Shake256.SpongeSpec.shake256)
      (len := 66 + lenOf (program.reader e)) fun k => muFin e k
  else fun o => Shake256.constByte (xofFin Shake256.SpongeSpec.shake256.xof
    (Shake256.inputBytes (muInput e)) 64 o)

/-- **`μ`'s hash soundness** (`Shake256.squeezeOut_sound` at the absorb permutation). -/
theorem muOut_sound {e : program.Env interp} (hs : HSat e) (o : Fin 64) :
    natOfBits (muOut e o) =
      xofFin Shake256.SpongeSpec.shake256.xof (Shake256.inputBytes (muInput e)) 64 o := by
  classical
  unfold muOut
  split_ifs with htr
  · refine Shake256.squeezeOut_sound (muInput_bool hs htr) (fun j h => ?_) o
    have hj : (j : ℕ) = 0 := by
      have := lt_of_lt_of_eq j.isLt (numBlocks_mu e)
      omega
    have hin : Shake256.inputOf Shake256.SpongeSpec.shake256 (muInput e)
        (n := Shake256.numBlocks Shake256.SpongeSpec.shake256 (66 + lenOf (program.reader e)) 64)
        (fun k => muFin e k) j = permStates e 0 0 := by
      unfold Shake256.inputOf Shake256.priorOf
      rw [hj, absorbBlocks_mu, if_pos (by norm_num), dif_neg (by omega), absorbed_mu hs]
    rw [hin] at h
    have hf : muFin e j = permStates e 0 (Fin.last 24) := by
      rw [permStates_last]
      rfl
    change Shake256.Encodes (muFin e j) _
    rw [hf]
    exact (permRelation hs 0).encodes h
  · rw [Shake256.natOfBits_constByte, Nat.mod_eq_of_lt]
    rw [Shake256.SpongeSpec.xof_shake256]
    exact xofFin_shake256_lt _ _ _

/-- **`h2c.mu.padding.output`**: `μ`'s output bits are the absorb permutation's first `512`
output bits. -/
theorem evalE_muOut {e : program.Env interp} (hs : HSat e) {j : ℕ} (hj : j < 512) :
    program.evalE (program.reader e) 1 (.leaf 121) j =
      program.evalE (program.reader e) 1 (.leaf 119) j := by
  have hh := pad_holds hs (q := 47) (by simp)
  rw [(pad_exprs (program := program)).2.2.2.2.2.1] at hh
  have := hh j (by rw [RealizedProgram.exprLen_mul, RealizedProgram.exprLen_reindex, (pad_facts (program := program)).2.2.2.2.2.2.2.2.2.1]; exact hj)
  rw [RealizedProgram.evalWith_eq_iff MldsaHCross.domainField1] at this
  rw [evalE_zeroConst e ((hash_sizes (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 10 (by simp)).1
      ((hash_sizes (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 10 (by simp)).2
      (hash_sizes (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    RealizedProgram.evalE_mul, RealizedProgram.evalE_reindex, idx37_eq hj, evalE_ref64, one_mul,
    RealizedProgram.evalE_add, RealizedProgram.evalE_reindex, RealizedProgram.evalE_reindex, idx13_id hj,
    RealizedProgram.evalE_ref MldsaHCross.refsOrdered _ _ (by rw [(hash_sizes (program := program)).1]; norm_num), (pad_exprs (program := program)).2.2.2.2.2.2.2.2.2.2,
    RealizedProgram.evalE_reindex, idx13_id hj] at this
  exact eq_of_add_eq_zeroH this

/-- **`μ`'s output is `h2c.mu.out`** where `tr` is bits. -/
theorem muOut_eq {e : program.Env interp} (hs : HSat e)
    (htr : AllBool (trBits (program.reader e))) (o : Fin 64) :
    muOut e o = Falcon512.HashCircuit.byteWires (muBits (program.reader e)) o := by
  classical
  unfold muOut
  rw [if_pos htr]
  funext j
  have ho := o.isLt
  have hj := j.isLt
  rw [squeezeOut_stateOf (fin := muFin e) (fun _ k => program.evalE (program.reader e) 1 (.leaf 119) k)
    (fun _ => rfl) o j (by rw [numBlocks_mu, absorbBlocks_mu]; omega)]
  rw [Nat.mod_eq_of_lt (by omega), ← evalE_muOut hs (by omega)]
  rfl

/-- **The input bytes of `μ`'s call** are `tr ‖ 0x00 ‖ 0x00 ‖ M`. -/
theorem inputBytes_mu (e : program.Env interp) :
    Shake256.inputBytes (muInput e) =
      Shake256.inputBytes (Falcon512.HashCircuit.byteWires (trBits (program.reader e))) ++ [0, 0] ++
        (List.ofFn (messageBytes (program.reader e))).map UInt8.toNat := by
  have hzero : natOfBits (fun _ : Fin 8 => (0 : (interp 1).K)) = 0 := by
    have := natOfBits_constBit (K := (interp 1).K) (m := 8) 0
    simpa [constBit] using this
  apply List.ext_getElem
  · simp [Shake256.inputBytes]
    omega
  intro n h₁ h₂
  simp only [Shake256.inputBytes, List.length_ofFn] at h₁
  simp only [Shake256.inputBytes, List.getElem_ofFn]
  have hbyte : ∀ i : ℕ, (hi : i < 136) → natOfBits (bufByte e i) =
      natOfBits (fun u : Fin 8 => if 8 * i + (u : ℕ) < 512 then
        program.evalE (program.reader e) 1 (.leaf 67) (8 * i + u)
        else if 8 * i + (u : ℕ) < 528 then 0
        else program.evalE (program.reader e) 1 (.leaf 68) (8 * i + u - 528)) := fun i hi => by
    refine congrArg natOfBits (funext fun u => ?_)
    exact evalE_ref11 e (by have := u.isLt; omega)
  rw [show muInput e ⟨n, h₁⟩ = bufByte e n from rfl, hbyte n (by have := lenOf_le (program.reader e); omega)]
  by_cases h64 : n < 64
  · rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega),
      List.getElem_ofFn]
    refine congrArg natOfBits (funext fun u => ?_)
    rw [if_pos (by have := u.isLt; omega)]
    rfl
  · by_cases h66 : n < 66
    · rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp; omega)]
      have hz : (fun u : Fin 8 => if 8 * n + (u : ℕ) < 512 then
          program.evalE (program.reader e) 1 (.leaf 67) (8 * n + u)
          else if 8 * n + (u : ℕ) < 528 then 0
          else program.evalE (program.reader e) 1 (.leaf 68) (8 * n + u - 528)) = fun _ => 0 := by
        funext u
        have := u.isLt
        rw [if_neg (by omega), if_pos (by omega)]
      rw [hz, hzero]
      simp only [List.length_ofFn, List.length_map]
      interval_cases n <;> rfl
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.length_append, List.length_ofFn, List.length_map, List.length_cons,
        List.length_nil, List.getElem_map, List.getElem_ofFn]
      rw [messageBytes, Native.toNat_toUInt8_natOfBits]
      refine congrArg natOfBits (funext fun u => ?_)
      have := u.isLt
      rw [if_neg (by omega), if_neg (by omega)]
      simp only [Falcon512.HashCircuit.byteWires, messageBits]
      rw [show 8 * n + (u : ℕ) - 528 = 8 * (n - 66) + u by omega]

/-- **The SHAKE256 call of `μ`** (`SpongeView`): the buffer's first `66 + L` bytes, the output
read off the absorb permutation where `tr` is bits. -/
noncomputable def muSponge : HSponge program F0 FH 64 where
  len e := 66 + lenOf (program.reader e)
  input := muInput
  out := muOut
  sound _ hs o := muOut_sound hs o

theorem muSponge_out {e : program.Env interp} (hs : HSat e)
    (htr : AllBool (trBits (program.reader e))) (o : Fin 64) :
    natOfBits (muSponge.out e o) = natOfBits (Falcon512.HashCircuit.byteWires (muBits (program.reader e)) o) := by
  change natOfBits (muOut e o) = _
  rw [muOut_eq hs htr o]

/-! ## `c̃'`'s call -/

theorem evalE_leaf_congr {rd : program.Valuation interp} {v a b : ℕ} (h : a = b) :
    program.evalE rd 1 (.leaf v) a = program.evalE rd 1 (.leaf v) b := h ▸ rfl

/-- The bits of `0x1F`. -/
theorem constBit_1F {K : Type*} [Field K] {b : ℕ} (hb : b < 8) :
    constBit (K := K) 0x1F b = if b < 5 then 1 else 0 := by
  interval_cases b <;> simp [constBit]

/-- The bits of `0x80`. -/
theorem constBit_80 {K : Type*} [Field K] {b : ℕ} (hb : b < 8) :
    constBit (K := K) 0x80 b = if b = 7 then 1 else 0 := by
  interval_cases b <;> simp [constBit]

set_option maxRecDepth 4096 in
/-- The kinds of `μ`'s output, `w1` and `c̃'` (bit views, generated data). -/
theorem bit_kinds : (program.value 121).kind = .bits 120 idx2 ∧ (program.value 71).kind = .bits 70 idx0 :=
  MldsaHHash.bit_kinds

theorem leaf_bool (e : program.Env interp) {v w : ℕ} {sel : RealizedProgram.IndexMap}
    (hk : (program.value v).kind = .bits w sel) (i : ℕ) :
    program.evalE (program.reader e) 1 (.leaf v) i = 0 ∨
      program.evalE (program.reader e) 1 (.leaf v) i = 1 := by
  rw [RealizedProgram.evalE_leaf]
  exact RealizedProgram.castElt_bool (RealizedProgram.reader_bool_of_bits e hk i)

/-- **`c̃'`'s input bytes**: `μ`'s `64` bytes, then `w1Encode(w1)`'s `768`. -/
def ctInput (e : program.Env interp) : Fin (64 + 768) → BitWires (interp 1).K 8 :=
  fun i u => if h : (i : ℕ) < 64 then muBits (program.reader e) ⟨8 * i + u, by omega⟩
    else w1HBits (program.reader e) ⟨8 * (i - 64) + u, by omega⟩

theorem inputBytes_ct (e : program.Env interp) :
    Shake256.inputBytes (ctInput e) =
      Shake256.inputBytes (Falcon512.HashCircuit.byteWires (muBits (program.reader e))) ++
        Shake256.inputBytes (Falcon512.HashCircuit.byteWires (w1HBits (program.reader e))) := by
  unfold Shake256.inputBytes
  rw [List.ofFn_add]
  refine congrArg₂ (· ++ ·) (List.ofFn_inj.2 (funext fun i => ?_))
    (List.ofFn_inj.2 (funext fun i => ?_))
  · refine congrArg natOfBits (funext fun u => ?_)
    simp only [ctInput, Falcon512.HashCircuit.byteWires, Fin.coe_castLE, Fin.val_castAdd, muBits, w1HBits]
    split_ifs
    · exact evalE_leaf_congr rfl
    · omega
  · refine congrArg natOfBits (funext fun u => ?_)
    simp only [ctInput, Falcon512.HashCircuit.byteWires, Fin.val_natAdd, Fin.coe_castLE, muBits, w1HBits]
    split_ifs
    · omega
    · exact evalE_leaf_congr (by omega)

theorem absorbBlocks_ct : Shake256.absorbBlocks Shake256.SpongeSpec.shake256 (64 + 768) = 7 := rfl

theorem numBlocks_ct : Shake256.numBlocks Shake256.SpongeSpec.shake256 (64 + 768) 32 = 7 := rfl

/-- **`c̃'`'s padded block `k`** is block `k` of `ref 66`. -/
theorem paddedByte_ct (e : program.Env interp) {k : ℕ} (hk : k < 7)
    (i : Fin Shake256.SpongeSpec.shake256.rate) (b : Fin 8) :
    Shake256.paddedByte Shake256.SpongeSpec.shake256 (ctInput e) k i b =
      program.evalE (program.reader e) 1 (.ref 66) (1088 * k + (8 * i + b)) := by
  have hi : (i : ℕ) < 136 := i.isLt
  have hb := b.isLt
  rw [paddedByte_bit, absorbBlocks_ct, evalE_ref66 e (by omega)]
  simp only [ctInput, muBits, w1HBits, constBit_1F hb, constBit_80 hb]
  split_ifs <;> (try simp only [add_zero, zero_add]) <;> first
    | omega
    | exact evalE_leaf_congr (by omega)

/-- **`c̃'`'s output states**: permutation `k + 1`'s last round output. -/
def ctFin (e : program.Env interp) (k : ℕ) : State (interp 1).K :=
  RealizedProgram.stateOf (program.evalE (program.reader e) 1 (.leaf (outVal (k + 1) 23)))

/-- **`c̃'`'s permutation `k + 1` reads block `k` of the padded input** xored into the previous
output (the zero state for `k = 0`). -/
theorem absorbed_ct (e : program.Env interp) {k : ℕ} (hk : k < 7) :
    permStates e ⟨k + 1, by omega⟩ 0 = Shake256.xorinBlock Shake256.SpongeSpec.shake256
      (Shake256.priorOf (n := 7) (fun j => ctFin e j) k)
      (Shake256.paddedByte Shake256.SpongeSpec.shake256 (ctInput e) k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [show Shake256.priorOf (n := 7) (fun j => ctFin e j) 0 = RealizedProgram.stateOf (fun _ => 0) from rfl,
      xorinBlock_stateOf _ (fun j => program.evalE (program.reader e) 1 (.ref 66) (1088 * 0 + j))
        _ (fun i b => (paddedByte_ct e hk i b).trans rfl), permStates_zero]
    refine stateOf_congr fun j hj => ?_
    rw [show linRef ⟨0 + 1, by omega⟩ 0 - 2 = 67 from rfl, evalE_ref67 e hj]
    split_ifs
    · rw [zero_add, Nat.mul_zero, Nat.zero_add]
    · rfl
  · have hp : Shake256.priorOf (n := 7) (fun j => ctFin e j) k = ctFin e (k - 1) := by
      unfold Shake256.priorOf
      rw [dif_pos ⟨hk0, by omega⟩]
    rw [hp, ctFin, xorinBlock_stateOf _
        (fun j => program.evalE (program.reader e) 1 (.ref 66) (1088 * k + j)) _
        (fun i b => (paddedByte_ct e hk i b).trans rfl), permStates_zero]
    refine stateOf_congr fun j hj => ?_
    rw [evalE_blk e (p := ⟨k + 1, by omega⟩) (by simp; omega) (by simp; omega) hj]
    simp only [show k - 1 + 1 = k by omega, show k + 1 - 1 = k by omega]
    split_ifs
    · rfl
    · exact add_zero _

theorem ctInput_bool (e : program.Env interp) (i : Fin (64 + 768)) : AllBool (ctInput e i) :=
  fun u => by
    simp only [ctInput]
    split_ifs
    · exact leaf_bool e (bit_kinds (program := program)).1 _
    · exact leaf_bool e (bit_kinds (program := program)).2 _

/-- **`c̃'`'s hash soundness** (`Shake256.squeezeOut_sound` at the seven absorbs). -/
theorem ctOut_sound {e : program.Env interp} (hs : HSat e) (o : Fin 32) :
    natOfBits (Shake256.squeezeOut (sp := Shake256.SpongeSpec.shake256) (len := 64 + 768)
        (fun k => ctFin e k) o) =
      xofFin Shake256.SpongeSpec.shake256.xof (Shake256.inputBytes (ctInput e)) 32 o := by
  refine Shake256.squeezeOut_sound (ctInput_bool e) (fun j h => ?_) o
  have hj : (j : ℕ) < 7 := lt_of_lt_of_eq j.isLt numBlocks_ct
  have hin : Shake256.inputOf Shake256.SpongeSpec.shake256 (ctInput e)
      (n := Shake256.numBlocks Shake256.SpongeSpec.shake256 (64 + 768) 32)
      (fun k => ctFin e k) j = permStates e ⟨j + 1, by omega⟩ 0 := by
    unfold Shake256.inputOf
    rw [absorbBlocks_ct, if_pos hj, absorbed_ct e hj]
    rfl
  rw [hin] at h
  have hf : ctFin e j = permStates e ⟨j + 1, by omega⟩ (Fin.last 24) := by
    rw [permStates_last]
    rfl
  change Shake256.Encodes (ctFin e j) _
  rw [hf]
  exact (permRelation hs _).encodes h

/-- **`c̃'`'s output is `h2c.c_tilde.out`.** -/
theorem ctOut_eq (e : program.Env interp) (o : Fin 32) :
    Shake256.squeezeOut (sp := Shake256.SpongeSpec.shake256) (len := 64 + 768)
        (fun k => ctFin e k) o = Falcon512.HashCircuit.byteWires (cTildeBits (program.reader e)) o := by
  funext j
  have ho := o.isLt
  have hj := j.isLt
  rw [squeezeOut_stateOf (fin := ctFin e)
    (fun k i => program.evalE (program.reader e) 1 (.leaf (outVal (k + 1) 23)) i)
    (fun _ => rfl) o j (by rw [numBlocks_ct, absorbBlocks_ct]; omega)]
  rw [absorbBlocks_ct, Nat.mod_eq_of_lt (by omega), show 7 - 1 + (o : ℕ) / 136 + 1 = 7 by omega,
    show outVal 7 23 = 457 from rfl, ← evalE_458 e (by omega)]
  rfl

/-- **The SHAKE256 call of `c̃'`** (`SpongeView`): `μ ‖ w1`, the output read off the seventh
absorb. -/
def cTildeSponge : HSponge program F0 FH 32 where
  len _ := 64 + 768
  input := ctInput
  out e := Shake256.squeezeOut (sp := Shake256.SpongeSpec.shake256) (len := 64 + 768)
    fun k => ctFin e k
  sound _ hs o := ctOut_sound hs o

/-! ## The SampleInBall stream's call -/

set_option maxRecDepth 4096 in
theorem kind458 : (program.value 458).kind = .bits 456 idx3 :=
  MldsaHHash.kind458

theorem absorbBlocks_sib : Shake256.absorbBlocks Shake256.SpongeSpec.shake256 32 = 1 := rfl

theorem numBlocks_sib : Shake256.numBlocks Shake256.SpongeSpec.shake256 32 272 = 2 := rfl

/-- **The stream's padded block** is `ref 410`. -/
theorem paddedByte_sib (e : program.Env interp) (i : Fin Shake256.SpongeSpec.shake256.rate)
    (b : Fin 8) :
    Shake256.paddedByte Shake256.SpongeSpec.shake256
        (Falcon512.HashCircuit.byteWires (cTildeBits (program.reader e))) 0 i b =
      program.evalE (program.reader e) 1 (.ref 410) (8 * i + b) := by
  have hi : (i : ℕ) < 136 := i.isLt
  have hb := b.isLt
  rw [paddedByte_bit, absorbBlocks_sib, evalE_ref410 e (by omega)]
  simp only [Falcon512.HashCircuit.byteWires, cTildeBits, constBit_1F hb, constBit_80 hb, and_true]
  split_ifs <;> (try simp only [add_zero, zero_add]) <;> first
    | omega
    | exact evalE_leaf_congr (by omega)

/-- **The stream's output states**: permutation `8 + k`'s last round output. -/
def sbFin (e : program.Env interp) (k : ℕ) : State (interp 1).K :=
  RealizedProgram.stateOf (program.evalE (program.reader e) 1 (.leaf (outVal (8 + k) 23)))

theorem absorbed_sib (e : program.Env interp) :
    permStates e 8 0 = Shake256.xorinBlock Shake256.SpongeSpec.shake256 (fun _ _ _ => 0)
      (Shake256.paddedByte Shake256.SpongeSpec.shake256
        (Falcon512.HashCircuit.byteWires (cTildeBits (program.reader e))) 0) := by
  rw [show (fun _ _ _ => (0 : (interp 1).K)) = RealizedProgram.stateOf (fun _ => 0) from rfl,
    xorinBlock_stateOf _ (fun j => program.evalE (program.reader e) 1 (.ref 410) j) _
      (paddedByte_sib e), permStates_zero]
  refine stateOf_congr fun j hj => ?_
  rw [show linRef 8 0 - 2 = 410 from rfl]
  split_ifs with h
  · exact (zero_add _).symm
  · rw [evalE_ref410 e hj, if_neg h]

/-- **The stream's hash soundness** (`Shake256.squeezeOut_sound` at the absorb and the
squeeze). -/
theorem sbOut_sound {e : program.Env interp} (hs : HSat e) (o : Fin 272) :
    natOfBits (Shake256.squeezeOut (sp := Shake256.SpongeSpec.shake256) (len := 32)
        (fun k => sbFin e k) o) =
      xofFin Shake256.SpongeSpec.shake256.xof
        (Shake256.inputBytes (Falcon512.HashCircuit.byteWires (cTildeBits (program.reader e)))) 272 o := by
  refine Shake256.squeezeOut_sound
    (Falcon512.HashCircuit.byteWires_allBool fun t => leaf_bool e (kind458 (program := program)) _) (fun j h => ?_) o
  have hj : (j : ℕ) < 2 := lt_of_lt_of_eq j.isLt numBlocks_sib
  have key : ∀ m : ℕ, (hm : m < 2) →
      Shake256.inputOf Shake256.SpongeSpec.shake256
        (Falcon512.HashCircuit.byteWires (cTildeBits (program.reader e)))
        (n := Shake256.numBlocks Shake256.SpongeSpec.shake256 32 272)
        (fun k => sbFin e k) m = permStates e ⟨8 + m, by omega⟩ 0 ∧
      sbFin e m = permStates e ⟨8 + m, by omega⟩ (Fin.last 24) := by
    intro m hm
    refine ⟨?_, by rw [permStates_last]; rfl⟩
    unfold Shake256.inputOf Shake256.priorOf
    rw [absorbBlocks_sib]
    rcases (show m = 0 ∨ m = 1 by omega) with rfl | rfl
    · rw [if_pos (by norm_num), dif_neg (by omega)]
      exact (absorbed_sib e).symm
    · rw [if_neg (by norm_num), dif_pos ⟨by norm_num, by rw [numBlocks_sib]; norm_num⟩,
        permStates_zero]
      refine stateOf_congr fun i hi => ?_
      rw [show linRef ⟨8 + 1, by omega⟩ 0 - 2 = 459 from rfl, evalE_ref459 e hi]
      rfl
  obtain ⟨hin, hf⟩ := key j hj
  change Shake256.Encodes (sbFin e j) _
  rw [hf]
  change Shake256.Encodes (Shake256.inputOf Shake256.SpongeSpec.shake256
    (Falcon512.HashCircuit.byteWires (cTildeBits (program.reader e)))
    (n := Shake256.numBlocks Shake256.SpongeSpec.shake256 32 272)
    (fun k => sbFin e k) j) _ at h
  rw [hin] at h
  exact (permRelation hs _).encodes h

/-- **The stream's output is `h2c.sib.out`.** -/
theorem sbOut_eq (e : program.Env interp) (o : Fin 272) :
    natOfBits (Shake256.squeezeOut (sp := Shake256.SpongeSpec.shake256) (len := 32)
        (fun k => sbFin e k) o) = sibStream (program.reader e) o := by
  refine congrArg natOfBits (funext fun j => ?_)
  have ho := o.isLt
  have hj := j.isLt
  rw [squeezeOut_stateOf (fin := sbFin e)
    (fun k i => program.evalE (program.reader e) 1 (.leaf (outVal (8 + k) 23)) i)
    (fun _ => rfl) o j (by rw [numBlocks_sib, absorbBlocks_sib]; omega), absorbBlocks_sib]
  show _ = sibBits (program.reader e) ⟨8 * o + j, by omega⟩
  unfold sibBits
  rcases Nat.lt_or_ge (o : ℕ) 136 with h1 | h1
  · rw [if_pos (by simp; omega), show 1 - 1 + (o : ℕ) / 136 = 0 by omega,
      show outVal (8 + 0) 23 = 506 from rfl, Nat.mod_eq_of_lt h1, ← evalE_555 e (by omega)]
  · rw [if_neg (by simp; omega), show 1 - 1 + (o : ℕ) / 136 = 1 by omega,
      show outVal (8 + 1) 23 = 554 from rfl, ← evalE_556 e (by omega)]
    exact evalE_leaf_congr (by simp only; omega)

/-- **The SHAKE256 call of the SampleInBall stream** (`SpongeView`): `c̃'`, the output read off
the absorb and the squeeze. -/
def sibSponge : HSponge program F0 FH 272 where
  len _ := 32
  input e := Falcon512.HashCircuit.byteWires (cTildeBits (program.reader e))
  out e := Shake256.squeezeOut (sp := Shake256.SpongeSpec.shake256) (len := 32)
    fun k => sbFin e k
  sound _ hs o := sbOut_sound hs o

/-! ## The hash view -/

theorem muSponge_input (e : program.Env interp) :
    Shake256.inputBytes (muSponge.input e) =
      Shake256.inputBytes (Falcon512.HashCircuit.byteWires (trBits (program.reader e))) ++ [0, 0] ++
        (List.ofFn (messageBytes (program.reader e))).map UInt8.toNat := by
  simp only [muSponge]
  exact inputBytes_mu e

theorem cTildeSponge_input (e : program.Env interp) :
    Shake256.inputBytes (cTildeSponge.input e) =
      Shake256.inputBytes (Falcon512.HashCircuit.byteWires (muBits (program.reader e))) ++
        Shake256.inputBytes (Falcon512.HashCircuit.byteWires (w1HBits (program.reader e))) := by
  change Shake256.inputBytes (ctInput e) = _
  exact inputBytes_ct e

theorem cTildeSponge_out (e : program.Env interp) (o : Fin 32) :
    natOfBits (cTildeSponge.out e o) =
      natOfBits (Falcon512.HashCircuit.byteWires (cTildeBits (program.reader e)) o) := by
  change natOfBits (Shake256.squeezeOut (sp := Shake256.SpongeSpec.shake256) (len := 64 + 768)
    (fun k => ctFin e k) o) = _
  rw [ctOut_eq e o]

theorem sibSponge_out (e : program.Env interp) (o : Fin 272) :
    natOfBits (sibSponge.out e o) = sibStream (program.reader e) o := by
  change natOfBits (Shake256.squeezeOut (sp := Shake256.SpongeSpec.shake256) (len := 32)
    (fun k => sbFin e k) o) = _
  exact sbOut_eq e o

theorem sibSponge_input (e : program.Env interp) :
    Shake256.inputBytes (sibSponge.input e) =
      Shake256.inputBytes (Falcon512.HashCircuit.byteWires (cTildeBits (program.reader e))) := by
  simp only [sibSponge]

/-- **The hash view of `MLDSA44.Native.ROMParams`** (`HashView`): the three SHAKE256 calls `muSponge`,
`cTildeSponge` and `sibSponge`, their inputs and outputs the program's readings. -/
noncomputable def hashView : HashView program F0 FH where
  mu := muSponge
  cTilde := cTildeSponge
  sib := sibSponge
  mu_input e _ := muSponge_input e
  mu_out _ hs htr o := muSponge_out hs htr o
  cTilde_input e _ := cTildeSponge_input e
  cTilde_out e _ o := cTildeSponge_out e o
  sib_input e _ := sibSponge_input e
  sib_out e _ o := sibSponge_out e o

end GordieHowe.MLDSA44.Native.ROMParams
