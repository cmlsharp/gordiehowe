-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Honest.Source
public import GordieHowe.Applications.Falcon512.Native.ROMParams.Frontend.Hash
public import GordieHowe.Applications.Falcon512.System.Honest

@[expose] public section

/-!
# GordieHowe: the honest SHAKE256 call of a native Falcon program

The converse of the frontend's hash view (`GordieHowe/Applications/Falcon512/Native/ROMParams/Frontend/Hash.lean`): at the source environment
of honest committed values whose trace words are the packed states of an honest Keccak trace
(`WordsAgree`), the `240` round predicates hold (`round_holds`, `GordieHowe.RealizedProgram.holdsWith_of_shapes` on the
round relations of the trace, `KeccakTrace.roundRelation_iff`). Generic in the program
(`FalconHHonest`: the frontend's hash facts and the honest prover's views, decided per program) and
the fields.
-/

namespace GordieHowe.Falcon512.Native.ROMParams

open Generated.Falcon512.Native.ROMParams.Program hiding program
open GordieHowe.Bits GordieHowe.Keccak GordieHowe.KeccakTrace

/-- **The committed words of round `t` of permutation `p`**: the value its output view reads. -/
def wordsVal (p : Fin 10) (t : Fin 24) : ℕ := outVal p t - 1

/-- **The program facts of the honest hash** (`FalconHHash` and): each round's output and
`h2p.shake.state` are bit views `idx0` of their committed words, `100` words of `GF(2^16)` in
domain `H`'s field; the nonce, the message part and the flags are committed cells of domain `H`.
Each program instantiates it by `decide`. -/
class FalconHHonest (program : RealizedProgram) : Prop extends FalconHHash program where
  /-- The rounds' outputs are bit views of their committed words. -/
  words_checks : ∀ p : Fin 10, ∀ t : Fin 24,
    program.isBitsB (outVal p t) (wordsVal p t) idx0 = true ∧
      program.privCellB (wordsVal p t) = true ∧ program.valueField (outVal p t) = 0 ∧
      program.valueField (wordsVal p t) = 0 ∧ (program.value (outVal p t)).size = 1600 ∧
      (program.value (wordsVal p t)).size = 100 ∧
      (program.value (wordsVal p t)).type.nodeName = some "GF(2^16)"
  /-- `h2p.shake.state` is the bit view of its committed words. -/
  state_checks : program.isBitsB 97 96 idx0 = true ∧ program.privCellB 96 = true ∧
    program.valueField 97 = 0 ∧ program.valueField 96 = 0 ∧ (program.value 97).size = 1600 ∧
    (program.value 96).size = 100 ∧ (program.value 96).type.nodeName = some "GF(2^16)"
  /-- The nonce, the message part and the flags are checked committed values of domain `H`. -/
  buf_checks : program.privCellB 45 = true ∧ program.privCellB 46 = true ∧
    program.privCellB 47 = true ∧ program.valueField 45 = 0 ∧ program.valueField 46 = 0 ∧
    program.valueField 47 = 0

open FalconHHash FalconHHashData FalconHHonest

set_option linter.unusedSectionVars false

variable {program : RealizedProgram} [FalconHHonest program] {FH FA : RealizedProgram.FieldInterp} [HField FH]
  [AField FA] [FalconHBase program] [FalconHConsts program FH] [FalconSelField program FH FA]

set_option hygiene false in
local notation "interp" => RealizedProgram.falconInterpOf FH FA

/-- **A bit read from a Boolean field element**: `ofBool (x = 1)` is `x`. -/
theorem ofBool_decide_eq {x : (interp 0).K} (hx : x = 0 ∨ x = 1) :
    (interp 0).ofBool (decide (x = 1)) = x := by
  rcases hx with rfl | rfl <;> simp [RealizedProgram.FieldInterp.ofBool]

/-- **A coordinate of an element of domain `H`'s field cast into a field identifier equal to
`0`.** -/
theorem coord_castElt {a : ℕ} (h : a = 0) (s : String) (y : (interp 0).K) (j : ℕ) :
    (interp a).coord s (RealizedProgram.castElt (a := 0) (b := a) y) j = FH.coord s y j := by
  subst h
  rw [RealizedProgram.castElt_self]
  rfl

/-- **A bit view of packed state words reads the state's bits** at the source environment. -/
theorem evalE_words {val : program.Valuation interp} {x : program.Valuation interp}
    {c : ∀ k, (program.layout interp).Ch k} {π : (program.layout interp).Pads} {v w : ℕ}
    {S : State FH.K} (hS : ∀ x y, AllBool (S x y))
    (hb : program.isBitsB v w idx0 = true) (hw : program.privCellB w = true)
    (hfv : program.valueField v = 0) (hfw : program.valueField w = 0)
    (hsv : (program.value v).size = 1600) (hsw : (program.value w).size = 100)
    (hn : (program.value w).type.nodeName = some "GF(2^16)")
    (hval : ∀ i < 100, val w i = RealizedProgram.castElt (a := 0) (RealizedProgram.stateWords HField.packing S i))
    {j : ℕ} (hj : j < 1600) :
    program.evalE (program.reader (program.srcEnv interp x val c π)) 0 (.leaf v) j =
      RealizedProgram.stateBit S j := by
  obtain ⟨-, -, -, he0, -, -, -⟩ := view_sel (program := program)
  have hsel : idx0.size = 100 := (view_sel (program := program)).1
  have hq : j / (1600 / 100) < 100 := by omega
  rw [RealizedProgram.evalE_leaf, RealizedProgram.reader_srcEnv_bits x val c π hb hw (by
    rw [hsv, hsel, he0 _ hq, hsw]; exact hq), hsv, hsel, he0 _ hq, hval _ hq, hn]
  rw [castElt_ofBool hfv, coord_castElt hfw]
  change (interp 0).ofBool (FH.coord "GF(2^16)" (PackedClaim.pack HField.packing _) _) = _
  rw [HField.coord_pack]
  simp only [Nat.mod_mod_of_dvd _ (show 16 ∣ 16 from dvd_rfl), show 1600 / 100 = 16 from rfl,
    Nat.div_add_mod]
  exact ofBool_decide_eq (RealizedProgram.stateBit_bool hS j)

/-- **An honest Keccak trace of the batch**: Boolean permutation inputs, every squeeze's input
Keccak-f of the previous permutation's (twenty-four rounds, `iterRounds`). -/
structure HonestTrace (S : Fin 10 → State FH.K) : Prop where
  /-- The inputs are Boolean. -/
  bool : ∀ p x y, AllBool (S p x y)
  /-- Each squeeze starts from the previous permutation's output. -/
  chain : ∀ p : Fin 9, S p.succ = iterRounds (S p.castSucc) 24

/-- **The committed trace words are the packed states of the trace** `S`: round `t` of
permutation `p` holds the words of its output `iterRounds (S p) (t + 1)`, `h2p.shake.state` the
words of the first squeeze's input. -/
structure WordsAgree (val : program.Valuation interp) (S : Fin 10 → State FH.K) : Prop where
  /-- The rounds' words. -/
  rounds : ∀ p t, ∀ i < 100, val (wordsVal p t) i =
    RealizedProgram.castElt (a := 0) (RealizedProgram.stateWords HField.packing (iterRounds (S p) ((t : ℕ) + 1)) i)
  /-- The state's words. -/
  state : ∀ i < 100, val 96 i = RealizedProgram.castElt (a := 0) (RealizedProgram.stateWords HField.packing (S 1) i)

section Rounds

variable {val x : program.Valuation interp} {c : ∀ k, (program.layout interp).Ch k}
  {π : (program.layout interp).Pads} {S : Fin 10 → State FH.K}

/-- **Round `t`'s output reads the trace** at the source environment. -/
theorem stateOf_out (hS : HonestTrace S) (hw : WordsAgree val S) (p : Fin 10) (t : Fin 24) :
    RealizedProgram.stateOf (program.evalE (program.reader (program.srcEnv interp x val c π)) 0
      (.leaf (outVal p t))) = iterRounds (S p) ((t : ℕ) + 1) := by
  obtain ⟨hb, hpw, hfv, hfw, hsv, hsw, hn⟩ := (words_checks (program := program)) p t
  funext x' y' z
  simp only [RealizedProgram.stateOf]
  rw [evalE_words (iterRounds_allBool (hS.bool p) _) hb hpw hfv hfw hsv hsw hn (hw.rounds p t)
    (RealizedProgram.keccakIdx_lt x' y' z), RealizedProgram.stateBit_keccakIdx]

/-- **`h2p.shake.state` reads the first squeeze's input** at the source environment. -/
theorem evalE_state_honest (hS : HonestTrace S) (hw : WordsAgree val S) {j : ℕ} (hj : j < 1600) :
    program.evalE (program.reader (program.srcEnv interp x val c π)) 0 (.leaf 97) j =
      RealizedProgram.stateBit (S 1) j := by
  obtain ⟨hb, hpw, hfv, hfw, hsv, hsw, hn⟩ := (state_checks (program := program))
  exact evalE_words (hS.bool 1) hb hpw hfv hfw hsv hsw hn hw.state hj

/-- **Round `t`'s input reads the trace** at the source environment, where the absorbed block
(`ref 2`) reads the absorb permutation's input. -/
theorem stateOf_src (hS : HonestTrace S) (hw : WordsAgree val S)
    (habs : ∀ j < 1600, program.evalE (program.reader (program.srcEnv interp x val c π)) 0
      (.ref 2) j = RealizedProgram.stateBit (S 0) j) (p : Fin 10) (t : Fin 24) :
    RealizedProgram.stateOf (program.evalE (program.reader (program.srcEnv interp x val c π)) 0
      (roundSrc p t.castSucc).expr) = iterRounds (S p) t := by
  by_cases ht : (t : ℕ) = 0
  · have ht0 : t = 0 := Fin.ext ht
    subst ht0
    rw [show ((0 : Fin 24) : ℕ) = 0 from rfl, show iterRounds (S p) 0 = S p from rfl]
    rcases Nat.lt_or_ge (p : ℕ) 2 with hp | hp
    · interval_cases hpv : (p : ℕ)
      · have hp0 : p = 0 := Fin.ext hpv
        subst hp0
        have h : roundSrc 0 (Fin.castSucc 0) = .ref 2 := by decide
        rw [h]
        funext x' y' z
        simp only [RealizedProgram.stateOf, RealizedProgram.StateSrc.expr]
        rw [habs _ (RealizedProgram.keccakIdx_lt x' y' z), RealizedProgram.stateBit_keccakIdx]
      · have hp1 : p = 1 := Fin.ext hpv
        subst hp1
        have h : roundSrc 1 (Fin.castSucc 0) = .ref 56 := by decide
        rw [h]
        funext x' y' z
        have hj := RealizedProgram.keccakIdx_lt x' y' z
        obtain ⟨-, -, -, -, -, h7, -, -, -, -, -, -, -, -, -, -, hlen⟩ := (squeezeIn_facts (program := program))
        simp only [RealizedProgram.stateOf, RealizedProgram.StateSrc.expr]
        rw [RealizedProgram.evalE_ref (FalconHBase.refsOrdered (program := program)) _ _ hlen, (expr_squeezeIn (program := program)).2.2.2.1, RealizedProgram.evalE_reindex,
          h7 _ hj, evalE_state_honest hS hw hj, RealizedProgram.stateBit_keccakIdx]
    · have h : roundSrc p (Fin.castSucc 0) = .leaf (outVal ((p : ℕ) - 1) 23) := by
        unfold roundSrc
        simp only [Fin.castSucc_zero, Fin.val_zero, ite_true, show (p : ℕ) ≠ 0 by omega,
          show (p : ℕ) ≠ 1 by omega, ite_false]
      rw [h]
      have hc := hS.chain ⟨p - 1, by omega⟩
      have hps : (⟨p - 1, by omega⟩ : Fin 9).succ = p := Fin.ext (by simp; omega)
      rw [hps] at hc
      have := stateOf_out (x := x) (c := c) (π := π) hS hw ⟨p - 1, by omega⟩ 23
      exact this.trans hc.symm
  · have h : roundSrc p t.castSucc = .leaf (outVal p ((t : ℕ) - 1)) := by
      unfold roundSrc
      simp only [Fin.val_castSucc, ht, ite_false]
    rw [h]
    have := stateOf_out (x := x) (c := c) (π := π) hS hw p ⟨t - 1, by omega⟩
    simp only at this
    simp only [RealizedProgram.StateSrc.expr]
    rw [this]
    congr 1
    omega

/-- **The round predicates hold at the source environment** of honest trace words (the converse
of `permRelation`). -/
theorem round_holds (hS : HonestTrace S) (hw : WordsAgree val S)
    (habs : ∀ j < 1600, program.evalE (program.reader (program.srcEnv interp x val c π)) 0
      (.ref 2) j = RealizedProgram.stateBit (S 0) j) (p : Fin 10) (t : Fin 24) :
    program.HoldsWith (program.reader (program.srcEnv interp x val c π))
      (program.predicate (roundPred p t)).body := by
  obtain ⟨hb, hlin, hcol⟩ := (roundShapes (program := program)) p t
  obtain ⟨-, -, hL, hC, -⟩ := (round_facts (program := program)) p t
  have hsize : (program.value (outVal p t)).size ≤ 1600 := (words_checks (program := program) p t).2.2.2.2.1.le
  refine RealizedProgram.holdsWith_of_shapes_at (r := t) (FalconHBase.refsOrdered (program := program))
    (FalconHBase.domainField0 (program := program)) hb hlin hcol hL hC keccakMaps hsize
    (fun j hj => evalE_ones _ hj) (fun j hj => evalE_zeros _ hj) (evalE_rc _ t) ?_
  rw [stateOf_src hS hw habs, stateOf_out hS hw]
  refine (roundRelation_iff (iterRounds_allBool (hS.bool p) _)).2 ?_
  show Keccak.round _ _ = _
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt t.isLt)

end Rounds

/-! ## The buffer and the padding -/

/-- **A checked committed value of domain `H` reads its honest values** at the source
environment. -/
theorem evalE_priv0 {val x : program.Valuation interp} {c : ∀ k, (program.layout interp).Ch k}
    {π : (program.layout interp).Pads} {v : ℕ} (h : program.privCellB v = true)
    (hf : program.valueField v = 0) {z : (interp 0).K} {i : ℕ}
    (hval : val v i = RealizedProgram.castElt (a := 0) z) (hi : i < (program.value v).size) :
    program.evalE (program.reader (program.srcEnv interp x val c π)) 0 (.leaf v) i = z := by
  rw [RealizedProgram.evalE_leaf, RealizedProgram.reader_srcEnv_of_privCellB x val c π h hi, hval]
  exact RealizedProgram.castElt_castElt_of_eq hf.symm _

/-- **The honest buffer and flags**: the nonce (value `45`) and the message part (value `46`)
hold the bits of the padded block `B` (`Shake256.paddedByte`), bytes `0 … 39` and `40 … 135`;
the in-message flags (value `47`) are the prefix of length `40 + L`. -/
structure BufAgree (val : program.Valuation interp) (B : Fin 136 → BitWires FH.K 8)
    (L : ℕ) : Prop where
  /-- The nonce's bits. -/
  nonce : ∀ j (hj : j < 320), val 45 j = RealizedProgram.castElt (a := 0) (B ⟨j / 8, by omega⟩ ⟨j % 8, by omega⟩)
  /-- The message part's bits. -/
  message : ∀ j (hj : j < 768), val 46 j = RealizedProgram.castElt (a := 0) (B ⟨40 + j / 8, by omega⟩ ⟨j % 8, by omega⟩)
  /-- The flags. -/
  flags : ∀ i < 136, val 47 i = RealizedProgram.castElt (a := 0) (if i < 40 + L then 1 else 0)

section Buffer

variable {val x : program.Valuation interp} {c : ∀ k, (program.layout interp).Ch k}
  {π : (program.layout interp).Pads} {B : Fin 136 → BitWires FH.K 8} {L : ℕ}

/-- **The buffer's bits are the block's** at the source environment. -/
theorem bufBit_honest (hb : BufAgree val B L) {j : ℕ} (hj : j < 1088) :
    bufBit (program.srcEnv interp x val c π) j = B ⟨j / 8, by omega⟩ ⟨j % 8, by omega⟩ := by
  obtain ⟨h45, h46, -, hf45, hf46, -⟩ := (buf_checks (program := program))
  obtain ⟨-, -, -, -, -, -, -, -, -, hs45, hs46, -⟩ := (absorb_facts (program := program))
  unfold bufBit
  split_ifs with h
  · exact evalE_priv0 h45 hf45 (hb.nonce j h) (by rw [hs45]; exact h)
  · rw [evalE_priv0 h46 hf46 (hb.message (j - 320) (by omega)) (by rw [hs46]; omega)]
    exact congrArg₂ (fun a b => B a b) (Fin.ext (by simp only; omega)) (Fin.ext (by simp only; omega))

/-- **The flags are the prefix** at the source environment. -/
theorem flag_honest (hb : BufAgree val B L) {i : ℕ} (hi : i < 136) :
    flag (program.srcEnv interp x val c π) i = if i < 40 + L then 1 else 0 :=
  evalE_priv0 (buf_checks (program := program)).2.2.1 (buf_checks (program := program)).2.2.2.2.2 (hb.flags i hi) (by rw [(flag_facts (program := program)).2.1]; exact hi)

/-- **The absorbed block is the block xored into the zero state** at the source environment. -/
theorem evalE_ref2_honest (hb : BufAgree val B L) {j : ℕ} (hj : j < 1600) :
    program.evalE (program.reader (program.srcEnv interp x val c π)) 0 (.ref 2) j =
      RealizedProgram.stateBit (Shake256.xorinBlock Shake256.SpongeSpec.shake256 (fun _ _ _ => 0) B) j := by
  obtain ⟨x', y', z, rfl⟩ := RealizedProgram.exists_keccakIdx hj
  rw [evalE_ref2 _ hj, RealizedProgram.stateBit_keccakIdx]
  unfold Shake256.xorinBlock
  have hrate : Shake256.SpongeSpec.shake256.rate = 136 := rfl
  simp only [hrate]
  split_ifs with h1 h2 h2
  · rw [bufBit_honest (FA := FA) hb h1, bxor_zero_left]
    exact congrArg₂ (fun a b => B a b) (Fin.ext (by simp only [RealizedProgram.keccakIdx]; omega))
      (Fin.ext (by simp only [RealizedProgram.keccakIdx]; omega))
  · exfalso
    unfold RealizedProgram.keccakIdx at h1
    omega
  · exfalso
    unfold RealizedProgram.keccakIdx at h1
    omega
  · rfl

end Buffer

/-! ## The padding predicates -/

section Padding

variable {val x : program.Valuation interp} {c : ∀ k, (program.layout interp).Ch k}
  {π : (program.layout interp).Pads} {B : Fin 136 → BitWires FH.K 8} {L : ℕ}

/-- **`h2p.shake.padding.monotone` holds on the prefix flags.** -/
theorem monotone_honest (hb : BufAgree val B L) :
    program.HoldsWith (program.reader (program.srcEnv interp x val c π))
      (program.predicate 24).body := by
  obtain ⟨-, -, h16, h17, h18, -, -, hs16, -, -, hc27, hf27, he27, -⟩ := (flag_facts (program := program))
  rw [(pred_padding (program := program)).1]
  refine holdsWith_equal0_of fun i hi => ?_
  rw [RealizedProgram.exprLen_mul, RealizedProgram.exprLen_reindex, hs16] at hi
  change program.evalE _ 0 _ i = program.evalE _ 0 (.leaf 27) i
  rw [evalE_const0 _ hc27 hf27, he27 i hi, decodeH_zero, RealizedProgram.evalE_mul,
    RealizedProgram.evalE_add, RealizedProgram.evalE_reindex, RealizedProgram.evalE_reindex, RealizedProgram.evalE_reindex,
    h16 i hi, h17 i hi, h18 i hi, evalE_const0 _ (squeezeIn_facts (program := program)).2.2.2.2.2.2.2.2.1
      (squeezeIn_facts (program := program)).2.2.2.2.2.2.2.2.2.2.1, (squeezeIn_facts (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.1,
    decodeH_one]
  change flag _ (i + 1) * (flag _ i + 1) = 0
  rw [flag_honest hb (by omega), flag_honest hb (by omega)]
  split_ifs with h1 h2
  · exact mul_eq_zero_of_right _ (CharTwo.add_self_eq_zero 1)
  · omega
  · simp
  · simp

/-- **`h2p.shake.padding.max` holds** for a message of at most `32` bytes. -/
theorem max_honest (hb : BufAgree val B L) (hL : L ≤ 32) :
    program.HoldsWith (program.reader (program.srcEnv interp x val c π))
      (program.predicate 25).body := by
  obtain ⟨-, -, -, -, -, h19, -, -, hs19, -, -, -, -, -⟩ := (flag_facts (program := program))
  rw [(pred_padding (program := program)).2.1]
  refine holdsWith_equal0_of fun i hi => ?_
  rw [RealizedProgram.exprLen_reindex, hs19] at hi
  obtain rfl : i = 0 := by omega
  change program.evalE _ 0 _ 0 = program.evalE _ 0 (.leaf 0) 0
  rw [evalE_const0 _ (squeezeIn_facts (program := program)).2.2.2.2.2.2.2.2.2.1 (squeezeIn_facts (program := program)).2.2.2.2.2.2.2.2.2.2.2.1,
    (squeezeIn_facts (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.1, decodeH_zero, RealizedProgram.evalE_reindex, h19]
  change flag _ 72 = 0
  rw [flag_honest hb (by norm_num), if_neg (by omega)]

/-- **`h2p.shake.padding.min` holds**: the nonce's flags are set. -/
theorem min_honest (hb : BufAgree val B L) :
    program.HoldsWith (program.reader (program.srcEnv interp x val c π))
      (program.predicate 26).body := by
  obtain ⟨-, -, -, -, -, -, h20, -, -, hs20, -, -, -, -⟩ := (flag_facts (program := program))
  rw [(pred_padding (program := program)).2.2.1]
  refine holdsWith_equal0_of fun i hi => ?_
  rw [RealizedProgram.exprLen_add, RealizedProgram.exprLen_reindex, hs20] at hi
  obtain rfl : i = 0 := by omega
  change program.evalE _ 0 _ 0 = program.evalE _ 0 (.leaf 0) 0
  rw [evalE_const0 _ (squeezeIn_facts (program := program)).2.2.2.2.2.2.2.2.2.1 (squeezeIn_facts (program := program)).2.2.2.2.2.2.2.2.2.2.2.1,
    (squeezeIn_facts (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.1, decodeH_zero, RealizedProgram.evalE_add,
    RealizedProgram.evalE_reindex, h20, evalE_const0 _ (squeezeIn_facts (program := program)).2.2.2.2.2.2.2.2.1
      (squeezeIn_facts (program := program)).2.2.2.2.2.2.2.2.2.2.1, (squeezeIn_facts (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.1,
    decodeH_one]
  change flag _ 39 + 1 = 0
  rw [flag_honest hb (by norm_num), if_pos (by omega)]
  exact CharTwo.add_self_eq_zero 1

/-- **The packed buffer byte is the block's byte packed** at the source environment. -/
theorem packed_honest (hb : BufAgree val B L) {i : ℕ} (hi : i < 136) :
    (∑ t : Fin 8, bufBit (program.srcEnv interp x val c π) (8 * i + t) * (gH (FH := FH)) ^ (t : ℕ)) =
      ∑ t : Fin 8, B ⟨i, hi⟩ t * (gH (FH := FH)) ^ (t : ℕ) := by
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [bufBit_honest hb (by omega)]
  congr 1
  exact congrArg₂ (fun a b => B a b) (Fin.ext (by simp only; omega)) (Fin.ext (by simp only; omega))

/-- **The padding of the block**: past the input's `40 + L` bytes, byte `i` of the block is
`padConst (40 + L) i` (FIPS 202's `pad10*1` with SHAKE256's suffix). -/
def PadAgree (B : Fin 136 → BitWires FH.K 8) (L : ℕ) : Prop :=
  ∀ i : Fin 136, 40 + L ≤ (i : ℕ) → B i = Shake256.constByte (padConst (40 + L) i)

/-- **`h2p.shake.padding.suffix` holds**: the byte after the input is `0x1F`. -/
theorem suffix_honest (hb : BufAgree val B L) (hL : L ≤ 32) (hp : PadAgree B L) :
    program.HoldsWith (program.reader (program.srcEnv interp x val c π))
      (program.predicate 27).body := by
  obtain ⟨-, -, -, -, -, -, -, h21, -, -, -, -, -, -, -, h30, -, -, hc⟩ := (absorb_facts (program := program))
  have hlen := (squeezeIn_facts (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rw [(pred_padding (program := program)).2.2.2.1]
  refine holdsWith_equal0_of fun i hi => ?_
  rw [RealizedProgram.exprLen_mul, RealizedProgram.exprLen_add, RealizedProgram.exprLen_ref (FalconHBase.refsOrdered (program := program)) (by omega),
    (expr_absorb (program := program)).2.2.2.1, RealizedProgram.exprLen_reindex, h21] at hi
  change program.evalE _ 0 _ i = program.evalE _ 0 (.leaf 30) i
  rw [evalE_const0 _ (hc 30 (by simp)).1 (hc 30 (by simp)).2, h30 i hi, decodeH_zero,
    RealizedProgram.evalE_mul, RealizedProgram.evalE_add, RealizedProgram.evalE_add, evalE_ref51 _ hi, evalE_ref52 _ hi,
    evalE_const0 _ (hc 29 (by simp)).1 (hc 29 (by simp)).2, packed_honest hb hi]
  change ((if i = 0 then 1 else flag _ (i - 1)) + flag _ i) * (_ + constH program 29 i) = 0
  rcases Nat.lt_trichotomy i (40 + L) with h | h | h
  · rw [flag_honest hb hi, if_pos h]
    split_ifs with h0
    · exact mul_eq_zero_of_left (CharTwo.add_self_eq_zero 1) _
    · rw [flag_honest hb (by omega), if_pos (by omega)]
      exact mul_eq_zero_of_left (CharTwo.add_self_eq_zero 1) _
  · refine mul_eq_zero_of_right _ ?_
    rw [const29 (by omega), hp ⟨i, hi⟩ (by simp only; omega)]
    unfold padConst
    rw [if_pos (by simp only; omega)]
    exact CharTwo.add_self_eq_zero _
  · rw [flag_honest hb hi, if_neg (by omega), if_neg (by omega), flag_honest hb (by omega),
      if_neg (by omega), add_zero, zero_mul]

/-- **`h2p.shake.padding.zeros` holds**: past the suffix the block is `0`, `0x80` at the last
byte. -/
theorem zeros_honest (hb : BufAgree val B L) (hp : PadAgree B L) :
    program.HoldsWith (program.reader (program.srcEnv interp x val c π))
      (program.predicate 28).body := by
  obtain ⟨-, -, -, -, -, -, h23, h21, -, -, -, -, -, -, -, h30, -, -, hc⟩ := (absorb_facts (program := program))
  have hlen := (squeezeIn_facts (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rw [(pred_padding (program := program)).2.2.2.2]
  refine holdsWith_equal0_of fun i hi => ?_
  rw [RealizedProgram.exprLen_mul, RealizedProgram.exprLen_add, RealizedProgram.exprLen_ref (FalconHBase.refsOrdered (program := program)) (by omega),
    (expr_absorb (program := program)).2.2.2.1, RealizedProgram.exprLen_reindex, h21] at hi
  change program.evalE _ 0 _ i = program.evalE _ 0 (.leaf 30) i
  rw [evalE_const0 _ (hc 30 (by simp)).1 (hc 30 (by simp)).2, h30 i hi, decodeH_zero,
    RealizedProgram.evalE_mul, RealizedProgram.evalE_add, RealizedProgram.evalE_add, evalE_ref51 _ hi, evalE_ref52 _ hi,
    RealizedProgram.evalE_reindex, RealizedProgram.evalE_mul, RealizedProgram.evalE_reindex, h23 i hi, evalE_selector,
    one_mul, evalE_const0 _ (squeezeIn_facts (program := program)).2.2.2.2.2.2.2.2.1
      (squeezeIn_facts (program := program)).2.2.2.2.2.2.2.2.2.2.1, (squeezeIn_facts (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.1,
    decodeH_one, evalE_const0 _ (hc 31 (by simp)).1 (hc 31 (by simp)).2, packed_honest hb hi]
  change _ * (_ + constH program 31 i) = 0
  by_cases h : i ≤ 40 + L
  · split_ifs with h0
    · exact mul_eq_zero_of_left (CharTwo.add_self_eq_zero 1) _
    · rw [flag_honest hb (by omega), if_pos (by omega)]
      exact mul_eq_zero_of_left (CharTwo.add_self_eq_zero 1) _
  · refine mul_eq_zero_of_right _ ?_
    rw [const31 hi, hp ⟨i, hi⟩ (by simp only; omega)]
    unfold padConst
    rw [if_neg (by simp only; omega)]
    exact CharTwo.add_self_eq_zero _

/-- **`h2p.shake.padding.output` holds**: `h2p.shake.state` holds the absorb permutation's
output. -/
theorem output_honest {S : Fin 10 → State FH.K} (hS : HonestTrace S)
    (hw : WordsAgree val S) :
    program.HoldsWith (program.reader (program.srcEnv interp x val c π))
      (program.predicate 29).body := by
  obtain ⟨-, -, -, -, h27, h7, hsz, -, -, -, -, -, -, -, -, -, hlen⟩ := (squeezeIn_facts (program := program))
  rw [(expr_squeezeIn (program := program)).2.2.2.2]
  refine holdsWith_equal0_of fun j hj => ?_
  rw [RealizedProgram.exprLen_mul, RealizedProgram.exprLen_reindex, hsz] at hj
  change program.evalE _ 0 _ j = program.evalE _ 0 (.leaf 4) j
  rw [evalE_zeros _ hj, RealizedProgram.evalE_mul, RealizedProgram.evalE_reindex, h27 j hj, evalE_selector,
    one_mul, RealizedProgram.evalE_add, RealizedProgram.evalE_reindex, RealizedProgram.evalE_reindex, h7 j hj,
    RealizedProgram.evalE_ref (FalconHBase.refsOrdered (program := program)) _ _ (by omega), (expr_squeezeIn (program := program)).2.2.1, RealizedProgram.evalE_reindex,
    h7 j hj, evalE_state_honest hS hw hj]
  obtain ⟨x', y', z, rfl⟩ := RealizedProgram.exists_keccakIdx hj
  have hout := congrFun (congrFun (congrFun (stateOf_out (x := x) (c := c) (π := π) hS hw 0 23)
    x') y') z
  simp only [RealizedProgram.stateOf] at hout
  rw [show outVal ((0 : Fin 10) : ℕ) ((23 : Fin 24) : ℕ) = 95 from rfl] at hout
  rw [hout, RealizedProgram.stateBit_keccakIdx, show ((23 : Fin 24) : ℕ) + 1 = 24 from rfl]
  have hc := hS.chain 0
  rw [show (0 : Fin 9).succ = 1 from rfl, show (0 : Fin 9).castSucc = 0 from rfl] at hc
  rw [hc]
  exact CharTwo.add_self_eq_zero _

end Padding

/-! ## The SHAKE256 call -/

/-- **The predicates of `h2p.shake`**: the absorb rounds `0 … 23`, the padding `24 … 29`, the
squeeze rounds `30 … 245`. -/
def IsShakePred (q : ℕ) : Prop := q < 246

/-- **The honest SHAKE256 call holds** at the source environment of honest values agreeing with an
honest trace `S` whose absorb input is the block `B` xored into the zero state, `B` padded past the
input's `40 + L ≤ 72` bytes: the `246` predicates of `h2p.shake`. -/
theorem shake_holds {val x : program.Valuation interp} {c : ∀ k, (program.layout interp).Ch k}
    {π : (program.layout interp).Pads} {B : Fin 136 → BitWires FH.K 8} {L : ℕ}
    {S : Fin 10 → State FH.K} (hS : HonestTrace S) (hw : WordsAgree val S)
    (hb : BufAgree val B L) (hL : L ≤ 32) (hp : PadAgree B L)
    (h0 : S 0 = Shake256.xorinBlock Shake256.SpongeSpec.shake256 (fun _ _ _ => 0) B)
    {q : ℕ} (hq : IsShakePred q) :
    program.HoldsWith (program.reader (program.srcEnv interp x val c π))
      (program.predicate q).body := by
  have habs : ∀ j < 1600, program.evalE (program.reader (program.srcEnv interp x val c π)) 0
      (.ref 2) j = RealizedProgram.stateBit (S 0) j := fun j hj => by
    rw [evalE_ref2_honest hb hj, h0]
  unfold IsShakePred at hq
  by_cases h24 : q < 24
  · have := round_holds (x := x) (c := c) (π := π) hS hw habs 0 ⟨q, h24⟩
    exact this
  by_cases h30 : q < 30
  · interval_cases q
    · exact monotone_honest hb
    · exact max_honest hb hL
    · exact min_honest hb
    · exact suffix_honest hb hL hp
    · exact zeros_honest hb hp
    · exact output_honest hS hw
  · have := round_holds (x := x) (c := c) (π := π) hS hw habs ⟨(q - 30) / 24 + 1, by omega⟩
      ⟨(q - 30) % 24, by omega⟩
    have hq' : roundPred ⟨(q - 30) / 24 + 1, by omega⟩ ⟨(q - 30) % 24, by omega⟩ = q := by
      unfold roundPred
      simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
      omega
    rw [hq'] at this
    exact this

/-! ## The honest sponge -/

section Sponge

variable {L : ℕ} (y : Falcon512.PoP.HonestInput L)

/-- **The honest permutation inputs** of SHAKE256 on the honest input's nonce and message
(`KeccakTrace.spongeStart` on `Emulated.honestSeed`), read in `GF(2^128)`. -/
-- spec-side
noncomputable def hStarts (FH : RealizedProgram.FieldInterp) [HField FH] {L : ℕ}
    (y : Falcon512.PoP.HonestInput L) (p : ℕ) : State FH.K :=
  spongeStart .shake256 (Emulated.honestSeed (KH := FH.K) y) p

/-- **The honest absorbed block**: the padded input bytes (`Shake256.paddedByte`). -/
-- spec-side
noncomputable def hBlock (FH : RealizedProgram.FieldInterp) [HField FH] {L : ℕ}
    (y : Falcon512.PoP.HonestInput L) : Fin 136 → BitWires FH.K 8 :=
  Shake256.paddedByte .shake256 (Emulated.honestSeed (KH := FH.K) y) 0

/-- The absorb permutation's input is the block xored into the zero state. -/
theorem hStarts_zero : hStarts FH y 0 =
    Shake256.xorinBlock Shake256.SpongeSpec.shake256 (fun _ _ _ => 0) (hBlock FH y) := rfl

/-- **The honest sponge is an honest trace** for a message of at most `95` bytes (one absorb
block): Boolean, each later input twenty-four rounds of the previous. -/
theorem honestTrace_hStarts (hL : L ≤ 95) : HonestTrace fun p : Fin 10 => hStarts FH y p where
  bool p := spongeStart_allBool
    (Emulated.seed_allBool (HashCircuit.wiresOfByteVec_allBool _) (HashCircuit.wiresOfByteVec_allBool _)) p
  chain p := by
    show spongeStart _ _ ((p : ℕ) + 1) = _
    simp only [spongeStart]
    rw [if_neg (by
      change ¬ ((p : ℕ) + 1 ≤ (40 + L) / 136)
      omega)]
    rfl

/-- **The honest block is padded** past the input's `40 + L` bytes, for `L ≤ 32`. -/
theorem padAgree_hBlock (hL : L ≤ 32) : PadAgree (hBlock FH y) L := by
  intro i hi
  have hab : Shake256.absorbBlocks Shake256.SpongeSpec.shake256 (HashCircuit.falconLen L) = 1 := by
    unfold Shake256.absorbBlocks
    change (40 + L) / 136 + 1 = 1
    omega
  have hlen : HashCircuit.falconLen L = 40 + L := rfl
  unfold hBlock
  refine (Shake256.paddedByte_of_ge (K := FH.K) (sp := .shake256) _ 0 i
    (by change 40 + L ≤ 136 * 0 + (i : ℕ); omega)).trans ?_
  rw [hab]
  have hsuf : Shake256.SpongeSpec.shake256.suffix = 31 := rfl
  have hr : Shake256.SpongeSpec.shake256.rate = 136 := rfl
  have hv : (@Fin.val Shake256.SpongeSpec.shake256.rate i) = (i : ℕ) := rfl
  simp only [hsuf, hr, hv, hlen, Nat.mul_zero, Nat.zero_add, and_true]
  unfold padConst
  funext j
  by_cases heq : (i : ℕ) = 40 + L
  · rw [if_neg (by omega), if_pos heq, if_pos heq]
  · rw [if_neg heq, if_neg heq]
    by_cases h135 : (i : ℕ) = 135
    · rw [if_pos (by omega), if_pos h135]
      change Bits.bxor (Bits.constBit (K := FH.K) 0 j) (Bits.constBit 128 j) =
        Bits.constBit 128 j
      rw [show Bits.constBit (K := FH.K) 0 j = 0 by simp [Bits.constBit], bxor_zero_left]
    · rw [if_neg (by omega), if_neg h135]

end Sponge

/-! ## The honest values of the hash -/

/-- **The round whose committed words are value `v`**, if any. -/
def wordsOwner? (v : ℕ) : Option (Fin 10 × Fin 24) :=
  ((List.finRange 10).flatMap fun p => (List.finRange 24).map fun t => (p, t)).find?
    fun pt => wordsVal pt.1 pt.2 == v

/-- The rounds' words are distinct values, none the nonce, the message part, the flags or the
state's words, decided. -/
theorem wordsOwner_checks : (∀ p t, wordsOwner? (wordsVal p t) = some (p, t)) ∧
    wordsOwner? 45 = none ∧ wordsOwner? 46 = none ∧ wordsOwner? 47 = none ∧
    wordsOwner? 96 = none := by
  decide +kernel

section Values

variable {L : ℕ} (y : Falcon512.PoP.HonestInput L)

/-- **The honest values of the hash's committed inputs** (`h2p.shake`): the nonce and the message
part the bits of the padded block (`hBlock`), the flags the prefix of length `40 + L`, the state's
and the rounds' words the packed states of the honest trace (`hStarts`); `0` elsewhere.

Running time: computing these values takes ten Keccak-f permutations (the trace) and `16`
packing sums per word. This running time is argued here, not proved in Lean. -/
-- spec-side
noncomputable def hashVal (v i : ℕ) : (interp (program.valueField v)).K :=
  if v = 45 then (if h : i < 320 then RealizedProgram.castElt (a := 0) (hBlock FH y ⟨i / 8, by omega⟩ ⟨i % 8, by omega⟩)
    else 0)
  else if v = 46 then
    (if h : i < 768 then RealizedProgram.castElt (a := 0) (hBlock FH y ⟨40 + i / 8, by omega⟩ ⟨i % 8, by omega⟩)
    else 0)
  else if v = 47 then RealizedProgram.castElt (a := 0) (if i < 40 + L then 1 else 0)
  else if v = 96 then RealizedProgram.castElt (a := 0) (RealizedProgram.stateWords HField.packing (hStarts FH y 1) i)
  else match wordsOwner? v with
    | some pt => RealizedProgram.castElt (a := 0)
        (RealizedProgram.stateWords HField.packing (iterRounds (hStarts FH y pt.1) ((pt.2 : ℕ) + 1)) i)
    | none => 0

/-- **Value `v` is a committed input of the hash**: the nonce, the message part, the flags, the
state's or a round's words. -/
def IsHashValue (v : ℕ) : Prop :=
  v = 45 ∨ v = 46 ∨ v = 47 ∨ v = 96 ∨ (wordsOwner? v).isSome

variable {y} {val : program.Valuation interp}

theorem wordsAgree_of_hashVal (h : ∀ v, IsHashValue v → val v = hashVal y v) :
    WordsAgree val fun p : Fin 10 => hStarts FH y p := by
  obtain ⟨hw, h45, h46, h47, h96⟩ := wordsOwner_checks
  refine ⟨fun p t i _ => ?_, fun i _ => ?_⟩
  · have hv : wordsVal p t ≠ 45 ∧ wordsVal p t ≠ 46 ∧ wordsVal p t ≠ 47 ∧ wordsVal p t ≠ 96 := by
      refine ⟨fun h' => ?_, fun h' => ?_, fun h' => ?_, fun h' => ?_⟩ <;>
        · have := hw p t
          rw [h'] at this
          simp_all
    rw [h _ (Or.inr (Or.inr (Or.inr (Or.inr (by rw [hw p t]; rfl)))))]
    unfold hashVal
    rw [if_neg hv.1, if_neg hv.2.1, if_neg hv.2.2.1, if_neg hv.2.2.2, hw p t]
  · rw [h _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]
    rfl

theorem bufAgree_of_hashVal (h : ∀ v, IsHashValue v → val v = hashVal y v) :
    BufAgree val (hBlock FH y) L where
  nonce j hj := by
    rw [h _ (Or.inl rfl)]
    unfold hashVal
    rw [if_pos rfl, dif_pos hj]
  message j hj := by
    rw [h _ (Or.inr (Or.inl rfl))]
    unfold hashVal
    rw [if_neg (by norm_num), if_pos rfl, dif_pos hj]
  flags i _ := by
    rw [h _ (Or.inr (Or.inr (Or.inl rfl)))]
    rfl

/-- **The honest SHAKE256 call holds** at the source environment of honest values agreeing with
`hashVal` on the hash's committed inputs, for a message of at most `32` bytes. -/
theorem shake_holds_honest (hL : L ≤ 32) (h : ∀ v, IsHashValue v → val v = hashVal y v)
    {x : program.Valuation interp} {c : ∀ k, (program.layout interp).Ch k}
    {π : (program.layout interp).Pads} {q : ℕ} (hq : IsShakePred q) :
    program.HoldsWith (program.reader (program.srcEnv interp x val c π))
      (program.predicate q).body :=
  shake_holds (honestTrace_hStarts y (by omega)) (wordsAgree_of_hashVal h)
    (bufAgree_of_hashVal h) hL (padAgree_hBlock y hL) (hStarts_zero y) hq

end Values

/-! ## The stream -/

/-- **The selection's samples are Falcon's candidate stream** of the nonce and message bytes,
where the hash's predicates hold (`HashSat`; `natOfBits_selSample` at the source program). -/
theorem natOfBits_selSample_hash {e : program.Env interp} (hs : HashSat e) (i : Fin falcon512.S) :
    Bits.natOfBits (selSample e i) = Falcon512.streamCandidates falcon512 shake256
      (Emulated.bytesOf (nonceBits (program.reader e))) (messageBytes (program.reader e)) i := by
  calc Bits.natOfBits (selSample e i)
      = Bits.natOfBits (HashCircuit.sampleAt (falconSponge.out e) i) :=
        (natOfBits_selSample0 e i).symm.trans (congrArg Bits.natOfBits (selSample_eq hs i))
    _ = _ := by
      rw [HashCircuit.sampleAt_decode, Falcon512.streamCandidates, ← inputBytes_eq e,
        ← Shake256.SpongeSpec.xof_shake256]
      exact congrFun (congrArg samples16 (funext (squeeze_sound hs))) i

section HonestHashSat

variable {L : ℕ} {y : Falcon512.PoP.HonestInput L} {val : program.Valuation interp}

/-- The honest block's bits are bits. -/
theorem hBlock_bool (i : Fin 136) (j : Fin 8) : hBlock FH y i j = 0 ∨ hBlock FH y i j = 1 :=
  Shake256.paddedByte_allBool (K := FH.K) (sp := Shake256.SpongeSpec.shake256)
    (Emulated.seed_allBool (HashCircuit.wiresOfByteVec_allBool _)
      (HashCircuit.wiresOfByteVec_allBool _)) 0 i j

/-- **The honest values satisfy what the hash's lemmas read** (`HashSat`). -/
theorem hashSat_honest (hL : L ≤ 32) (h : ∀ v, IsHashValue v → val v = hashVal y v)
    {x : program.Valuation interp} {c : ∀ k, (program.layout interp).Ch k}
    {π : (program.layout interp).Pads} : HashSat (program.srcEnv interp x val c π) where
  preds q hq := shake_holds_honest hL h hq
  bits v hv i hi := by
    have hb := bufAgree_of_hashVal h
    obtain ⟨h45, h46, h47, hf45, hf46, hf47⟩ := (buf_checks (program := program))
    obtain ⟨-, -, -, -, -, -, -, -, -, hs45, hs46, -⟩ := (absorb_facts (program := program))
    rcases hv with rfl | rfl | rfl
    · rw [hs45] at hi
      rw [evalE_priv0 h45 hf45 (hb.nonce i hi) (by rw [hs45]; exact hi)]
      exact hBlock_bool _ _
    · rw [hs46] at hi
      rw [evalE_priv0 h46 hf46 (hb.message i hi) (by rw [hs46]; exact hi)]
      exact hBlock_bool _ _
    · rw [(flag_facts (program := program)).2.1] at hi
      rw [evalE_priv0 h47 hf47 (hb.flags i hi) (by rw [(flag_facts (program := program)).2.1]; exact hi)]
      split_ifs
      · exact Or.inr rfl
      · exact Or.inl rfl

end HonestHashSat

/-! ## The honest nonce, message and length -/

section HonestInputs

variable {L : ℕ} {y : Falcon512.PoP.HonestInput L} {val : program.Valuation interp}
  {x : program.Valuation interp} {c : ∀ k, (program.layout interp).Ch k}
  {π : (program.layout interp).Pads}

/-- **The honest block's input bytes** are the seed's. -/
theorem hBlock_lt (hL : L ≤ 32) (i : Fin 136) (hi : (i : ℕ) < 40 + L) :
    hBlock FH y i = Emulated.honestSeed (KH := FH.K) y ⟨i, hi⟩ := by
  unfold hBlock Shake256.paddedByte
  have hv : (@Fin.val Shake256.SpongeSpec.shake256.rate i) = (i : ℕ) := rfl
  have hp : 0 + (@Fin.val Shake256.SpongeSpec.shake256.rate i) < HashCircuit.falconLen L := by
    change 0 + (i : ℕ) < 40 + L
    omega
  simp only [show Shake256.SpongeSpec.shake256.rate = 136 from rfl, Nat.mul_zero]
  rw [if_neg (by rw [hv]; omega)]
  simp only [hp, ↓reduceDIte]
  exact congrArg _ (Fin.ext (Nat.zero_add _))

/-- **The honest nonce bits** are the nonce's bit wires. -/
theorem nonceBits_honest (hL : L ≤ 32) (h : ∀ v, IsHashValue v → val v = hashVal y v) :
    nonceBits (program.reader (program.srcEnv interp x val c π)) =
      HashCircuit.wiresOfByteVec (K := FH.K) y.nonce := by
  funext k
  have hk := k.isLt
  have hk' : (k : ℕ) < 320 := by
    have : 8 * falcon512.saltBytes = 320 := rfl
    omega
  unfold nonceBits
  rw [evalE_priv0 (buf_checks (program := program)).1 (buf_checks (program := program)).2.2.2.1 ((bufAgree_of_hashVal h).nonce k hk')
    (by rw [(absorb_facts (program := program)).2.2.2.2.2.2.2.2.2.1]; exact hk'), hBlock_lt hL _ (by simp only; omega)]
  unfold Emulated.honestSeed Emulated.seed
  have hc : (⟨(k : ℕ) / 8, by
        change (k : ℕ) / 8 < 40 + L
        omega⟩ : Fin (HashCircuit.falconLen L)) =
      Fin.castAdd L (⟨(k : ℕ) / 8, by
        have : falcon512.saltBytes = 40 := rfl
        omega⟩ : Fin falcon512.saltBytes) :=
    rfl
  rw [hc, Fin.append_left]
  simp only [HashCircuit.byteWires, HashCircuit.wiresOfByteVec]
  have h1 : (8 * ((k : ℕ) / 8) + (k : ℕ) % 8) = k := Nat.div_add_mod _ _
  exact congrArg₂ (fun a b => Bits.constBit (y.nonce a) b) (Fin.ext (by simp only [h1]))
    (by simp only [h1])

/-- **The honest message part's input bits** are the message's bit wires. -/
theorem messageBit_honest (hL : L ≤ 32) (h : ∀ v, IsHashValue v → val v = hashVal y v)
    {k : ℕ} (hk : k < 8 * L) :
    program.evalE (program.reader (program.srcEnv interp x val c π)) 0 (.leaf 46) k =
      HashCircuit.wiresOfByteVec (K := FH.K) y.message ⟨k, hk⟩ := by
  have hk' : k < 768 := by omega
  rw [evalE_priv0 (buf_checks (program := program)).2.1 (buf_checks (program := program)).2.2.2.2.1 ((bufAgree_of_hashVal h).message k hk')
    (by rw [(absorb_facts (program := program)).2.2.2.2.2.2.2.2.2.2.1]; exact hk'), hBlock_lt hL _ (by simp only; omega)]
  unfold Emulated.honestSeed Emulated.seed
  have hc : (⟨40 + k / 8, by
        change 40 + k / 8 < 40 + L
        omega⟩ : Fin (HashCircuit.falconLen L)) =
      Fin.natAdd falcon512.saltBytes (⟨k / 8, by omega⟩ : Fin L) := rfl
  rw [hc, Fin.append_right]
  simp only [HashCircuit.byteWires, HashCircuit.wiresOfByteVec]
  have h1 : (8 * (k / 8) + k % 8) = k := Nat.div_add_mod _ _
  exact congrArg₂ (fun a b => Bits.constBit (y.message a) b) (Fin.ext (by simp only [h1]))
    (by simp only [h1])

/-- **The honest length** read off the flags is `L`. -/
theorem lenOf_honest (hL : L ≤ 32) (h : ∀ v, IsHashValue v → val v = hashVal y v) :
    lenOf (program.reader (program.srcEnv interp x val c π)) = L := by
  have hs := hashSat_honest (x := x) (c := c) (π := π) hL h
  have hf : ∀ i < 136, flag (program.srcEnv interp x val c π) i = if i < 40 + L then 1 else 0 :=
    fun i hi => flag_honest (bufAgree_of_hashVal h) hi
  have hle := lenOf_le (program.reader (program.srcEnv interp x val c π))
  have h10 : (1 : (interp 0).K) ≠ 0 := one_ne_zero
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have := (flag_iff hs (i := 40 + lenOf (program.reader (program.srcEnv interp x val c π)))
      (by omega)).1 (by rw [hf _ (by omega), if_pos (by omega)])
    omega
  · have := (flag_iff hs (i := 40 + L) (by omega)).2 (by omega)
    rw [hf _ (by omega), if_neg (by omega)] at this
    exact h10 this.symm

/-- **The honest input bytes**: the nonce's and the message's. -/
theorem bytes_honest (hL : L ≤ 32) (hy : y.Valid) (h : ∀ v, IsHashValue v → val v = hashVal y v) :
    Emulated.bytesOf (nonceBits (program.reader (program.srcEnv interp x val c π))) =
        List.ofFn y.nonce ∧
      messageBytes (program.reader (program.srcEnv interp x val c π)) = List.ofFn y.message := by
  refine ⟨by rw [nonceBits_honest hL h]; exact Emulated.bytesOf_wiresOfByteVec (KH := FH.K) hy.nonce_bytes, ?_⟩
  have hl := lenOf_honest (x := x) (c := c) (π := π) hL h
  unfold messageBytes
  revert hl
  generalize lenOf (program.reader (program.srcEnv interp x val c π)) = m
  intro hl
  subst hl
  have : messageBits (program.reader (program.srcEnv interp x val c π)) m =
      HashCircuit.wiresOfByteVec (K := FH.K) y.message := by
    funext k
    exact messageBit_honest hL h k.isLt
  rw [this]
  exact Emulated.bytesOf_wiresOfByteVec (KH := FH.K) hy.message_bytes

end HonestInputs

end GordieHowe.Falcon512.Native.ROMParams
