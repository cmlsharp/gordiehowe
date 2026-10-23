-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Honest.Source
public import GordieHowe.Applications.MLDSA44.Native.ROMParams.Frontend.Hash

@[expose] public section

/-!
# GordieHowe: the honest SHAKE256 calls of an ML-DSA program's domain `H`

The converse of the frontend's hash view (`GordieHowe/Applications/MLDSA44/Native/ROMParams/Frontend/Hash.lean`) for a native ML-DSA program
(`MldsaHHash`): at an environment reading honest committed values (`GordieHowe.RealizedProgram.ReadsCells`, such as the
source environment) whose trace words are the packed states of an honest Keccak trace
(`WordsAgree`), the `240` round predicates hold (`round_holds`, `GordieHowe.RealizedProgram.holdsWith_of_shapes` on the
round relations of the trace, `KeccakTrace.roundRelation_iff`), given the permutations' inputs.

The program facts beyond the frontend's (`MldsaHHonest`: each round's output is the bit view of its
committed words) are decided per program.
-/

namespace GordieHowe.MLDSA44.Native.ROMParams

open Generated.MLDSA44.Native.ROMParams.Program
open GordieHowe.Bits GordieHowe.Keccak GordieHowe.KeccakTrace

/-- **The committed words of round `t` of permutation `p`**: the value its output view reads. -/
def wordsVal (p : Fin 10) (t : Fin 24) : ℕ := outVal p t - 1

/-- **The program facts of the honest hash** (`MldsaHHash` and): each round's output is the bit
view `idx1` of its committed words, `100` words of `GF(2^16)` in domain `H`'s field. Each program
instantiates it by `decide`. -/
class MldsaHHonest (program : RealizedProgram) : Prop extends MldsaHHash program where
  /-- The rounds' outputs are bit views of their committed words. -/
  words_checks : ∀ p : Fin 10, ∀ t : Fin 24,
    program.isBitsB (outVal p t) (wordsVal p t) idx1 = true ∧
      program.privCellB (wordsVal p t) = true ∧ program.valueField (outVal p t) = 1 ∧
      program.valueField (wordsVal p t) = 1 ∧ (program.value (outVal p t)).size = 1600 ∧
      (program.value (wordsVal p t)).size = 100 ∧
      (program.value (wordsVal p t)).type.nodeName = some "GF(2^16)"
  /-- The word view reads word `i` at entry `i`. -/
  idx1_entry : RealizedProgram.IndexMap.size idx1 = 100 ∧ ∀ i < 100, idx1.entry i = i
  /-- `h2c.mu.out` is the bit view `idx2` of its `32` committed words. -/
  view121 : program.isBitsB 121 120 idx2 = true ∧ program.privCellB 120 = true ∧
    program.valueField 121 = 1 ∧ program.valueField 120 = 1 ∧ (program.value 121).size = 512 ∧
    (program.value 120).size = 32 ∧ (program.value 120).type.nodeName = some "GF(2^16)" ∧
    RealizedProgram.IndexMap.size idx2 = 32 ∧ ∀ i < 32, idx2.entry i = i
  /-- `w1` is the bit view `idx0` of its `384` committed words. -/
  view71 : program.isBitsB 71 70 idx0 = true ∧ program.privCellB 70 = true ∧
    program.valueField 71 = 1 ∧ program.valueField 70 = 1 ∧ (program.value 71).size = 6144 ∧
    (program.value 70).size = 384 ∧ (program.value 70).type.nodeName = some "GF(2^16)" ∧
    RealizedProgram.IndexMap.size idx0 = 384 ∧ ∀ i < 384, idx0.entry i = i
  /-- The message buffer and its flags are committed cells of domain `H`. -/
  priv6869 : program.privCellB 68 = true ∧ program.valueField 68 = 1 ∧
    program.privCellB 69 = true ∧ program.valueField 69 = 1
  /-- `tr` is the statement's opaque value. -/
  kind67 : (program.value 67).kind = .pub (.opaque "tr" [])

set_option maxRecDepth 4096 in
/-- The program of `MLDSA44.Native.ROMParams` has these facts. -/
instance : MldsaHHonest program where
  words_checks := by decide +kernel
  idx1_entry := by decide +kernel
  view121 := by decide +kernel
  view71 := by decide +kernel
  priv6869 := by decide +kernel
  kind67 := rfl

set_option linter.unusedSectionVars false

variable {program : RealizedProgram} [MldsaHHonest program] {F0 FH : RealizedProgram.FieldInterp} [HField FH]
  [MldsaHConstsSelect program FH]

set_option hygiene false in
local notation "interp" => RealizedProgram.mldsaInterpOf F0 FH

/-- **A bit read from a Boolean field element**: `ofBool (x = 1)` is `x`. -/
theorem ofBool_decide_eqH {x : FH.K} (hx : x = 0 ∨ x = 1) :
    FH.ofBool (decide (x = 1)) = x := by
  rcases hx with rfl | rfl <;> simp [RealizedProgram.FieldInterp.ofBool]

/-- A bit read in an equal field identifier is the bit there. -/
theorem castElt_ofBoolH {a b : ℕ} (h : a = b) (c : Bool) :
    (RealizedProgram.castElt ((interp a).ofBool c) : (interp b).K) = (interp b).ofBool c := by
  subst h
  exact RealizedProgram.castElt_self _

/-- **A coordinate of an element of domain `H`'s field cast into a field identifier equal to
`1`.** -/
theorem coord_castEltH {a : ℕ} (h : a = 1) (s : String) (y : (interp 1).K) (j : ℕ) :
    (interp a).coord s (RealizedProgram.castElt (a := 1) (b := a) y) j = FH.coord s y j := by
  subst h
  rw [RealizedProgram.castElt_self]
  rfl

/-- **A bit view of packed state words reads the state's bits** at an environment reading the
words. -/
theorem evalE_words {e : program.Env interp} {val : program.Valuation interp}
    (hr : program.ReadsCells 1 e val) {v w : ℕ}
    {S : State FH.K} (hS : ∀ x y, AllBool (S x y))
    (hb : program.isBitsB v w idx1 = true) (hw : program.privCellB w = true)
    (hfv : program.valueField v = 1) (hfw : program.valueField w = 1)
    (hsv : (program.value v).size = 1600) (hsw : (program.value w).size = 100)
    (hn : (program.value w).type.nodeName = some "GF(2^16)")
    (hval : ∀ i < 100, val w i = RealizedProgram.castElt (a := 1) (RealizedProgram.stateWords HField.packing S i))
    {j : ℕ} (hj : j < 1600) :
    program.evalE (program.reader e) 1 (.leaf v) j =
      RealizedProgram.stateBit S j := by
  obtain ⟨hsel, he⟩ := MldsaHHonest.idx1_entry (program := program)
  have hq : j / (1600 / 100) < 100 := by omega
  rw [RealizedProgram.evalE_leaf, hr.reader_bits hb hw hfw (by
    rw [hsv, hsel, he _ hq, hsw]; exact hq), hsv, hsel, he _ hq, hval _ hq, hn]
  rw [castElt_ofBoolH hfv, coord_castEltH hfw]
  change FH.ofBool (FH.coord "GF(2^16)" (PackedClaim.pack HField.packing _) _) = _
  rw [HField.coord_pack]
  simp only [Nat.mod_mod_of_dvd _ (show 16 ∣ 16 from dvd_rfl), show 1600 / 100 = 16 from rfl,
    Nat.div_add_mod]
  exact ofBool_decide_eqH (RealizedProgram.stateBit_bool hS j)

/-- **A bit view of packed words reads the packed bits**: value `v` the bit view `sel` (the
identity on `n` words) of the committed words `w` of `GF(2^16)`, word `i` the packing of bits
`16 i … 16 i + 15` of `f`, reads bit `j` of `f` below `16 n`, where `f` is bits. -/
theorem evalE_bitview {e : program.Env interp} {val : program.Valuation interp}
    (hr : program.ReadsCells 1 e val) {v w n : ℕ}
    {sel : RealizedProgram.IndexMap} {f : ℕ → FH.K} (hf : ∀ j, f j = 0 ∨ f j = 1)
    (hb : program.isBitsB v w sel = true) (hw : program.privCellB w = true)
    (hfv : program.valueField v = 1) (hfw : program.valueField w = 1)
    (hsv : (program.value v).size = 16 * n) (hsw : (program.value w).size = n)
    (hn : (program.value w).type.nodeName = some "GF(2^16)") (hsel : sel.size = n)
    (he : ∀ i < n, sel.entry i = i)
    (hval : ∀ i < n, val w i = RealizedProgram.castElt (a := 1)
      (PackedClaim.pack HField.packing fun b => decide (f (16 * i + b) = 1)))
    {j : ℕ} (hj : j < 16 * n) :
    program.evalE (program.reader e) 1 (.leaf v) j = f j := by
  have hn0 : 0 < n := by omega
  have hdiv : 16 * n / n = 16 := by rw [Nat.mul_div_cancel _ hn0]
  have hq : j / 16 < n := by omega
  rw [RealizedProgram.evalE_leaf, hr.reader_bits hb hw hfw (by
    rw [hsv, hsel, hdiv, he _ hq, hsw]; exact hq), hsv, hsel, hdiv, he _ hq, hval _ hq, hn]
  rw [castElt_ofBoolH hfv, coord_castEltH hfw]
  change FH.ofBool (FH.coord "GF(2^16)" (PackedClaim.pack HField.packing _) _) = _
  rw [HField.coord_pack]
  simp only [Nat.mod_mod_of_dvd _ (show 16 ∣ 16 from dvd_rfl), Nat.div_add_mod]
  exact ofBool_decide_eqH (hf j)

/-- **An honest Keccak trace of domain `H`**: the ten permutations' Boolean inputs. -/
structure HonestTrace (S : Fin 10 → State FH.K) : Prop where
  /-- The inputs are Boolean. -/
  bool : ∀ p x y, AllBool (S p x y)

/-- **The committed trace words are the packed states of the trace** `S`: round `t` of
permutation `p` holds the words of its output `iterRounds (S p) (t + 1)`. -/
structure WordsAgree (val : program.Valuation interp) (S : Fin 10 → State FH.K) : Prop where
  /-- The rounds' words. -/
  rounds : ∀ p t, ∀ i < 100, val (wordsVal p t) i =
    RealizedProgram.castElt (a := 1) (RealizedProgram.stateWords HField.packing (iterRounds (S p) ((t : ℕ) + 1)) i)

section Rounds

variable {e : program.Env interp} {val : program.Valuation interp}
  (hr : program.ReadsCells 1 e val) {S : Fin 10 → State FH.K}

include hr

/-- **Round `t`'s output reads the trace** at an environment reading the trace words. -/
theorem stateOf_out (hS : HonestTrace S) (hw : WordsAgree val S) (p : Fin 10) (t : Fin 24) :
    RealizedProgram.stateOf (program.evalE (program.reader e) 1
      (.leaf (outVal p t))) = iterRounds (S p) ((t : ℕ) + 1) := by
  obtain ⟨hb, hpw, hfv, hfw, hsv, hsw, hn⟩ := MldsaHHonest.words_checks (program := program) p t
  funext x' y' z
  simp only [RealizedProgram.stateOf]
  rw [evalE_words hr (iterRounds_allBool (hS.bool p) _) hb hpw hfv hfw hsv hsw hn (hw.rounds p t)
    (RealizedProgram.keccakIdx_lt x' y' z), RealizedProgram.stateBit_keccakIdx]

/-- **Round `t`'s input reads the trace** at an environment reading the trace words, given the
permutation's input. -/
theorem stateOf_src (hS : HonestTrace S) (hw : WordsAgree val S) (p : Fin 10)
    (hin : RealizedProgram.stateOf (program.evalE (program.reader e) 1
      (.ref (linRef p 0 - 2))) = S p) (t : Fin 24) :
    RealizedProgram.stateOf (program.evalE (program.reader e) 1
      (roundSrc p t.castSucc).expr) = iterRounds (S p) t := by
  by_cases ht : (t : ℕ) = 0
  · have h : roundSrc p t.castSucc = .ref (linRef p 0 - 2) := by
      unfold roundSrc
      simp [ht]
    rw [h, ht]
    exact hin
  · have h : roundSrc p t.castSucc = .leaf (outVal p ((t : ℕ) - 1)) := by
      unfold roundSrc
      simp only [Fin.val_castSucc, ht, ite_false]
    rw [h]
    have := stateOf_out hr hS hw p ⟨t - 1, by omega⟩
    simp only at this
    simp only [RealizedProgram.StateSrc.expr]
    rw [this]
    congr 1
    omega

/-- **The round predicates hold at an environment reading honest trace words** (the converse
of `permRelation`), given the permutation's input. -/
theorem round_holds (hS : HonestTrace S) (hw : WordsAgree val S) (p : Fin 10)
    (hin : RealizedProgram.stateOf (program.evalE (program.reader e) 1
      (.ref (linRef p 0 - 2))) = S p) (t : Fin 24) :
    program.HoldsWith (program.reader e)
      (program.predicate (roundPred p t)).body := by
  obtain ⟨hb, hlin, hcol⟩ := (roundShapes (program := program)) p t
  obtain ⟨-, -, hL, hC, -⟩ := (round_facts (program := program)) p t
  have hsize : (program.value (outVal p t)).size ≤ 1600 :=
    (MldsaHHonest.words_checks (program := program) p t).2.2.2.2.1.le
  have key : ∀ D, program.domainField 1 = D →
      (∀ j < 1600, program.evalE (program.reader e) D
        (.leaf 11) j = 1) →
      (∀ j < 1600, program.evalE (program.reader e) D
        (.leaf 13) j = 0) →
      (∀ x' y' z', program.evalE (program.reader e) D
        (.leaf (rcLeaf t)) (RealizedProgram.keccakIdx x' y' z') = iotaVec t (x', y', z')) →
      RoundRelation t (RealizedProgram.stateOf (program.evalE (program.reader e)
        D (roundSrc p t.castSucc).expr))
        (RealizedProgram.stateOf (program.evalE (program.reader e) D
          (.leaf (outVal p t)))) →
      program.HoldsWith (program.reader e)
        (program.predicate (roundPred p t)).body := by
    intro D hD hones hzeros hrc hrel
    subst hD
    exact @RealizedProgram.holdsWith_of_shapes program interp MldsaHCross.refsOrdered _ _ _ _ _ t
      charP_domainH hb hlin hcol hL hC keccakMaps hsize hones hzeros hrc hrel
  refine key 1 MldsaHCross.domainField1 (fun j hj => evalE_ones _ hj)
    (fun j hj => evalE_zeros _ hj) (evalE_rc _ t) ?_
  rw [stateOf_src hr hS hw p hin, stateOf_out hr hS hw]
  refine (roundRelation_iff (iterRounds_allBool (hS.bool p) _)).2 ?_
  show Keccak.round _ _ = _
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt t.isLt)

end Rounds

/-! ## The honest trace of the three calls -/

/-- **The honest inputs of domain `H`'s hash**, as bit readings: `tr` (`512` bits, value `67`),
`μ`'s buffer past `tr ‖ 0x00 ‖ 0x00` (`560` bits, value `68`), `μ` (`512` bits, value `121`) and
`w1` (`6144` bits, value `71`). -/
structure HashData (K : Type*) where
  /-- The bits of `tr`. -/
  tr : ℕ → K
  /-- The bits of `μ`'s buffer past `tr ‖ 0x00 ‖ 0x00`. -/
  buf : ℕ → K
  /-- The bits of `μ`. -/
  mu : ℕ → K
  /-- The bits of `w1`. -/
  w1 : ℕ → K

namespace HashData

variable {K : Type*} [Field K] [DecidableEq K] (D : HashData K)

/-- **`c̃'`'s padded input** bit `j`: `μ`, `w1`, then the padding `0x1F … 0x80` (`ref 66`). -/
def ctIn (j : ℕ) : K :=
  if j < 512 then D.mu j else if j < 6656 then D.w1 (j - 512)
  else if j - 6656 < 5 ∨ j - 6656 = 959 then 1 else 0

/-- **`μ`'s absorbed state**: the buffer `tr ‖ 0x00 ‖ 0x00 ‖ buf`, then the capacity's zeros. -/
def muState : State K :=
  RealizedProgram.stateOf fun j => if j < 1088 then (if j < 512 then D.tr j else if j < 528 then 0
    else D.buf (j - 528)) else 0

/-- **`c̃'`'s absorbed states**: block `0` of the padded input, then each permutation's output plus
the next block. -/
def ctState : ℕ → State K
  | 0 => RealizedProgram.stateOf fun j => if j < 1088 then D.ctIn j else 0
  | k + 1 => RealizedProgram.stateOf fun j => RealizedProgram.stateBit (iterRounds (ctState k) 24) j +
      if j < 1088 then D.ctIn (1088 * (k + 1) + j) else 0

/-- **The stream's absorbed state**: `c̃'`'s `256` output bits, the padding, then zeros. -/
def sbState : State K :=
  RealizedProgram.stateOf fun j => if j < 1088 then (if j < 256 then RealizedProgram.stateBit (iterRounds (D.ctState 6) 24) j
    else if j - 256 < 5 ∨ j - 256 = 831 then 1 else 0) else 0

/-- **The ten permutations' inputs**: `μ`'s, `c̃'`'s seven, the stream's absorb and squeeze. -/
def states (p : Fin 10) : State K :=
  if (p : ℕ) = 0 then D.muState else if (p : ℕ) ≤ 7 then D.ctState ((p : ℕ) - 1)
  else if (p : ℕ) = 8 then D.sbState else iterRounds D.sbState 24

/-- **The data are bits.** -/
structure Bool : Prop where
  tr : ∀ j, D.tr j = 0 ∨ D.tr j = 1
  buf : ∀ j, D.buf j = 0 ∨ D.buf j = 1
  mu : ∀ j, D.mu j = 0 ∨ D.mu j = 1
  w1 : ∀ j, D.w1 j = 0 ∨ D.w1 j = 1

variable {D}

theorem stateOf_bool {f : ℕ → K} (h : ∀ j, f j = 0 ∨ f j = 1) : ∀ x y, AllBool (RealizedProgram.stateOf f x y) :=
  fun _ _ _ => h _

theorem ctIn_bool (hD : D.Bool) (j : ℕ) : D.ctIn j = 0 ∨ D.ctIn j = 1 := by
  unfold ctIn
  split_ifs
  · exact hD.mu j
  · exact hD.w1 _
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem add_bool [CharP K 2] {a b : K} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    a + b = 0 ∨ a + b = 1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [CharTwo.add_self_eq_zero]

theorem ctState_bool [CharP K 2] (hD : D.Bool) : ∀ k x y, AllBool (D.ctState k x y)
  | 0 => stateOf_bool fun j => by
      split_ifs
      · exact ctIn_bool hD j
      · exact Or.inl rfl
  | k + 1 => stateOf_bool fun j => add_bool
      (RealizedProgram.stateBit_bool (iterRounds_allBool (ctState_bool hD k) 24) j) (by
        split_ifs
        · exact ctIn_bool hD _
        · exact Or.inl rfl)

theorem states_bool [CharP K 2] (hD : D.Bool) : ∀ p x y, AllBool (D.states p x y) := by
  intro p
  unfold states
  split_ifs
  · exact stateOf_bool fun j => by
      split_ifs
      · exact hD.tr j
      · exact Or.inl rfl
      · exact hD.buf _
      · exact Or.inl rfl
  · exact ctState_bool hD _
  · exact stateOf_bool fun j => by
      split_ifs
      · exact RealizedProgram.stateBit_bool (iterRounds_allBool (ctState_bool hD 6) 24) j
      · exact Or.inr rfl
      · exact Or.inl rfl
      · exact Or.inl rfl
  · exact iterRounds_allBool (stateOf_bool fun j => by
      split_ifs
      · exact RealizedProgram.stateBit_bool (iterRounds_allBool (ctState_bool hD 6) 24) j
      · exact Or.inr rfl
      · exact Or.inl rfl
      · exact Or.inl rfl) 24

end HashData

/-- **The readings of the hash inputs** `D`: `tr`, the buffer, `μ` and `w1`. -/
structure InputsAgree (rd : program.Valuation interp) (D : HashData FH.K) : Prop where
  tr : ∀ j < 512, program.evalE rd 1 (.leaf 67) j = D.tr j
  buf : ∀ j < 560, program.evalE rd 1 (.leaf 68) j = D.buf j
  mu : ∀ j < 512, program.evalE rd 1 (.leaf 121) j = D.mu j
  w1 : ∀ j < 6144, program.evalE rd 1 (.leaf 71) j = D.w1 j

section Inputs

variable {e : program.Env interp} {val : program.Valuation interp} {D : HashData FH.K}

set_option hygiene false in
local notation "RD" => program.reader e

/-- **Round `t`'s output reads the trace**, coordinatewise. -/
theorem evalE_out (hr : program.ReadsCells 1 e val) (hD : D.Bool) (hw : WordsAgree val D.states)
    (p : Fin 10) (t : Fin 24) {j : ℕ} (hj : j < 1600) :
    program.evalE RD 1 (.leaf (outVal p t)) j = RealizedProgram.stateBit (iterRounds (D.states p) ((t : ℕ) + 1)) j := by
  obtain ⟨hb, hpw, hfv, hfw, hsv, hsw, hn⟩ := MldsaHHonest.words_checks (program := program) p t
  exact evalE_words hr (iterRounds_allBool (D.states_bool hD p) _) hb hpw hfv hfw hsv hsw hn
    (hw.rounds p t) hj

/-- **`c̃'`'s padded input** (`ref 66`) reads `ctIn`. -/
theorem evalE_ref66_honest (ha : InputsAgree RD D) {j : ℕ} (hj : j < 7616) :
    program.evalE RD 1 (.ref 66) j = D.ctIn j := by
  rw [evalE_ref66 _ hj]
  unfold HashData.ctIn
  split_ifs with h1 h2
  · exact ha.mu j h1
  · exact ha.w1 _ (by omega)
  · rfl
  · rfl

/-- **Every permutation's input reads the trace** at an environment reading the trace words. -/
theorem stateOf_in (hr : program.ReadsCells 1 e val) (hD : D.Bool) (ha : InputsAgree RD D)
    (hw : WordsAgree val D.states) (p : Fin 10) :
    RealizedProgram.stateOf (program.evalE RD 1 (.ref (linRef p 0 - 2))) = D.states p := by
  have hp := p.isLt
  rcases Nat.lt_or_ge (p : ℕ) 1 with h0 | h1
  · have hp0 : p = 0 := Fin.ext (by omega)
    subst hp0
    simp only [HashData.states, Fin.val_zero, ite_true, HashData.muState]
    refine stateOf_congr fun j hj => ?_
    rw [show linRef 0 0 - 2 = 12 from rfl, evalE_ref12 _ hj]
    split_ifs with h1 h2 h3
    · rw [evalE_ref11 _ h1, if_pos h2]
      exact ha.tr j h2
    · rw [evalE_ref11 _ h1, if_neg h2, if_pos h3]
    · rw [evalE_ref11 _ h1, if_neg h2, if_neg h3]
      exact ha.buf _ (by omega)
    · rfl
  rcases Nat.lt_or_ge (p : ℕ) 2 with h2 | h2
  · have hp1 : p = 1 := Fin.ext (by omega)
    subst hp1
    simp only [HashData.states, show ((1 : Fin 10) : ℕ) = 1 from rfl]
    simp only [show (1 : ℕ) ≠ 0 by omega, ite_false, show (1 : ℕ) ≤ 7 by omega, ite_true]
    unfold HashData.ctState
    refine stateOf_congr fun j hj => ?_
    rw [show linRef 1 0 - 2 = 67 from rfl, evalE_ref67 _ hj]
    split_ifs with h
    · exact evalE_ref66_honest ha (by omega)
    · rfl
  rcases Nat.lt_or_ge (p : ℕ) 8 with h8 | h8
  · have hs : D.states p = D.ctState ((p : ℕ) - 1) := by
      simp only [HashData.states, show (p : ℕ) ≠ 0 by omega, ite_false, show (p : ℕ) ≤ 7 by omega,
        ite_true]
    have hs' : D.states ⟨(p : ℕ) - 1, by omega⟩ = D.ctState ((p : ℕ) - 1 - 1) := by
      simp only [HashData.states, show (p : ℕ) - 1 ≠ 0 by omega, ite_false,
        show (p : ℕ) - 1 ≤ 7 by omega, ite_true]
    rw [hs, show (p : ℕ) - 1 = ((p : ℕ) - 1 - 1) + 1 by omega]
    simp only [HashData.ctState]
    refine stateOf_congr fun j hj => ?_
    rw [evalE_blk _ h2 (by omega) hj]
    have ho : outVal ((p : ℕ) - 1) 23 = outVal (⟨(p : ℕ) - 1, by omega⟩ : Fin 10) (23 : Fin 24) :=
      rfl
    rw [ho, evalE_out hr hD hw _ _ hj, hs']
    congr 1
    split_ifs with h
    · rw [evalE_ref66_honest ha (by omega)]
      congr 1
      omega
    · rfl
  rcases Nat.lt_or_ge (p : ℕ) 9 with h9 | h9
  · have hp8 : p = 8 := Fin.ext (by omega)
    subst hp8
    simp only [HashData.states, show ((8 : Fin 10) : ℕ) = 8 from rfl]
    simp only [show (8 : ℕ) ≠ 0 by omega, ite_false, show ¬ (8 : ℕ) ≤ 7 by omega, ite_true,
      HashData.sbState]
    refine stateOf_congr fun j hj => ?_
    rw [show linRef 8 0 - 2 = 410 from rfl, evalE_ref410 _ hj]
    split_ifs with h1 h2
    · rw [evalE_458 _ h2, show (457 : ℕ) = outVal (7 : Fin 10) (23 : Fin 24) from rfl,
        evalE_out hr hD hw _ _ hj]
      simp only [HashData.states, show ((7 : Fin 10) : ℕ) = 7 from rfl]
      rfl
    · rfl
    · rfl
    · rfl
  · have hp9 : p = 9 := Fin.ext (by omega)
    subst hp9
    have hst : D.states 9 = iterRounds D.sbState 24 := by
      simp only [HashData.states, show ((9 : Fin 10) : ℕ) = 9 from rfl]
      simp
    rw [hst]
    funext x' y' z
    simp only [RealizedProgram.stateOf]
    rw [show linRef 9 0 - 2 = 459 from rfl, evalE_ref459 _ (RealizedProgram.keccakIdx_lt x' y' z),
      show (506 : ℕ) = outVal (8 : Fin 10) (23 : Fin 24) from rfl,
      evalE_out hr hD hw _ _ (RealizedProgram.keccakIdx_lt x' y' z), RealizedProgram.stateBit_keccakIdx]
    simp only [HashData.states, show ((8 : Fin 10) : ℕ) = 8 from rfl]
    simp

/-- **Every round predicate holds at an environment reading honest trace words and inputs.** -/
theorem trace_holds (hr : program.ReadsCells 1 e val) (hD : D.Bool) (ha : InputsAgree RD D)
    (hw : WordsAgree val D.states) (p : Fin 10) (t : Fin 24) :
    program.HoldsWith RD (program.predicate (roundPred p t)).body :=
  round_holds hr ⟨D.states_bool hD⟩ hw p (stateOf_in hr hD ha hw p) t

/-- **An environment reading honest committed values reads the hash inputs**: `tr` from the
statement, the buffer from value `68`, `μ` and `w1` packed in their words (`120`, `70`). -/
theorem inputsAgree_of (hr : program.ReadsCells 1 e val) (hD : D.Bool)
    (htr : ∀ j < 512, (RealizedProgram.castElt (b := 1) (e.stmt 67 j) : (interp 1).K) = D.tr j)
    (h68 : ∀ j < 560, val 68 j = RealizedProgram.castElt (a := 1) (D.buf j))
    (h120 : ∀ i < 32, val 120 i = RealizedProgram.castElt (a := 1)
      (PackedClaim.pack HField.packing fun b => decide (D.mu (16 * i + b) = 1)))
    (h70 : ∀ i < 384, val 70 i = RealizedProgram.castElt (a := 1)
      (PackedClaim.pack HField.packing fun b => decide (D.w1 (16 * i + b) = 1))) :
    InputsAgree RD D where
  tr j hj := by
    rw [RealizedProgram.evalE_leaf, RealizedProgram.reader_of_opaque_nil _ (MldsaHHonest.kind67 (program := program))]
    exact htr j hj
  buf j hj := by
    obtain ⟨hp, hf, -, -⟩ := MldsaHHonest.priv6869 (program := program)
    rw [RealizedProgram.evalE_leaf, hr hp hf
      (by rw [(pad_facts (program := program)).2.2.2.1]; exact hj), h68 j hj]
    exact RealizedProgram.castElt_castElt_of_eq hf.symm _
  mu j hj := by
    obtain ⟨hb, hw, hfv, hfw, hsv, hsw, hn, hsel, he⟩ := MldsaHHonest.view121 (program := program)
    exact evalE_bitview hr hD.mu hb hw hfv hfw (by rw [hsv]) hsw hn hsel he h120 (by omega)
  w1 j hj := by
    obtain ⟨hb, hw, hfv, hfw, hsv, hsw, hn, hsel, he⟩ := MldsaHHonest.view71 (program := program)
    exact evalE_bitview hr hD.w1 hb hw hfv hfw (by rw [hsv]) hsw hn hsel he h70 (by omega)

end Inputs

/-! ## `μ`'s padding, conversely -/

section Padding

variable (e : program.Env interp)

/-- **`h2c.mu.padding.monotone` holds** where every set flag's predecessor is set. -/
theorem pad42_of (h : ∀ i < 135, flag e (i + 1) * (flag e i + 1) = 0) :
    program.HoldsWith (program.reader e) (program.predicate 42).body := by
  rw [(pad_exprs (program := program)).1]
  intro i hi
  rw [RealizedProgram.exprLen_mul, RealizedProgram.exprLen_reindex, (pad_facts (program := program)).2.2.2.2.2.1]
    at hi
  rw [RealizedProgram.evalWith_eq_iff MldsaHCross.domainField1]
  rw [evalE_zeroConst e (constPad 35 (by simp)).1 (constPad 35 (by simp)).2
      (pad_facts (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    RealizedProgram.evalE_mul, RealizedProgram.evalE_add, RealizedProgram.evalE_reindex, RealizedProgram.evalE_reindex,
    RealizedProgram.evalE_reindex, idx26_eq hi, idx27_id hi, idx28_eq hi, evalE_one7 e 0 rfl]
  exact h i hi

/-- **`h2c.mu.padding.max` holds** where flag `98` is clear. -/
theorem pad43_of (h : flag e 98 = 0) :
    program.HoldsWith (program.reader e) (program.predicate 43).body := by
  rw [(pad_exprs (program := program)).2.1]
  intro i hi
  rw [RealizedProgram.exprLen_reindex, (pad_facts (program := program)).2.2.2.2.2.2.1] at hi
  obtain rfl : i = 0 := by omega
  rw [RealizedProgram.evalWith_eq_iff MldsaHCross.domainField1]
  rw [evalE_listConst e (constPad 36 (by simp)).1 (constPad 36 (by simp)).2
      (pad_facts (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, RealizedProgram.evalE_reindex,
    (pad_facts (program := program)).2.2.2.2.2.2.2.2.2.2.1]
  exact h.trans HField.decode_zero.symm

/-- **`h2c.mu.padding.min` holds** where flag `65` is set. -/
theorem pad44_of (h : flag e 65 = 1) :
    program.HoldsWith (program.reader e) (program.predicate 44).body := by
  rw [(pad_exprs (program := program)).2.2.1]
  intro i hi
  rw [RealizedProgram.exprLen_add, RealizedProgram.exprLen_reindex, (pad_facts (program := program)).2.2.2.2.2.2.2.1]
    at hi
  obtain rfl : i = 0 := by omega
  rw [RealizedProgram.evalWith_eq_iff MldsaHCross.domainField1]
  rw [evalE_listConst e (constPad 36 (by simp)).1 (constPad 36 (by simp)).2
      (pad_facts (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, RealizedProgram.evalE_add,
    RealizedProgram.evalE_reindex, (pad_facts (program := program)).2.2.2.2.2.2.2.2.2.2.2.1, evalE_one7 e 0 rfl]
  change flag e 65 + 1 = _
  rw [h, show ([0] : List ℕ).getD 0 0 = 0 from rfl, HField.decode_zero,
    CharTwo.add_self_eq_zero]

/-- **`h2c.mu.padding.suffix` holds** where `suffix_eq`'s identity holds at every byte. -/
theorem pad45_of (h : ∀ i < 136, ((if i = 0 then 1 else flag e (i - 1)) + flag e i) *
      (selF.embedBits (by decide) (bufByte e i) + cH (program := program) (FH := FH) 38 i) = 0) :
    program.HoldsWith (program.reader e) (program.predicate 45).body := by
  rw [(pad_exprs (program := program)).2.2.2.1]
  intro i hi
  rw [RealizedProgram.exprLen_mul, RealizedProgram.exprLen_add,
    RealizedProgram.exprLen_ref MldsaHCross.refsOrdered (by rw [(hash_sizes (program := program)).1]; norm_num),
    (pad_exprs (program := program)).2.2.2.2.2.2.1, RealizedProgram.exprLen_reindex,
    (pad_facts (program := program)).2.2.2.2.2.2.2.2.1] at hi
  rw [RealizedProgram.evalWith_eq_iff MldsaHCross.domainField1]
  rw [evalE_zeroConst e (constPad 39 (by simp)).1 (constPad 39 (by simp)).2
      (pad_facts (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    RealizedProgram.evalE_mul, RealizedProgram.evalE_add, RealizedProgram.evalE_add, evalE_ref61 e hi, evalE_ref62 e hi,
    evalE_constH e (constPad 38 (by simp)).1 (constPad 38 (by simp)).2]
  exact h i hi

/-- **`h2c.mu.padding.zeros` holds** where `zeros_eq`'s identity holds at every byte. -/
theorem pad46_of (h : ∀ i < 136, ((if i = 0 then 1 else flag e (i - 1)) + 1) *
      (selF.embedBits (by decide) (bufByte e i) + cH (program := program) (FH := FH) 40 i) = 0) :
    program.HoldsWith (program.reader e) (program.predicate 46).body := by
  rw [(pad_exprs (program := program)).2.2.2.2.1]
  intro i hi
  rw [RealizedProgram.exprLen_mul, RealizedProgram.exprLen_add,
    RealizedProgram.exprLen_ref MldsaHCross.refsOrdered (by rw [(hash_sizes (program := program)).1]; norm_num),
    (pad_exprs (program := program)).2.2.2.2.2.2.1, RealizedProgram.exprLen_reindex,
    (pad_facts (program := program)).2.2.2.2.2.2.2.2.1] at hi
  rw [RealizedProgram.evalWith_eq_iff MldsaHCross.domainField1]
  rw [evalE_zeroConst e (constPad 39 (by simp)).1 (constPad 39 (by simp)).2
      (pad_facts (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    RealizedProgram.evalE_mul, RealizedProgram.evalE_add, RealizedProgram.evalE_add, evalE_ref61 e hi, evalE_ref62 e hi,
    RealizedProgram.evalE_reindex, idx33_eq hi, evalE_one7 e 0 rfl, RealizedProgram.evalE_mul,
    RealizedProgram.evalE_reindex, idx33_eq hi, evalE_ref64, one_mul,
    evalE_constH e (constPad 40 (by simp)).1 (constPad 40 (by simp)).2]
  exact h i hi

/-- **`h2c.mu.padding.output` holds** where `h2c.mu.out` reads `μ`'s state's first `512` bits. -/
theorem pad47_of (h : ∀ j < 512, program.evalE (program.reader e) 1 (.leaf 121) j =
      program.evalE (program.reader e) 1 (.leaf 119) j) :
    program.HoldsWith (program.reader e) (program.predicate 47).body := by
  rw [(pad_exprs (program := program)).2.2.2.2.2.1]
  intro j hj
  rw [RealizedProgram.exprLen_mul, RealizedProgram.exprLen_reindex,
    (pad_facts (program := program)).2.2.2.2.2.2.2.2.2.1] at hj
  rw [RealizedProgram.evalWith_eq_iff MldsaHCross.domainField1]
  rw [evalE_zeroConst e ((hash_sizes (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 10 (by simp)).1
      ((hash_sizes (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 10 (by simp)).2
      (hash_sizes (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    RealizedProgram.evalE_mul, RealizedProgram.evalE_reindex, idx37_eq hj, evalE_ref64, one_mul,
    RealizedProgram.evalE_add, RealizedProgram.evalE_reindex, RealizedProgram.evalE_reindex, idx13_id hj,
    RealizedProgram.evalE_ref MldsaHCross.refsOrdered _ _ (by rw [(hash_sizes (program := program)).1]; norm_num),
    (pad_exprs (program := program)).2.2.2.2.2.2.2.2.2.2, RealizedProgram.evalE_reindex, idx13_id hj, h j hj,
    CharTwo.add_self_eq_zero]

/-- **The honest buffer byte** at block byte `i` for a message `msg` of length `L`: the message,
SHAKE256's suffix `0x1F` at `66 + L`, `0x80` at the last byte, `0` between. -/
def bufNat (L : ℕ) (msg : ℕ → ℕ) (i : ℕ) : ℕ :=
  if i < 66 + L then msg (i - 66) else if i = 66 + L then 0x1F else if i = 135 then 0x80 else 0

/-- **The honest in-message flags** for a message of length `L`: set below `66 + L`. -/
def flagNat (L i : ℕ) : ℕ := if i < 66 + L then 1 else 0

/-- **`μ`'s padding holds at honest flags and buffer**: the flags set below `66 + L`, the buffer
bytes past `66` the honest buffer bytes (`bufNat`), `L ≤ 32`. -/
theorem pad_holds_honest {L : ℕ} (hL : L ≤ 32) {msg : ℕ → ℕ} (hmsg : ∀ k, msg k < 256)
    (hflag : ∀ i < 136, flag e i = (flagNat L i : (interp 1).K))
    (hbuf : ∀ i < 136, 66 ≤ i →
      bufByte e i = fun u : Fin 8 => Bits.constBit (K := (interp 1).K) (bufNat L msg i) u)
    {q : ℕ} (hq : q ∈ [42, 43, 44, 45, 46]) :
    program.HoldsWith (program.reader e) (program.predicate q).body := by
  have hconst := (pad_facts (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have h2 : (2 : (interp 1).K) = 0 := CharTwo.two_eq_zero
  have hfv : ∀ i < 136, flag e i = if i < 66 + L then 1 else 0 := fun i hi => by
    rw [hflag i hi, flagNat]
    split_ifs <;> simp
  have hemb : ∀ i < 136, 66 ≤ i → selF.embedBits (by decide) (bufByte e i) =
      selF.embed (bufNat L msg i) := fun i hi h66 => by
    rw [hbuf i hi h66, selF.embedBits_eq _ (fun u => Bits.constBit_bool _ _),
      Bits.natOfBits_constBit, Nat.mod_eq_of_lt]
    have := hmsg (i - 66)
    unfold bufNat
    split_ifs <;> norm_num <;> omega
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · refine pad42_of e fun i hi => ?_
    rw [hfv _ (by omega), hfv _ (by omega)]
    split_ifs <;> first | omega | simp [CharTwo.add_self_eq_zero]
  · refine pad43_of e ?_
    rw [hfv 98 (by norm_num), if_neg (by omega)]
  · refine pad44_of e ?_
    rw [hfv 65 (by norm_num), if_pos (by omega)]
  · refine pad45_of e fun i hi => ?_
    by_cases hb : i = 66 + L
    · subst hb
      rw [if_neg (by omega), hfv _ (by omega), hfv _ (by omega), if_pos (by omega), if_neg (by omega),
        add_zero, one_mul, hemb _ hi (by omega), cH, hconst.1 _ (by omega), decode_xorSel37 (by norm_num)]
      unfold bufNat
      rw [if_neg (by omega), if_pos rfl]
      exact CharTwo.add_self_eq_zero _
    · have h0 : ((if i = 0 then 1 else flag e (i - 1)) + flag e i) = 0 := by
        rw [hfv i hi]
        by_cases hi0 : i = 0
        · subst hi0
          rw [if_pos rfl, if_pos (by omega)]
          exact CharTwo.add_self_eq_zero _
        · rw [if_neg hi0, hfv _ (by omega)]
          split_ifs <;> first | omega | exact CharTwo.add_self_eq_zero _
      rw [h0, zero_mul]
  · refine pad46_of e fun i hi => ?_
    by_cases hle : i ≤ 66 + L
    · have h0 : (if i = 0 then 1 else flag e (i - 1)) + 1 = 0 := by
        by_cases hi0 : i = 0
        · rw [if_pos hi0]
          exact CharTwo.add_self_eq_zero _
        · rw [if_neg hi0, hfv _ (by omega), if_pos (by omega)]
          exact CharTwo.add_self_eq_zero _
      rw [h0, zero_mul]
    · rw [hemb _ hi (by omega)]
      by_cases h135 : i = 135
      · subst h135
        rw [cH, hconst.2.2.1, decode_xorSel37 (by norm_num)]
        unfold bufNat
        rw [if_neg (by omega), if_neg (by omega), if_pos rfl, if_neg (by omega),
          CharTwo.add_self_eq_zero, mul_zero]
      · rw [cH_eq_zero (program := program) (F0 := F0) (FH := FH) (hconst.2.1 i (by omega)), add_zero]
        simp only [bufNat, show ¬ i < 66 + L by omega, show i ≠ 66 + L by omega, h135, if_false]
        have : (selF (F0 := F0) (FH := FH)).embed 0 = 0 := by
          unfold SelectionField.embed selectionEmbed
          simp
        rw [this, mul_zero]

end Padding

end GordieHowe.MLDSA44.Native.ROMParams
