-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Ring.HonestInput
public import GordieHowe.Applications.MLDSA44.Honest.SampleInBall

@[expose] public section

/-!
# GordieHowe: domain `H`'s core at the honest values of an ML-DSA-44 ring input

The native ML-DSA-44 ring programs hold the native ML-DSA program's domain `H` core (its
predicates `48 … 270`: the seven Keccak-f permutations of `c̃' = H(μ ‖ w1Encode(w1))`, the two of
SampleInBall's stream `H(c̃')`, SampleInBall's selection and memory check) with `μ` committed
(`GordieHowe.MLDSA44.Ring.Native.MldsaRingEmbed`). This file gives the honest values of that core
at a ring input (`GordieHowe.MLDSA44.Ring.RingIn`), read at the native program's value identifiers,
and proves the core's predicates at any environment of a native ML-DSA program reading them
(`GordieHowe.RealizedProgram.ReadsCells`), so that they hold, read through the renaming, in each native ring
program. The proof of possession's honest values (`GordieHowe.MLDSA44.hVal`) compute `μ`
from `tr` and the message; here `μ` is the ring input's (`RingIn.mu`, `μ = H(tr ‖ M′)` of the
signer's key).

* **The honest data** (`muBitsR`, `w1BitsR`, `dataR`): the hash inputs `μ` and `w1Encode(w1)` as
  bits (`GordieHowe.MLDSA44.HashData`, `tr` and `μ`'s buffer `0`), and the honest committed
  values (`hValCore`): `w1`'s and `μ`'s words, the core rounds' words (the packed honest Keccak
  trace), the selected bytes' bits (the input's positions), the threshold words (the honest low
  threshold bits of `c̃`'s stream) and the memory cells (`MemoryShuffle.honestWit` of the positions
  and the stream's sign bits).
* **The rounds** (`rounds_core`): the round predicates of permutations `1 … 9` at an environment
  reading the honest trace words and `μ`'s and `w1`'s words (the converse of the frontend's
  `permRelation_of`, permutation by permutation).
* **The hash outputs** (`cTildeOf_honest`, `sibStream_honest`): where the core's rounds hold,
  `c̃'` is the ring input's `c̃` (Algorithm 8's commitment check, `RingIn.checks`) and the stream
  is `GordieHowe.MLDSA44.PoP.stream c̃`, by the frontend's sponge soundness (`Shake256.squeezeOut_sound`)
  read at the round predicates only.
* **SampleInBall** (`select_core`, `mem_core`): the selection and the memory check at the honest
  cells; **the decoded challenge** (`chalPair_core`) is the ring input's challenge.
* **The core** (`hPreds_core`): every predicate `48 … 270`.
-/

namespace GordieHowe.MLDSA44.Ring.Native

open Generated.MLDSA44.Native.ROMParams.Program
open GordieHowe.Bits GordieHowe.Keccak GordieHowe.KeccakTrace RealizedProgram
open MLDSA44.Native.ROMParams

set_option linter.unusedSectionVars false

variable {msgLen : ℕ}

/-! ## The honest hash data -/

section Data

variable {K : Type} [Field K] (y : RingIn msgLen)

/-- **The bits of the ring input's `μ`**: bit `b` of byte `k` at `8 k + b`, `0` past `512`. -/
-- spec-side
def muBitsR (n : ℕ) : K :=
  if h : n < 512 then constBit ((y.mu.get ⟨n / 8, by omega⟩).toNat) (n % 8) else 0

/-- **The bytes of `w1Encode(w1)`** at the ring input, `0` past `768`. -/
-- spec-side
noncomputable def w1NatR (k : ℕ) : ℕ :=
  if h : k < 768 then (MLDSA44.PoP.Compose.honestW1Bytes y.key y.c y.z y.h ⟨k, h⟩).toNat else 0

/-- **The bits of `w1Encode(w1)`** at the ring input. -/
-- spec-side
noncomputable def w1BitsR (n : ℕ) : K := constBit (w1NatR y (n / 8)) (n % 8)

/-- **The honest hash inputs of domain `H`'s core** (`HashData`): `μ` and `w1Encode(w1)`; `tr` and
`μ`'s buffer, which the core does not read, `0`. -/
-- spec-side
noncomputable def dataR : HashData K := ⟨fun _ => 0, fun _ => 0, muBitsR y, w1BitsR y⟩

/-- **The honest hash data are bits.** -/
theorem dataR_bool : (dataR (K := K) y).Bool where
  tr _ := Or.inl rfl
  buf _ := Or.inl rfl
  mu j := by
    unfold dataR muBitsR
    dsimp only
    split_ifs
    · exact constBit_bool _ _
    · exact Or.inl rfl
  w1 _ := constBit_bool _ _

/-- **The ring input's challenge is ternary.** -/
theorem c_ternaryR (k : Fin mldsa44.N) : y.c k = 0 ∨ y.c k = 1 ∨ y.c k = -1 :=
  MLDSA44.PoP.challenge_ternary _ _ k

/-- **The ring input's stream**: `SHAKE256(c̃, 272)` (`GordieHowe.MLDSA44.PoP.stream`). -/
-- spec-side
def streamR : Fin 272 → ℕ := MLDSA44.PoP.stream y.ctilde

/-- **The honest candidates**: bytes `8 … 271` of the stream. -/
-- spec-side
def candNatR (k : Fin 264) : ℕ := streamR y ⟨8 + k, by omega⟩

/-- **The honest low threshold bits**, flat: bit `b` of position `k` at `6 k + b`. -/
-- spec-side
noncomputable def lowFR (n : ℕ) : K :=
  if h : n < 1584 then constBit (SelectFirstTau.honestThr 39 (candNatR y) ⟨n / 6, by omega⟩) (n % 6)
  else 0

/-- **The honest selected bytes' bits**, flat: bit `b` of step `t` at `8 t + b`, the input's
positions. -/
-- spec-side
def jFR (n : ℕ) : K :=
  if h : n < 312 then constBit (y.positions ⟨n / 8, by change n / 8 < 39; omega⟩) (n % 8) else 0

end Data

/-! ## The honest committed values of domain `H`'s core -/

section Values

variable {program : RealizedProgram} [MldsaHHonest program] [MldsaHShuffle program]
  [MldsaHSelHonest program] {F0 FH : FieldInterp} [HField FH] [MldsaHConsts program FH]
  (y : RingIn msgLen)

set_option hygiene false in
local notation "interp" => mldsaInterpOf F0 FH

/-- **The honest committed values of the hash in domain `H`'s core**: `w1`'s and `μ`'s words their
bits packed, the rounds' words the packed states of the honest trace; `0` elsewhere. -/
-- spec-side
noncomputable def hashValCore (v i : ℕ) : (interp (program.valueField v)).K :=
  if v = 69 then castElt (a := 1) (packWord (FH := FH) (w1BitsR y) i)
  else if v = 119 then castElt (a := 1) (packWord (FH := FH) (muBitsR y) i)
  else match wordsOwner? v with
    | some pt => castElt (a := 1) (stateWords HField.packing
        (iterRounds ((dataR (K := FH.K) y).states pt.1) ((pt.2 : ℕ) + 1)) i)
    | none => 0

variable (program F0 FH) in
/-- SampleInBall's step count is the signature's `τ`. -/
theorem samM_τR : (samM program F0 FH).τ = mldsa44.τ := rfl

variable (program F0 FH) in
/-- **The honest signs**: the stream's sign bits (`MLDSA44.sampleInBallSign`), indexed by
SampleInBall's steps. -/
-- spec-side
def sgBR (t : Fin (samM program F0 FH).τ) : Bool :=
  MLDSA44.sampleInBallSign (streamR y) (Fin.cast (samM_τR program F0 FH) t)

variable (program F0 FH) in
/-- **The input's positions**, indexed by SampleInBall's steps. -/
-- spec-side
def posNR (t : Fin (samM program F0 FH).τ) : ℕ := y.positions (Fin.cast (samM_τR program F0 FH) t)

variable (program F0 FH) in
/-- **The honest memory trace** of SampleInBall's shuffle (`MemoryShuffle.honestWit`) on the
input's positions and the stream's signs. -/
-- spec-side
noncomputable def honestMemWR :
    MemoryShuffle.Wit (interp 1).K (samM program F0 FH).N (samM program F0 FH).τ :=
  MemoryShuffle.honestWit (samM program F0 FH).field (samM program F0 FH).Θ (posNR program F0 FH y)
    (sgBR program F0 FH y)

variable (program F0 FH) in
/-- **The honest cells of SampleInBall's memory check**, flat per value (`560`–`565`): the read
values, the read origins' bits, the final cells, the final origins, the units, the origins. -/
-- spec-side
noncomputable def memFR (v n : ℕ) : (interp 1).K :=
  if v = 560 then (if h : n < 39 then ((honestMemWR program F0 FH y).read ⟨n, h⟩).value else 0)
  else if v = 561 then
    (if h : n < 234 then ((honestMemWR program F0 FH y).read ⟨n / 6, by change n / 6 < 39; omega⟩).origin
      ⟨n % 6, by omega⟩ else 0)
  else if v = 562 then (if h : n < 256 then (honestMemWR program F0 FH y).cEnc ⟨n, h⟩ else 0)
  else if v = 563 then (if h : n < 256 then (honestMemWR program F0 FH y).finalOrigin ⟨n, h⟩ else 0)
  else if v = 564 then (if h : n < 39 then
      MemoryShuffle.unit (samM program F0 FH).Θ ((honestMemWR program F0 FH y).signs ⟨n, h⟩)
      else 0)
  else if v = 565 then (if h : n < 39 then (samM program F0 FH).originOf
      ((honestMemWR program F0 FH y).read ⟨n, h⟩).origin else 0)
  else 0

variable (program F0 FH) in
/-- **The honest committed values of domain `H`'s core** at a ring input: the hash's
(`hashValCore`), the selected bytes' bits (`556`), the threshold words (`557`) and the memory
cells (`560`–`565`); `0` elsewhere.

Running time: nine Keccak-f permutations (the core trace), `16` packing sums per word, one
SHAKE256 call of `272` bytes and SampleInBall's honest memory trace (`39` steps over `256` cells).
This running time is argued here, not proved in Lean. -/
-- spec-side
noncomputable def hValCore (v j : ℕ) : (interp (program.valueField v)).K :=
  if IsHashValue v then hashValCore (program := program) (F0 := F0) (FH := FH) y v j
  else if v = 556 then castElt (a := 1) (jFR (K := FH.K) y j)
  else if v = 557 then castElt (a := 1) (packWord (FH := FH) (lowFR (K := FH.K) y) j)
  else if v ∈ [560, 561, 562, 563, 564, 565] then castElt (a := 1) (memFR program F0 FH y v j)
  else 0

end Values

/-! ## The rounds of the core -/

/-- **Value `v` is a committed hash value of domain `H`'s core**: `w1`'s or `μ`'s words, or the
words of a round of permutations `1 … 9`. -/
def coreHashB (v : ℕ) : Bool :=
  v == 69 || v == 119 || match wordsOwner? v with
    | some pt => (pt.1 : ℕ) != 0
    | none => false

section Rounds

variable {program : RealizedProgram} [MldsaHHonest program] {F0 FH : FieldInterp} [HField FH]
  [MldsaHConstsSelect program FH]

set_option hygiene false in
local notation "interp" => mldsaInterpOf F0 FH

/-- **The committed words of permutation `p` are the packed states of the trace `S`**: round `t`
holds the words of its output `iterRounds (S p) (t + 1)`. -/
def WordsAt (val : program.Valuation interp) (S : Fin 10 → State FH.K) (p : Fin 10) : Prop :=
  ∀ t : Fin 24, ∀ i < 100, val (wordsVal p t) i =
    castElt (a := 1) (stateWords HField.packing (iterRounds (S p) ((t : ℕ) + 1)) i)

variable {e : program.Env interp} {val : program.Valuation interp}
  (hr : program.ReadsCells 1 e val) {S : Fin 10 → State FH.K}

include hr

/-- **Round `t`'s output reads the trace** at an environment reading permutation `p`'s words. -/
theorem stateOf_outAt {p : Fin 10} (hS : ∀ x y, AllBool (S p x y)) (hw : WordsAt val S p)
    (t : Fin 24) :
    stateOf (program.evalE (program.reader e) 1 (.leaf (outVal p t))) =
      iterRounds (S p) ((t : ℕ) + 1) := by
  obtain ⟨hb, hpw, hfv, hfw, hsv, hsw, hn⟩ := MldsaHHonest.words_checks (program := program) p t
  funext x' y' z
  simp only [stateOf]
  rw [evalE_words hr (iterRounds_allBool hS _) hb hpw hfv hfw hsv hsw hn (hw t)
    (keccakIdx_lt x' y' z), stateBit_keccakIdx]

/-- **Round `t`'s input reads the trace** at an environment reading permutation `p`'s words,
given the permutation's input. -/
theorem stateOf_srcAt {p : Fin 10} (hS : ∀ x y, AllBool (S p x y)) (hw : WordsAt val S p)
    (hin : stateOf (program.evalE (program.reader e) 1 (.ref (linRef p 0 - 2))) = S p)
    (t : Fin 24) :
    stateOf (program.evalE (program.reader e) 1 (roundSrc p t.castSucc).expr) =
      iterRounds (S p) t := by
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
    have := stateOf_outAt hr hS hw ⟨t - 1, by omega⟩
    simp only at this
    simp only [StateSrc.expr]
    rw [this]
    congr 1
    omega

/-- **The round predicates of permutation `p` hold** at an environment reading its words, given
its input (the converse of the frontend's `permRelation_of`). -/
theorem round_holdsAt {p : Fin 10} (hS : ∀ x y, AllBool (S p x y)) (hw : WordsAt val S p)
    (hin : stateOf (program.evalE (program.reader e) 1 (.ref (linRef p 0 - 2))) = S p)
    (t : Fin 24) :
    program.HoldsWith (program.reader e) (program.predicate (roundPred p t)).body := by
  obtain ⟨hb, hlin, hcol⟩ := (roundShapes (program := program)) p t
  obtain ⟨-, -, hL, hC, -⟩ := (round_facts (program := program)) p t
  have hsize : (program.value (outVal p t)).size ≤ 1600 :=
    (MldsaHHonest.words_checks (program := program) p t).2.2.2.2.1.le
  have key : ∀ D, program.domainField 1 = D →
      (∀ j < 1600, program.evalE (program.reader e) D (.leaf 10) j = 1) →
      (∀ j < 1600, program.evalE (program.reader e) D (.leaf 12) j = 0) →
      (∀ x' y' z', program.evalE (program.reader e) D (.leaf (rcLeaf t)) (keccakIdx x' y' z') =
        iotaVec t (x', y', z')) →
      RoundRelation t (stateOf (program.evalE (program.reader e) D (roundSrc p t.castSucc).expr))
        (stateOf (program.evalE (program.reader e) D (.leaf (outVal p t)))) →
      program.HoldsWith (program.reader e) (program.predicate (roundPred p t)).body := by
    intro D hD hones hzeros hrc hrel
    subst hD
    exact @holdsWith_of_shapes program interp MldsaHCross.refsOrdered _ _ _ _ _ t
      charP_domainH hb hlin hcol hL hC keccakMaps hsize hones hzeros hrc hrel
  refine key 1 MldsaHCross.domainField1 (fun j hj => evalE_ones _ hj)
    (fun j hj => evalE_zeros _ hj) (evalE_rc _ t) ?_
  rw [stateOf_srcAt hr hS hw hin, stateOf_outAt hr hS hw]
  refine (roundRelation_iff (iterRounds_allBool hS _)).2 ?_
  show Keccak.round _ _ = _
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt t.isLt)

variable {D : HashData FH.K}

/-- **Round `t`'s output reads the trace**, coordinatewise. -/
theorem evalE_outAt (hD : D.Bool) {p : Fin 10} (hw : WordsAt val D.states p) (t : Fin 24) {j : ℕ}
    (hj : j < 1600) :
    program.evalE (program.reader e) 1 (.leaf (outVal p t)) j =
      stateBit (iterRounds (D.states p) ((t : ℕ) + 1)) j := by
  obtain ⟨hb, hpw, hfv, hfw, hsv, hsw, hn⟩ := MldsaHHonest.words_checks (program := program) p t
  exact evalE_words hr (iterRounds_allBool (D.states_bool hD p) _) hb hpw hfv hfw hsv hsw hn
    (hw t) hj

omit hr in
/-- **`c̃'`'s padded input** (`ref 66`) reads `ctIn` where `μ` and `w1` read the data's. -/
theorem evalE_ref66_core
    (hmu : ∀ j < 512, program.evalE (program.reader e) 1 (.leaf 120) j = D.mu j)
    (hw1 : ∀ j < 6144, program.evalE (program.reader e) 1 (.leaf 70) j = D.w1 j)
    {j : ℕ} (hj : j < 7616) :
    program.evalE (program.reader e) 1 (.ref 66) j = D.ctIn j := by
  rw [evalE_ref66 _ hj]
  unfold HashData.ctIn
  split_ifs with h1 h2
  · exact hmu j h1
  · exact hw1 _ (by omega)
  · rfl
  · rfl

/-- **The inputs of permutations `1 … 9` read the trace** at an environment reading the core's
words and `μ`'s and `w1`'s bits. -/
theorem stateOf_in_core (hD : D.Bool)
    (hmu : ∀ j < 512, program.evalE (program.reader e) 1 (.leaf 120) j = D.mu j)
    (hw1 : ∀ j < 6144, program.evalE (program.reader e) 1 (.leaf 70) j = D.w1 j)
    (hw : ∀ p : Fin 10, (p : ℕ) ≠ 0 → WordsAt val D.states p) (p : Fin 10) (hp : (p : ℕ) ≠ 0) :
    stateOf (program.evalE (program.reader e) 1 (.ref (linRef p 0 - 2))) = D.states p := by
  have hpl := p.isLt
  rcases Nat.lt_or_ge (p : ℕ) 2 with h2 | h2
  · have hp1 : p = 1 := Fin.ext (by omega)
    subst hp1
    simp only [HashData.states, show ((1 : Fin 10) : ℕ) = 1 from rfl]
    simp only [show (1 : ℕ) ≠ 0 by omega, ite_false, show (1 : ℕ) ≤ 7 by omega, ite_true]
    unfold HashData.ctState
    refine stateOf_congr fun j hj => ?_
    rw [show linRef 1 0 - 2 = 67 from rfl, evalE_ref67 _ hj]
    split_ifs with h
    · exact evalE_ref66_core hmu hw1 (by omega)
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
    rw [ho, evalE_outAt hr hD (hw _ (by simp only; omega)) _ hj, hs']
    congr 1
    split_ifs with h
    · rw [evalE_ref66_core hmu hw1 (by omega)]
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
    · rw [evalE_458 _ h2, show (456 : ℕ) = outVal (7 : Fin 10) (23 : Fin 24) from rfl,
        evalE_outAt hr hD (hw 7 (by decide)) _ hj]
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
    simp only [stateOf]
    rw [show linRef 9 0 - 2 = 459 from rfl, evalE_ref459 _ (keccakIdx_lt x' y' z),
      show (505 : ℕ) = outVal (8 : Fin 10) (23 : Fin 24) from rfl,
      evalE_outAt hr hD (hw 8 (by decide)) _ (keccakIdx_lt x' y' z), stateBit_keccakIdx]
    simp only [HashData.states, show ((8 : Fin 10) : ℕ) = 8 from rfl]
    simp

/-- **The round predicates of permutations `1 … 9` hold** at an environment reading the core's
honest words and `μ`'s and `w1`'s bits. -/
theorem rounds_core (hD : D.Bool)
    (hmu : ∀ j < 512, program.evalE (program.reader e) 1 (.leaf 120) j = D.mu j)
    (hw1 : ∀ j < 6144, program.evalE (program.reader e) 1 (.leaf 70) j = D.w1 j)
    (hw : ∀ p : Fin 10, (p : ℕ) ≠ 0 → WordsAt val D.states p) (p : Fin 10) (hp : (p : ℕ) ≠ 0)
    (t : Fin 24) :
    program.HoldsWith (program.reader e) (program.predicate (roundPred p t)).body :=
  round_holdsAt hr (D.states_bool hD p) (hw p hp) (stateOf_in_core hr hD hmu hw1 hw p hp) t

end Rounds

/-! ## The hash outputs where the core's rounds hold -/

section Outputs

variable {program : RealizedProgram} [MldsaHHonest program] {F0 FH : FieldInterp} [HField FH]
  [MldsaHConstsSelect program FH]

set_option hygiene false in
local notation "interp" => mldsaInterpOf F0 FH

/-- **The round predicates of permutations `1 … 9` hold.** -/
def RoundsCore (e : program.Env interp) : Prop :=
  ∀ p : Fin 10, (p : ℕ) ≠ 0 → ∀ t : Fin 24, program.HoldsAt e (program.predicate (roundPred p t)).body

variable {e : program.Env interp} (hround : RoundsCore e)
include hround

/-- **The round relations of permutations `1 … 9` hold** where their round predicates hold
(`permRelation_of`). -/
theorem permRelation_rounds (p : Fin 10) (hp : (p : ℕ) ≠ 0) : PermRelation (permStates e p) :=
  permRelation_of (roundShapes_core p hp) (round_facts_core p hp) (hround p hp)

/-- **`c̃'`'s hash soundness** at the round predicates (`Shake256.squeezeOut_sound` at the seven
absorbs, the frontend's `ctOut_sound` read at the rounds only). -/
theorem ctOut_sound_rounds (o : Fin 32) :
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
  exact (permRelation_rounds hround _ (by simp)).encodes h

/-- **The stream's hash soundness** at the round predicates (`Shake256.squeezeOut_sound` at the
absorb and the squeeze, the frontend's `sbOut_sound` read at the rounds only). -/
theorem sbOut_sound_rounds (o : Fin 272) :
    natOfBits (Shake256.squeezeOut (sp := Shake256.SpongeSpec.shake256) (len := 32)
        (fun k => sbFin e k) o) =
      xofFin Shake256.SpongeSpec.shake256.xof
        (Shake256.inputBytes (Falcon512.HashCircuit.byteWires (cTildeBits (program.reader e)))) 272 o := by
  refine Shake256.squeezeOut_sound
    (Falcon512.HashCircuit.byteWires_allBool fun t => leaf_bool e (kind458 (program := program)) _)
    (fun j h => ?_) o
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
  exact (permRelation_rounds hround _ (by simp)).encodes h

/-- **`c̃'` is the commitment hash** `H(μ ‖ w, 32)` where the core's rounds hold, at any `μ` whose
bytes are those of `muBits` and any `w` whose bytes are those of H's `w1` bits (the frontend's
`cTildeOf_eq_hashCommitment` read at the rounds only). -/
theorem cTildeOf_rounds {mu : _root_.MLDSA.Bytes 64} {w : List UInt8}
    (hmu : Shake256.inputBytes (Falcon512.HashCircuit.byteWires (muBits (program.reader e))) =
      mu.toList.map UInt8.toNat)
    (hw : Shake256.inputBytes (Falcon512.HashCircuit.byteWires (w1HBits (program.reader e))) =
      w.map UInt8.toNat) :
    _root_.MLDSA.Concrete.hashCommitment _root_.MLDSA.mldsa44 mu w = cTildeOf (program.reader e) := by
  apply Vector.ext
  intro i hi
  apply UInt8.toNat_inj.mp
  have hl := MLDSA44.hashCommitment_get mu w ⟨i, hi⟩
  change UInt8.toNat (Vector.get _ ⟨i, hi⟩) = UInt8.toNat (Vector.get _ ⟨i, hi⟩)
  refine hl.trans ?_
  rw [← hmu, ← hw, ← Shake256.SpongeSpec.xof_shake256, ← inputBytes_ct e,
    ← ctOut_sound_rounds hround ⟨i, hi⟩, ctOut_eq e ⟨i, hi⟩]
  simp only [cTildeOf, Vector.get_ofFn]
  rw [MLDSA44.Native.toNat_toUInt8_natOfBits]
  rfl

/-- **The SampleInBall stream is `SHAKE256(c̃')`** where the core's rounds hold. -/
theorem sibStream_rounds :
    sibStream (program.reader e) =
      xofFin GordieHowe.shake256 ((cTildeOf (program.reader e)).toList.map UInt8.toNat) (264 + 8) := by
  funext o
  rw [← sbOut_eq e o, sbOut_sound_rounds hround o, inputBytes_cTilde,
    Shake256.SpongeSpec.xof_shake256]

end Outputs

/-! ## The core at the honest values -/

/-- **The honest trace's read origins are bits** (`MemoryShuffle.honestWit`, at any positions and
signs). -/
theorem honestWit_origin_bool {K : Type*} [Field K] [DecidableEq K] {S N τ : ℕ}
    (F : SelectionField K S) (Θ : MemoryShuffle.Theta K) (pos : Fin τ → ℕ) (sg : Fin τ → Bool)
    (s : Fin τ) (b : Fin 6) :
    ((MemoryShuffle.honestWit (N := N) F Θ pos sg).read s).origin b = 0 ∨
      ((MemoryShuffle.honestWit (N := N) F Θ pos sg).read s).origin b = 1 :=
  constBit_bool _ _

section Honest

variable {program : RealizedProgram} [MldsaHHonest program] [MldsaHShuffle program]
  [MldsaHSelHonest program] {F0 FH : FieldInterp} [HField FH] [MldsaHConsts program FH]
  (y : RingIn msgLen)

set_option hygiene false in
local notation "interp" => mldsaInterpOf F0 FH

/-- **The stream's bytes are bits** (bit views). -/
theorem sibByte_bool (e : program.Env interp) (o : Fin (264 + 8)) :
    AllBool (sibByte (program.reader e) o) := fun b => by
  obtain ⟨-, -, -, k4, -, -, k7, -⟩ := view_kinds (program := program)
  unfold sibByte Falcon512.HashCircuit.byteWires sibBits
  dsimp only
  split_ifs
  · exact leaf_bool e k4 _
  · exact leaf_bool e k7 _

variable {e : program.Env interp} {val : program.Valuation interp} (hr : program.ReadsCells 1 e val)
  (hh : ∀ v, coreHashB v = true → val v = hashValCore (program := program) (F0 := F0) (FH := FH) y v)

set_option hygiene false in
local notation "RD" => program.reader e

include hr hh

omit hr in
/-- **The core's committed trace words are the honest data's packed trace.** -/
theorem wordsAt_honest (p : Fin 10) (hp : (p : ℕ) ≠ 0) : WordsAt val (dataR (K := FH.K) y).states p := by
  intro t i _
  obtain ⟨hw, -, -, h70, h120⟩ := wordsOwner_checks
  have h1 : wordsVal p t ≠ 69 := fun h => by
    have := hw p t
    rw [h, h70] at this
    cases this
  have h2 : wordsVal p t ≠ 119 := fun h => by
    have := hw p t
    rw [h, h120] at this
    cases this
  have hc : coreHashB (wordsVal p t) = true := by
    unfold coreHashB
    rw [hw p t]
    simp [hp]
  rw [hh _ hc]
  unfold hashValCore
  rw [if_neg h1, if_neg h2, hw p t]

/-- **`μ`'s bits read the ring input's `μ`** (the bit view `120` of `μ`'s words `119`). -/
theorem evalE_mu_honest {j : ℕ} (hj : j < 512) :
    program.evalE RD 1 (.leaf 120) j = muBitsR (K := FH.K) y j := by
  obtain ⟨hb, hw, hfv, hfw, hsv, hsw, hn, hsel, he⟩ := MldsaHHonest.view121 (program := program)
  refine evalE_bitview hr (fun j => (dataR_bool (K := FH.K) y).mu j) hb hw hfv hfw (by rw [hsv])
    hsw hn hsel he (fun i _ => ?_) (by omega)
  rw [hh 119 (by decide)]
  unfold hashValCore
  rw [if_neg (by decide), if_pos rfl]
  rfl

/-- **`w1`'s bits read `w1Encode(w1)`** (the bit view `70` of `w1`'s words `69`). -/
theorem evalE_w1_honest {j : ℕ} (hj : j < 6144) :
    program.evalE RD 1 (.leaf 70) j = w1BitsR (K := FH.K) y j := by
  obtain ⟨hb, hw, hfv, hfw, hsv, hsw, hn, hsel, he⟩ := MldsaHHonest.view71 (program := program)
  refine evalE_bitview hr (fun j => (dataR_bool (K := FH.K) y).w1 j) hb hw hfv hfw (by rw [hsv])
    hsw hn hsel he (fun i _ => ?_) (by omega)
  rw [hh 69 (by decide)]
  unfold hashValCore
  rw [if_pos rfl]
  rfl

/-- **The core's rounds hold** at the honest values. -/
theorem rounds_honest : RoundsCore e :=
  fun p hp t => rounds_core hr (dataR_bool (K := FH.K) y) (fun _ hj => evalE_mu_honest y hr hh hj)
    (fun _ hj => evalE_w1_honest y hr hh hj) (fun p hp => wordsAt_honest y hh p hp) p hp t

/-- **`μ`'s bytes are the ring input's `μ`.** -/
theorem inputBytes_mu_honest :
    Shake256.inputBytes (Falcon512.HashCircuit.byteWires (muBits RD)) = y.mu.toList.map UInt8.toNat := by
  apply List.ext_getElem
  · simp [Shake256.inputBytes]
  · intro i h₁ h₂
    simp only [Shake256.inputBytes, List.getElem_ofFn, List.getElem_map, Vector.getElem_toList]
    have hi : i < 64 := by simpa [Shake256.inputBytes] using h₁
    have hb : Falcon512.HashCircuit.byteWires (muBits RD) ⟨i, hi⟩ =
        fun b : Fin 8 => constBit (K := (interp 1).K) ((y.mu.get ⟨i, hi⟩).toNat) b := by
      funext b
      have hb8 := b.isLt
      have e1 : (8 * i + (b : ℕ)) / 8 = i := by omega
      have e2 : (8 * i + (b : ℕ)) % 8 = b := by omega
      change program.evalE (program.reader e) 1 (.leaf 120) (8 * i + b) = _
      rw [evalE_mu_honest y hr hh (by omega)]
      unfold muBitsR
      rw [dif_pos (by omega)]
      simp only [e1, e2]
    rw [hb, natOfBits_constBit, Nat.mod_eq_of_lt (UInt8.toNat_lt _)]
    rfl

/-- **`w1`'s bytes are `w1Encode(w1)`.** -/
theorem inputBytes_w1_honest :
    Shake256.inputBytes (Falcon512.HashCircuit.byteWires (w1HBits RD)) =
      (_root_.MLDSA.Concrete.w1Encode _root_.MLDSA.mldsa44
        (MLDSA44.PoP.Compose.honestW1 y.key y.c y.z y.h)).map UInt8.toNat := by
  have hlen := MLDSA44.w1Encode_length_mldsa44 (MLDSA44.PoP.Compose.honestW1 y.key y.c y.z y.h)
  apply List.ext_getElem (by rw [Shake256.inputBytes, List.length_ofFn, List.length_map, hlen])
  intro i h₁ h₂
  have hi : i < 768 := by
    rw [Shake256.inputBytes, List.length_ofFn] at h₁
    exact h₁
  simp only [Shake256.inputBytes, List.getElem_ofFn, List.getElem_map]
  have hb : Falcon512.HashCircuit.byteWires (w1HBits RD) ⟨i, hi⟩ =
      fun b : Fin 8 => constBit (K := (interp 1).K) (w1NatR y i) b := by
    funext b
    have hb8 := b.isLt
    have e1 : (8 * i + (b : ℕ)) / 8 = i := by omega
    have e2 : (8 * i + (b : ℕ)) % 8 = b := by omega
    change program.evalE (program.reader e) 1 (.leaf 70) (8 * i + b) = _
    rw [evalE_w1_honest y hr hh (by omega)]
    unfold w1BitsR
    rw [e1, e2]
  rw [hb, natOfBits_constBit]
  unfold w1NatR
  rw [dif_pos hi, Nat.mod_eq_of_lt (UInt8.toNat_lt _)]
  unfold MLDSA44.PoP.Compose.honestW1Bytes
  rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact hi)]

/-- **`c̃'` is the ring input's `c̃`** at the honest values: `H(μ ‖ w1Encode(w1)) = c̃`
(`RingIn.checks`, Algorithm 8's commitment check). -/
theorem cTildeOf_honest : cTildeOf RD = y.ctilde :=
  (cTildeOf_rounds (rounds_honest y hr hh) (inputBytes_mu_honest y hr hh)
    (inputBytes_w1_honest y hr hh)).symm.trans y.checks.2.1

/-- **The stream is the ring input's stream** `SHAKE256(c̃, 272)` at the honest values. -/
theorem sibStream_honest : sibStream RD = streamR y := by
  rw [sibStream_rounds (rounds_honest y hr hh), cTildeOf_honest y hr hh, streamR,
    MLDSA44.PoP.stream_eq]

/-- **The candidates read the ring input's candidates.** -/
theorem natOfBits_candBits (k : Fin 264) : natOfBits (candBits RD k) = candNatR y k := by
  have h := congrFun (sibStream_honest y hr hh) ⟨8 + k, by omega⟩
  exact h

/-- **The selected bytes read the input's positions.** -/
theorem jBits_honest (h557 : ∀ n < 312, castElt (b := 1) (val 556 n) = jFR (K := FH.K) y n)
    (t : Fin 39) (b : Fin 8) : jBits RD t b = constBit (y.positions t) b := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hp7, hf7, hs7⟩ := MldsaHSelHonest.sel_cells (program := program)
  have ht := t.isLt
  have hb := b.isLt
  unfold jBits
  rw [evalE_leaf, hr hp7 hf7 (by rw [hs7]; omega), h557 _ (by omega)]
  unfold jFR
  rw [dif_pos (by omega)]
  congr 2
  · exact Fin.ext (show (8 * (t : ℕ) + b) / 8 = t by omega)
  · omega

/-- **The selected bytes are the positions as naturals.** -/
theorem natOfBits_jBits (h557 : ∀ n < 312, castElt (b := 1) (val 556 n) = jFR (K := FH.K) y n)
    (t : Fin 39) : natOfBits (jBits RD t) = y.positions t := by
  rw [show jBits RD t = fun b : Fin 8 => constBit (K := (interp 1).K) (y.positions t) b from
    funext (jBits_honest y hr hh h557 t), natOfBits_constBit, Nat.mod_eq_of_lt]
  have ha := MLDSA44.acceptedCandidates_le mldsa44 y.positions_eq t
  have hb : (t : ℕ) < 39 := t.isLt
  change y.positions t ≤ 256 - 39 + (t : ℕ) at ha
  change y.positions t < 256
  omega

set_option maxRecDepth 8192 in
/-- **SampleInBall's selection predicates hold at the honest values**: the selected bytes the
input's positions (`jFR`) and the threshold words the honest low threshold bits packed (`lowFR`);
the stream is `SHAKE256(c̃)` (`sibStream_honest`), whose candidates the positions are the first
accepted ones (`RingIn.positions_eq`). -/
theorem select_core (h557 : ∀ n < 312, castElt (b := 1) (val 556 n) = jFR (K := FH.K) y n)
    (h558 : ∀ w < 99, castElt (b := 1) (val 557 w) = packWord (FH := FH) (lowFR (K := FH.K) y) w)
    {q : ℕ} (hq : q ∈ [264, 265, 266]) :
    program.HoldsWith RD (program.predicate q).body := by
  obtain ⟨hb9, hp8, hf9, hf8, hs9, hs8, hn8, hsel, he, -⟩ := MldsaHSelHonest.sel_cells (program := program)
  have hcb : ∀ k, AllBool (candBits RD k) := fun k => sibByte_bool _ _
  have hcn : (fun k => natOfBits (candBits RD k)) = candNatR y :=
    funext (natOfBits_candBits y hr hh)
  have hlow : lowThr RD = SelectFirstTau.honestLow 39 fun k => natOfBits (candBits RD k) := by
    funext k b
    have hk := k.isLt
    have hb : (b : ℕ) < 6 := b.isLt
    unfold lowThr
    have hbool : ∀ n, lowFR (K := FH.K) y n = 0 ∨ lowFR (K := FH.K) y n = 1 := fun n => by
      unfold lowFR
      split_ifs
      · exact constBit_bool _ _
      · exact Or.inl rfl
    rw [evalE_bitview hr hbool hb9 hp8 hf9 hf8 (by rw [hs9]) hs8 hn8 hsel he
      (fun w hw => by rw [← castElt_castElt_of_eq (I := interp) hf8 (val 557 w)]; exact congrArg _ (h558 w hw)) (by omega)]
    unfold lowFR SelectFirstTau.honestLow
    rw [dif_pos (by omega), hcn]
    congr 2
    · exact Fin.ext (show (6 * (k : ℕ) + b) / 6 = k by omega)
    · omega
  have hrun : SelectFirstTau.run selF 39 (candBits RD) (jBits RD) (lowThr RD) (selDelta RD) = true := by
    rw [hlow]
    refine SelectFirstTau.complete selF (by norm_num) (by decide) hcb
      (fun t b => by rw [jBits_honest y hr hh h557]; exact constBit_bool _ _) ?_ _
    rw [hcn, funext (natOfBits_jBits y hr hh h557)]
    have h := y.positions_eq
    rw [SelectFirstTau.acceptedCandidates_eq] at h
    exact h
  exact select_holds_of_run _ hrun hq

/-- **The signs are the ring input's stream's sign bits.** -/
theorem signs_honest (t : Fin (samM program F0 FH).τ) :
    (samM program F0 FH).signs e t = if sgBR program F0 FH y t then 1 else 0 := by
  rw [samM_signs]
  have ht := t.isLt
  change (t : ℕ) < 39 at ht
  have key := congrFun (MLDSA44.Native.signBoolsOf_signWires
    (fun o => sibByte_bool (program := program) (F0 := F0) (FH := FH) e o)) (Fin.cast (samM_τR program F0 FH) t)
  have hbool : signsH RD (Fin.cast (samM_τR program F0 FH) t) = 0 ∨
      signsH RD (Fin.cast (samM_τR program F0 FH) t) = 1 :=
    sibByte_bool e ⟨(t : ℕ) / 8, by omega⟩ ⟨(t : ℕ) % 8, by omega⟩
  have hsg : sgBR program F0 FH y t = decide (signsH RD (Fin.cast (samM_τR program F0 FH) t) = 1) := by
    unfold SampleInBall.signBoolsOf at key
    change _ = decide (HashCircuit.signWires (sibByte RD) (Fin.cast (samM_τR program F0 FH) t) = 1)
    rw [key]
    unfold sgBR
    rw [← sibStream_honest y hr hh]
    rfl
  rw [hsg]
  split_ifs with h1
  · exact of_decide_eq_true h1
  · rcases hbool with h | h
    · exact h
    · exact absurd (decide_eq_true h) h1

set_option maxRecDepth 8192 in
/-- **SampleInBall's memory check predicates hold at the honest values**: the selected bytes, and
the memory cells the honest trace's (`memFR`). -/
theorem mem_core (h557 : ∀ n < 312, castElt (b := 1) (val 556 n) = jFR (K := FH.K) y n)
    (hm : ∀ v, v ∈ [560, 561, 562, 563, 564, 565] → ∀ n < (program.value v).size,
      castElt (b := 1) (val v n) = memFR program F0 FH y v n)
    {q : ℕ} (hq : q ∈ [267, 268, 269, 270]) :
    program.HoldsWith RD (program.predicate q).body := by
  obtain ⟨hcell, h1, h2, h3, h4, h5, h6⟩ := MldsaHSelHonest.mem_cells (program := program)
  have rd : ∀ v, v ∈ [560, 561, 562, 563, 564, 565] → ∀ n < (program.value v).size,
      program.evalE RD 1 (.leaf v) n = memFR program F0 FH y v n := fun v hv n hn => by
    rw [evalE_leaf, hr (hcell v hv).1 (hcell v hv).2 hn]
    exact hm v hv n hn
  have hlt := fun t => (MLDSA44.acceptedCandidates_le mldsa44 y.positions_eq t)
  have hsg := signs_honest y hr hh
  have hB : SampleInBall.signBoolsOf ((samM program F0 FH).signs e) = sgBR program F0 FH y := by
    funext t
    unfold SampleInBall.signBoolsOf
    rw [hsg t]
    cases sgBR program F0 FH y t <;> simp
  have hP : (fun t => natOfBits ((samM program F0 FH).positions e t)) = posNR program F0 FH y := by
    funext t
    rw [samM_positions]
    exact natOfBits_jBits y hr hh h557 (Fin.cast (samM_τR program F0 FH) t)
  have hTr : (samM program F0 FH).honestTrace e = honestMemWR program F0 FH y := by
    unfold SampleInBall.honestTrace honestMemWR SampleInBall.signBools
    rw [hP, hB]
  have hL : samLowered e = (samM program F0 FH).honestCells e := by
    unfold samLowered SampleInBall.honestCells
    rw [hTr, SampleInBall.Lowered.mk.injEq]
    refine ⟨rfl, funext fun t => ?_, funext fun t => funext fun b => ?_, funext fun k => ?_,
      funext fun k => ?_, funext fun t => ?_, funext fun t => ?_⟩
    · have ht : (t : ℕ) < 39 := t.isLt
      rw [rd 560 (by simp) t (by rw [h1]; exact ht)]
      unfold memFR
      rw [if_pos rfl, dif_pos ht]
    · have ht : (t : ℕ) < 39 := t.isLt
      have hb : (b : ℕ) < 6 := b.isLt
      rw [rd 561 (by simp) _ (by rw [h2]; omega)]
      unfold memFR
      rw [if_neg (by decide), if_pos rfl, dif_pos (by omega)]
      have e1 : (⟨(6 * (t : ℕ) + b) / 6, by change _ < 39; omega⟩ : Fin (samM program F0 FH).τ) = t :=
        Fin.ext (by simp only; omega)
      have e2 : (⟨(6 * (t : ℕ) + b) % 6, by omega⟩ : Fin 6) = b := Fin.ext (by simp only; omega)
      rw [e1, e2]
    · have hk : (k : ℕ) < 256 := k.isLt
      rw [rd 562 (by simp) k (by rw [h3]; exact hk)]
      unfold memFR
      rw [if_neg (by decide), if_neg (by decide), if_pos rfl, dif_pos hk]
    · have hk : (k : ℕ) < 256 := k.isLt
      rw [rd 563 (by simp) k (by rw [h4]; exact hk)]
      unfold memFR
      rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl, dif_pos hk]
    · have ht : (t : ℕ) < 39 := t.isLt
      rw [rd 564 (by simp) t (by rw [h5]; exact ht)]
      unfold memFR
      rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl,
        dif_pos ht]
      change _ = MemoryShuffle.unit _ ((samM program F0 FH).signs e t)
      rw [hsg t]
      rfl
    · have ht : (t : ℕ) < 39 := t.isLt
      rw [rd 565 (by simp) t (by rw [h6]; exact ht)]
      unfold memFR
      rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
        if_neg (by decide), if_pos rfl, dif_pos ht]
  have hpz : SampleInBall.Positioned 256 ((samM program F0 FH).positions e)
      ((samM program F0 FH).signs e) := by
    refine ⟨fun t b => ?_, fun t => ?_, fun t => ?_⟩
    · rw [samM_positions, jBits_honest y hr hh h557 t b]
      exact constBit_bool _ _
    · rw [samM_positions, natOfBits_jBits y hr hh h557 t]
      exact hlt t
    · rw [hsg t]
      cases sgBR program F0 FH y t
      · exact Or.inl rfl
      · exact Or.inr rfl
  have hS : (samM program F0 FH).HonestShuffles e := by
    refine ⟨hpz, fun k => ?_⟩
    have hd := decodeRow (program := program) (F0 := F0) (FH := FH) e k
    rw [samLowered_base] at hd
    have hk : (k : ℕ) < 256 := k.isLt
    have hce : (samLowered e).cEnc k = (honestMemWR program F0 FH y).cEnc k := by
      rw [samLowered_cEnc, rd 562 (by simp) k (by rw [h3]; exact hk)]
      unfold memFR
      rw [if_neg (by decide), if_neg (by decide), if_pos rfl, dif_pos hk]
    have hsh : (samM program F0 FH).shuffle e =
        MemoryShuffle.shuffle _ _ (posNR program F0 FH y) (sgBR program F0 FH y) := by
      unfold SampleInBall.shuffle SampleInBall.shuffleOf
      rw [hP, hB]
    rw [hd, hce, honestMemWR, honestWit_cEnc, hsh]
  refine mem_holds_of_checks (program := program) (F0 := F0) (FH := FH) e ?_ (fun t ht b hb => ?_) hq
  · rw [hL]
    exact SampleInBall.checks_honestCells _ hS _
  · rw [rd 561 (by simp) _ (by rw [h2]; omega)]
    unfold memFR
    rw [if_neg (by decide), if_pos rfl, dif_pos (by omega)]
    unfold honestMemWR
    exact honestWit_origin_bool _ _ _ _ _ _

end Honest

/-! ## The core's predicates and H's decoded challenge -/

section Core

variable {program : RealizedProgram} [MldsaHHonest program] [MldsaHShuffle program]
  [MldsaHSelHonest program] {F0 FH : FieldInterp} [HField FH] [MldsaHConsts program FH]
  [MldsaHNativeData FH] (y : RingIn msgLen)

set_option hygiene false in
local notation "interp" => mldsaInterpOf F0 FH

/-- **The honest final cells encode the challenge**: SampleInBall's shuffle of the positions and
the stream's signs is the ring input's challenge (`GordieHowe.MLDSA44.PoP.challenge`). -/
theorem honestMemWR_cEnc (k : ℕ) (hk : k < 256) :
    (honestMemWR program F0 FH y).cEnc ⟨k, hk⟩ =
      MemoryShuffle.encode (samM program F0 FH).Θ (y.c (Fin.cast cdeg ⟨k, hk⟩)) := by
  rw [honestMemWR, honestWit_cEnc]
  rfl

variable {e : program.Env interp} {val : program.Valuation interp} (hr : program.ReadsCells 1 e val)
  (hh : ∀ v, coreHashB v = true → val v = hashValCore (program := program) (F0 := F0) (FH := FH) y v)
  (h557 : ∀ n < 312, castElt (b := 1) (val 556 n) = jFR (K := FH.K) y n)
  (h558 : ∀ w < 99, castElt (b := 1) (val 557 w) = packWord (FH := FH) (lowFR (K := FH.K) y) w)
  (hm : ∀ v, v ∈ [560, 561, 562, 563, 564, 565] → ∀ n < (program.value v).size,
    castElt (b := 1) (val v n) = memFR program F0 FH y v n)

set_option hygiene false in
local notation "RD" => program.reader e

include hr hm in
/-- **H's decoded challenge is the ring input's challenge's ternary bits** at the honest cells. -/
theorem chalPair_core (k : Fin 256) :
    chalPair RD k = HashCircuit.ternaryBits (K := (interp 1).K) (y.c (Fin.cast cdeg k)) := by
  obtain ⟨hcell, -, -, h3, -⟩ := MldsaHSelHonest.mem_cells (program := program)
  rw [chalPair_eq, evalE_leaf, hr (hcell 562 (by simp)).1 (hcell 562 (by simp)).2
    (by rw [h3]; exact k.isLt), hm 562 (by simp) k (by rw [h3]; exact k.isLt)]
  unfold memFR
  rw [if_neg (by decide), if_neg (by decide), if_pos rfl, dif_pos k.isLt, honestMemWR_cEnc]
  exact MemoryShuffle.decodeTernary_encode _ _ (c_ternaryR y _)

include hr hh h557 h558 hm in
/-- **Domain `H`'s core holds at the honest values**: the predicates `48 … 270` (the rounds of
`c̃'` and of the stream, SampleInBall's selection and memory check). -/
theorem hPreds_core {q : ℕ} (h48 : 48 ≤ q) (h270 : q ≤ 270) :
    program.HoldsWith RD (program.predicate q).body := by
  by_cases h : q < 264
  · have := rounds_honest y hr hh ⟨(q - 48) / 24 + 1, by omega⟩ (by simp) ⟨(q - 48) % 24, by omega⟩
    have hq : roundPred ⟨(q - 48) / 24 + 1, by omega⟩ ⟨(q - 48) % 24, by omega⟩ = q := by
      unfold roundPred
      simp only [show (q - 48) / 24 + 1 ≠ 0 by omega, if_false]
      omega
    rw [hq] at this
    exact this
  by_cases hs : q < 267
  · exact select_core y hr hh h557 h558 (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)
  · exact mem_core y hr hh h557 hm (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)

end Core

end GordieHowe.MLDSA44.Ring.Native
