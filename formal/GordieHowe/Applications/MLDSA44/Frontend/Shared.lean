-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Native.System.Application
public import GordieHowe.Applications.FieldInterps.Basic
public import GordieHowe.Language.RealizedProgram.OpsLemmas
public import GordieHowe.Language.Library.Eval
public import GordieHowe.Language.RealizedProgram.Encoding

@[expose] public section

/-!
# GordieHowe frontend: ML-DSA facts for the theorem at the realized program

General facts the `MLDSA44.Native.ROMParams` frontend uses that belong next to other objects (the
ML-DSA specification, the evaluation library), kept here until they move:

* `GordieHowe.MLDSA44.verifiesBytes_of_parts`: `sigEncode(c̃, z, h)` verifies when `ExpandA`
  finishes within the byte budget, the challenge is the fixed-stream `SampleInBall` of `c̃`'s stream,
  `w1 = UseHint(h, computeWApprox(Â, c, z, t1))`, `c̃` is the commitment hash of `μ` and
  `w1Encode(w1)`, and the norm and hint-weight checks pass (stated on the
  verifier's parts; belongs in `GordieHowe/Applications/MLDSA44/Spec/Encoding.lean`).
* `GordieHowe.RealizedProgram.gf128_toNat_injective`: the integer reading of `GF(2^128)` is injective (belongs in
  `GordieHowe/Applications/FieldInterps/Basic.lean`).
* `Ops.eqReduce_eq_fst`, `Ops.eqWord_eq_eqConst`, `Ops.leqWord_eq_leConst`: on bits, `Logic::eq`
  and `Logic::leq` against a constant's bits are the gadget library's `Bits.eqConst` and
  `Bits.leConst` (belong in `GordieHowe/Language/RealizedProgram/OpsLemmas.lean`, next to `Ops.ltWord_eq_ltConst`).
* `GordieHowe.RealizedProgram.evalE_logic`, `GordieHowe.RealizedProgram.evalIntWith_logic`: one step of evaluation of a Logic builder of
  two arguments (belong in `GordieHowe/Language/Library/Eval.lean`).
* `GordieHowe.RealizedProgram.xorSel`: the `XOR` of basis constants over a natural's set bits (its decoding is
  `decode_xorSel`, `GordieHowe/Applications/MLDSA44/Frontend/HField.lean`).
* `IndexMap.entry_flatMap_range`, `IndexMap.entry_rep`: the entries of a repeated pattern, read
  per repetition (belong in `GordieHowe/Language/Library/Eval.lean`, next to the index-map
  lemmas); deciding a repeated map entry by entry exhausts the kernel.
-/

namespace GordieHowe.MLDSA44

open _root_.MLDSA.Concrete (sigEncode useHintCoeff)

/-- **The serialized verifier from FIPS 204 Algorithm 8's parts**: at a key whose `ExpandA`
finishes within the byte budget (`ExpandAWithin`), with `c` the fixed-stream `SampleInBall` of `SHAKE256(c̃)` (`C ≤ 264` candidates),
`W = computeWApprox(Â, c, z, t1)`, `w1 = UseHint(h, W)`, `c̃` the commitment hash of
`μ = H(tr ‖ frame([], msg))` and `w1Encode(w1)`, `‖z‖∞ < γ₁ − β` and the hint weight at most `ω`,
`MLDSA44.VerifiesBytes` holds for `sigEncode(c̃, z, h)` at the empty context. -/
theorem verifiesBytes_of_parts {C : ℕ} {pk : PublicKey44} {msg : List UInt8}
    {cTilde : _root_.MLDSA.CommitHashBytes _root_.MLDSA.mldsa44} {c : Fin mldsa44.N → ℤ}
    {z W : _root_.MLDSA.RqVec _root_.MLDSA.mldsa44.l}
    {h : Vector _root_.MLDSA.Concrete.Hint _root_.MLDSA.mldsa44.k}
    {w1 : Vector _root_.MLDSA.Concrete.High _root_.MLDSA.mldsa44.k}
    (hC : C ≤ _root_.MLDSA.Concrete.sampleInBallCandidateBudget) (hexp : ExpandAWithin _root_.MLDSA.mldsa44 pk.rho)
    (hball : fixedStreamChallenge mldsa44
      (xofFin GordieHowe.shake256 (cTilde.toList.map UInt8.toNat) (C + 8)) = some c)
    (hW : _root_.MLDSA.computeWApprox _root_.MLDSA.mldsa44 Native.Rows.prims
      (nttOps := _root_.MLDSA.Concrete.concreteNTTRingOps) (Native.Rows.aHat pk)
      (ofCoeff fun k => (c k : _root_.MLDSA.Coeff)) z pk.t1 = W)
    (huse : Native.Rows.prims.useHintVec h W = w1)
    (hcommit : _root_.MLDSA.Concrete.hashCommitment _root_.MLDSA.mldsa44
      (_root_.MLDSA.Concrete.hashMessage (Native.Rows.prims.hashPublicKey pk.rho pk.t1)
        (frame [] msg))
      (_root_.MLDSA.Concrete.w1Encode _root_.MLDSA.mldsa44 w1) = cTilde)
    (hnorm : ∀ j k,
      (LatticeCrypto.centeredRepr ((z.get j).get k)).natAbs < mldsa44.normBound)
    (hwt : Native.Rows.prims.hintWeight h ≤ _root_.MLDSA.mldsa44.omega) :
    VerifiesBytes pk [] msg (sigEncode _root_.MLDSA.mldsa44 cTilde z h) := by
  have hball? := fixedStreamChallenge_agree hC hball
  have hball' := fixedStreamChallenge_agree_prims hC hball
  have hverify : Verifies pk (frame [] msg) ⟨cTilde, z, h⟩ := by
    refine ⟨hexp, by rw [hball?]; rfl, ?_⟩
    unfold verifyChecks
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨polyVecNorm_lt hnorm (by decide), ?_⟩, hwt⟩
    erw [hball', hW, huse]
    exact hcommit
  exact extract_accepted_signature (by simp) hverify

end GordieHowe.MLDSA44

namespace GordieHowe.RealizedProgram

/-- **The integer reading of `GF(2^128)` is injective** (the polynomial-basis bits as a
`BitVec 128`). -/
theorem gf128_toNat_injective : Function.Injective gf128.toNat := fun _ _ h => BitVec.eq_of_toNat_eq h

namespace Ops

variable {R : Type*} [CommRing R]

/-- **The OR tree of two bits** is their `lor`. -/
theorem orTree_two (a : ℕ → R) (i0 : ℕ) : orTree a 2 i0 = lor (a i0) (a (i0 + 1)) := by
  rw [orTree.eq_3]
  simp [orTree.eq_2]

/-- **`eq_reduce` is the first component of `lt_reduce`.** -/
theorem eqReduce_eq_fst (a b : ℕ → R) (n : ℕ) : ∀ i0, eqReduce a b n i0 = (ltReduce a b n i0).1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i0
    rcases n with _ | _ | n
    · simp [eqReduce.eq_1, ltReduce.eq_1]
    · simp [eqReduce.eq_2, ltReduce.eq_2]
    · rw [eqReduce.eq_3, ltReduce.eq_3, ih _ (by omega), ih _ (by omega), mul_comm]

variable {K : Type*} [Field K] [DecidableEq K]

/-- The window of a word's bits at `0` is the word's natural. -/
theorem winNat_zero_eq_natOfBits {w : ℕ} (a : ℕ → K) :
    winNat a 0 w = Bits.natOfBits (fun t : Fin w => a t) := by
  simp only [winNat, Bits.natOfBits, Nat.zero_add,
    Fin.sum_univ_eq_sum_range (fun t => if a t = 1 then 2 ^ t else 0) w]

/-- **`a = c` on a word of `w` bits against the constant `c`** (`Logic::eq` with the constant's
bits) is `Bits.eqConst`, when the word's bits are `0` or `1` and `c < 2^w`. -/
theorem eqWord_eq_eqConst {w c : ℕ} {a : ℕ → K} (ha : ∀ t < w, a t = 0 ∨ a t = 1)
    (hc : c < 2 ^ w) :
    eqWord w a (fun t => Bits.constBit c t) = Bits.eqConst (fun t : Fin w => a t) c := by
  have hab : ∀ t < w, Bits.constBit (K := K) c (0 + t) = 0 ∨ Bits.constBit (K := K) c (0 + t) = 1 :=
    fun t _ => Bits.constBit_bool c _
  rw [eqWord, eqReduce_eq_fst, ltReduce_eq w 0 (fun t ht => by simpa using ha t ht) hab,
    winNat_constBit, Nat.mod_eq_of_lt hc, Bits.eqConst_eq (fun t => ha t t.isLt), Nat.mod_eq_of_lt hc,
    winNat_zero_eq_natOfBits]

/-- **`a ≤ c` on a word of `w` bits against the constant `c`** (`Logic::leq` with the constant's
bits) is `Bits.leConst`, when the word's bits are `0` or `1` and `c < 2^w`. -/
theorem leqWord_eq_leConst {w c : ℕ} {a : ℕ → K} (ha : ∀ t < w, a t = 0 ∨ a t = 1)
    (hc : c < 2 ^ w) :
    leqWord w a (fun t => Bits.constBit c t) = Bits.leConst (fun t : Fin w => a t) c := by
  have hab : ∀ t < w, Bits.constBit (K := K) c (0 + t) = 0 ∨ Bits.constBit (K := K) c (0 + t) = 1 :=
    fun t _ => Bits.constBit_bool c _
  rw [leqWord, ltWord, ltReduce_eq w 0 hab (fun t ht => by simpa using ha t ht),
    winNat_constBit, Nat.mod_eq_of_lt hc, Bits.leConst_eq (fun t => ha t t.isLt),
    winNat_zero_eq_natOfBits]
  split_ifs with h1 h2 h2 <;> first | rfl | omega | simp

/-- **`a ≤ b` on two words of `w` bits** (`Logic::leq`) is the gadget library's `Bits.leVar`, when
both words' bits are `0` or `1`. -/
theorem leqWord_eq_leVar {w : ℕ} {a b : ℕ → K} (ha : ∀ t < w, a t = 0 ∨ a t = 1)
    (hb : ∀ t < w, b t = 0 ∨ b t = 1) :
    leqWord w a b = Bits.leVar (fun t : Fin w => a t) (fun t : Fin w => b t) := by
  rw [leqWord, ltWord, ltReduce_eq w 0 (fun t ht => by simpa using hb t ht)
    (fun t ht => by simpa using ha t ht), winNat_zero_eq_natOfBits, winNat_zero_eq_natOfBits,
    Bits.leVar_eq (fun t => ha t t.isLt) (fun t => hb t t.isLt)]
  split_ifs with h1 h2 h2 <;> first | rfl | omega | simp

end Ops

namespace IndexMap

/-- **The size of a repetition of maps of one size.** -/
theorem size_flatMap_range {c : ℕ} (f : ℕ → IndexMap) (hf : ∀ j, size (f j) = c) :
    ∀ n, size ((List.range n).flatMap f) = c * n
  | 0 => by simp [size]
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append, size_append, size_flatMap_range f hf n,
      List.flatMap_singleton, hf, Nat.mul_succ]

/-- **Entry `c j + t` of a repetition of maps of size `c`** is entry `t` of repetition `j`. -/
theorem entry_flatMap_range {c : ℕ} (f : ℕ → IndexMap) (hf : ∀ j, size (f j) = c) :
    ∀ {n j t : ℕ}, j < n → t < c → entry ((List.range n).flatMap f) (c * j + t) = entry (f j) t
  | 0, _, _, hj, _ => absurd hj (Nat.not_lt_zero _)
  | n + 1, j, t, hj, ht => by
    rw [List.range_succ, List.flatMap_append, entry_append, size_flatMap_range f hf n,
      List.flatMap_singleton]
    by_cases hjn : j < n
    · rw [if_pos (by nlinarith), entry_flatMap_range f hf hjn ht]
    · have hjn' : j = n := by omega
      subst hjn'
      rw [if_neg (by omega), Nat.add_sub_cancel_left]

/-- **Entry `c j + t` of a repeated pattern of size `c`** (`IdxSeg.rep pat k`, the per-repetition
size not growing) is entry `t` of repetition `j`. -/
theorem entry_rep {pat : List RepRun} {k c : ℕ}
    (hc : ∀ j, size (pat.map fun p => IdxSeg.shift j p.base p.delta) = c) {j t : ℕ} (hj : j < k)
    (ht : t < c) :
    entry (IndexMap.ofSegs [.rep pat k]) (c * j + t) =
      entry (pat.map fun p => IdxSeg.shift j p.base p.delta) t := by
  have h : IndexMap.ofSegs [.rep pat k] =
      (List.range k).flatMap fun j => pat.map fun p => IdxSeg.shift j p.base p.delta := by
    simp [IndexMap.ofSegs, IdxSeg.expand]
  rw [h]
  exact entry_flatMap_range _ hc hj ht

/-- **An index map's entries from its list of entries**: where the entries are `f 0, …, f (n − 1)`,
entry `i < n` is `f i` (decide the list once, rather than each entry, which walks the runs). -/
theorem entry_of_toList {m : IndexMap} {f : ℕ → ℕ} {n : ℕ} (h : m.toList = (List.range n).map f)
    {i : ℕ} (hi : i < n) : m.entry i = f i := by
  rw [entry_eq_getD_toList, h, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
    List.getElem_range]

end IndexMap

section

variable {ir : RealizedProgram} {I : Interp}

/-- **A Logic builder of two arguments**: coordinate `i` is the builder on the words
`i w, …, i w + w − 1` of the arguments' coordinates. -/
theorem evalE_logic (rd : ir.Valuation I) (f : ℕ) (op : LogicOp) (w : ℕ) (a b : Expr) (i : ℕ) :
    ir.evalE rd f (.logic op w [a, b]) i = op.eval w [ir.evalE rd f a, ir.evalE rd f b] i := rfl

/-- **A Logic builder of one argument**: coordinate `i` is the builder on the word
`i w, …, i w + w − 1` of the argument's coordinates. -/
theorem evalE_logic₁ (rd : ir.Valuation I) (f : ℕ) (op : LogicOp) (w : ℕ) (a : Expr) (i : ℕ) :
    ir.evalE rd f (.logic op w [a]) i = op.eval w [ir.evalE rd f a] i := rfl

/-- **A Logic builder of two arguments on the integers**. -/
theorem evalIntWith_logic (rd : ir.Valuation I) (d : ℕ) (op : LogicOp) (w : ℕ) (a b : Expr)
    (i : ℕ) : ir.evalIntWith rd d (.logic op w [a, b]) i =
      op.eval w [ir.evalIntWith rd d a, ir.evalIntWith rd d b] i := rfl

end

/-! ## `GF(2^128)` constants as `XOR`s of basis constants -/

/-- **The `XOR` of the constants `c u` over the set bits `u < 8` of `v`** (on naturals). -/
def xorSel (v : ℕ) (c : ℕ → ℕ) : ℕ :=
  (List.range 8).foldl (fun acc u => acc ^^^ (if v.testBit u then c u else 0)) 0

end GordieHowe.RealizedProgram
