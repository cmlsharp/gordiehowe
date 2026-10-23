-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.System.Application
public import GordieHowe.Applications.MLDSA44.PoP.Configuration
public import GordieHowe.Applications.MLDSA44.Circuits.HashStep
public import GordieHowe.Applications.MLDSA44.Circuits.NativeAlgebraHonest

@[expose] public section

/-!
# ML-DSA: the honest hash values and source

The honest values both ML-DSA configurations compute from an honest input (`HonestInput`): the
message and `w1` bytes (`honestMsg`, `honestW1Bytes`, `honestW1`), the packed honest Keccak trace of
the three hashes (`honestStarts`, `honestStates`) with the facts the honest provers read (chained,
Boolean, the words and digests SHAKE256's, `hashConstraints_honest`), the honest advice and source
assignment (`honestAdvice`, `honestAssignment`), and the agreement and decoding facts of the honest
application (`crossBits_honest`, `bitsAgree_honest`, `messageOf_honestMsg`, `decodeW1_honest`,
`positions_lt`, `natOfBits_positions`).
-/

namespace GordieHowe.MLDSA44.Native

open IOP RealizedProgram.ProofSystem.PhaseLayout GordieHowe.Bits GordieHowe.Keccak GordieHowe.Shake256 GordieHowe.KeccakTrace GordieHowe.KeccakBatch
  GordieHowe.KeccakSponge GordieHowe.PackedClaim GordieHowe.HashCircuit Params
open _root_.MLDSA.Concrete (useHintCoeff)
open HashBatchedCircuit (nMu nCommit)

variable {KH : Type} [Field KH] [DecidableEq KH] [CharP KH 2] {msgLen : ℕ}

/-- The honest input of ML-DSA native: the empty context. -/
abbrev HonestInput (msgLen : ℕ) : Type := MLDSA44.PoP.HonestInput 0 msgLen

/-! ### Domain H -/

/-- **The honest message bits.** -/
-- spec-side
def honestMsg (y : HonestInput msgLen) : BitWires KH (8 * msgLen) :=
  Falcon512.HashCircuit.wiresOfByteVec fun i => (y.message i).toNat

/-- **The honest `w1Encode(w1)` bytes**, `w1 = UseHint(h, w')` at the input's challenge. -/
-- spec-side
noncomputable def honestW1Bytes (y : HonestInput msgLen) : Fin 768 → UInt8 :=
  MLDSA44.PoP.Compose.honestW1Bytes y.key y.c y.z y.h

/-- **The honest `w1` bits** (H's copy and A's `hint.w1`): the bits of `w1Encode(w1)`. -/
-- spec-side
noncomputable def honestW1 {K : Type} [Field K] (y : HonestInput msgLen) : BitWires K (8 * 768) :=
  Falcon512.HashCircuit.wiresOfByteVec fun p => (honestW1Bytes y p).toNat

/-- The honest `μ` output on the honest input's bits (`HashBatchedCircuit.honestMu`). -/
-- spec-side
abbrev honestMuOf (y : HonestInput msgLen) : Fin 64 → BitWires KH 8 :=
  HashBatchedCircuit.honestMu (ctxLen := 0) (trWires y.pk) noCtx (honestMsg y)

/-- The honest `c̃'` output on the honest input's bits (`HashBatchedCircuit.honestCommit`). -/
-- spec-side
noncomputable abbrev honestCommitOf (y : HonestInput msgLen) : Fin 32 → BitWires KH 8 :=
  HashBatchedCircuit.honestCommit (ctxLen := 0) (trWires y.pk) noCtx (honestMsg y) (honestW1 y)

/-- **The honest permutation inputs** of the three calls: `μ`'s, `c̃'`'s, then the stream's absorb
and squeeze (`KeccakTrace.spongeStart` of each call's input). -/
-- spec-side
noncomputable def honestStarts (y : HonestInput msgLen) : Fin (nPerms msgLen) → State KH :=
  fun p => Fin.append
    (Fin.append (fun k : Fin (nMu 0 msgLen) =>
        spongeStart .shake256 (HashCircuit.muInput (trWires y.pk) noCtx (honestMsg y)) k)
      (fun k : Fin nCommit =>
        spongeStart .shake256 (HashCircuit.commitInput (honestMuOf y) (honestW1 y)) k))
    (fun k : Fin nSib => spongeStart .shake256 (honestCommitOf (KH := KH) y) k)
    (Fin.cast (nPerms_def msgLen) p)

omit [DecidableEq KH] [CharP KH 2] in
theorem honestStarts_mu (y : HonestInput msgLen) (k : Fin (nMu 0 msgLen)) :
    honestStarts (KH := KH) y ((muCall (msgLen := msgLen)).perm k) =
      spongeStart .shake256 (HashCircuit.muInput (trWires y.pk) noCtx (honestMsg y)) k := by
  have e : Fin.cast (nPerms_def msgLen) (muCall.perm k) = Fin.castAdd _ (Fin.castAdd _ k) :=
    Fin.ext (muCall_perm k)
  simp only [honestStarts, e, Fin.append_left]

omit [DecidableEq KH] [CharP KH 2] in
theorem honestStarts_commit (y : HonestInput msgLen) (k : Fin nCommit) :
    honestStarts (KH := KH) y ((commitCall (msgLen := msgLen)).perm k) =
      spongeStart .shake256 (HashCircuit.commitInput (honestMuOf y) (honestW1 y)) k := by
  have e : Fin.cast (nPerms_def msgLen) (commitCall.perm k) = Fin.castAdd _ (Fin.natAdd _ k) :=
    Fin.ext (commitCall_perm k)
  simp only [honestStarts, e, Fin.append_left, Fin.append_right]

omit [DecidableEq KH] [CharP KH 2] in
theorem honestStarts_sib (y : HonestInput msgLen) (k : Fin nSib) :
    honestStarts (KH := KH) y ((sibCall (msgLen := msgLen)).perm k) =
      spongeStart .shake256 (honestCommitOf (KH := KH) y) k := by
  have e : Fin.cast (nPerms_def msgLen) (sibCall.perm k) = Fin.natAdd _ k :=
    Fin.ext (sibCall_perm k)
  simp only [honestStarts, e, Fin.append_right]

omit [CharP KH 2] in
theorem honestStarts_allBool (y : HonestInput msgLen) (p : Fin (nPerms msgLen)) (x y' : Fin 5) :
    AllBool (honestStarts (KH := KH) y p x y') := by
  have hmuIn : ∀ i, AllBool (HashCircuit.muInput (trWires y.pk) noCtx (honestMsg (KH := KH) y) i) :=
    HashCircuit.muInput_allBool (Falcon512.HashCircuit.wiresOfByteVec_allBool _)
      (fun i : Fin (8 * 0) => Fin.elim0 i) (Falcon512.HashCircuit.wiresOfByteVec_allBool _)
  have hmu : ∀ j, AllBool (honestMuOf (KH := KH) y j) :=
    squeezeOut_allBool fun k x y => keccakF_allBool (spongeStart_allBool hmuIn _) x y
  have hcomIn : ∀ i, AllBool (HashCircuit.commitInput (honestMuOf (KH := KH) y) (honestW1 y) i) :=
    HashCircuit.commitInput_allBool hmu (Falcon512.HashCircuit.wiresOfByteVec_allBool _)
  have hcom : ∀ j, AllBool (honestCommitOf (KH := KH) y j) :=
    squeezeOut_allBool fun k x y => keccakF_allBool (spongeStart_allBool hcomIn _) x y
  revert x y'
  obtain ⟨q, rfl⟩ : ∃ q, p = Fin.cast (nPerms_def msgLen).symm q :=
    ⟨Fin.cast (nPerms_def msgLen) p, by simp only [Fin.cast_cast, Fin.cast_eq_self]⟩
  simp only [honestStarts, Fin.cast_cast, Fin.cast_eq_self]
  refine Fin.addCases (fun q => ?_) (fun k => ?_) q
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) q
    · rw [Fin.append_left, Fin.append_left]
      exact spongeStart_allBool hmuIn _
    · rw [Fin.append_left, Fin.append_right]
      exact spongeStart_allBool hcomIn _
  · rw [Fin.append_right]
    exact spongeStart_allBool hcom _

omit [DecidableEq KH] [CharP KH 2] in
/-- **The honest inputs chain**: the stream's squeeze, the only unhooked permutation, starts at
Keccak-f of the stream's absorb (`spongeStart_succ_of_le`). -/
theorem honestStarts_chained (y : HonestInput msgLen) :
    Chained (ghShape msgLen) (honestStarts (KH := KH) y) := by
  intro p hp hnh
  have hp2 : p + 1 = nPerms msgLen - 1 := by
    rw [ghShape_hooked_iff] at hnh
    simp only at hnh
    omega
  have hpn := nPerms_eq_add (msgLen := msgLen)
  have e1 : (⟨p + 1, hp⟩ : Fin (nPerms msgLen)) = (sibCall (msgLen := msgLen)).perm ⟨1, by decide⟩ :=
    Fin.ext (by rw [sibCall_perm]; change p + 1 = nMu 0 msgLen + 7 + 1; omega)
  have e0 : (⟨p, by omega⟩ : Fin (nPerms msgLen)) = (sibCall (msgLen := msgLen)).perm ⟨0, by decide⟩ :=
    Fin.ext (by rw [sibCall_perm]; change p = nMu 0 msgLen + 7 + 0; omega)
  rw [e1, e0, honestStarts_sib, honestStarts_sib]
  exact spongeStart_succ_of_le (by decide)

/-- **The honest Keccak trace words** (`h2c.*.states`): the packed honest trace.

Running time: `nPerms msgLen` Keccak-f permutations of `24` rounds on bit states, then `16` packing
sums for each of the `100 nStates` words. This running time is argued here, not proved in Lean. -/
-- spec-side
noncomputable def honestStates (B : PackedBasis KH 4) (y : HonestInput msgLen) : Words KH msgLen :=
  packStates B (KeccakBatch.trace (ghShape msgLen) (honestStarts y))

/-- The words of a state of the honest trace are its packed lane words. -/
theorem stateWords_honestStates (B : PackedBasis KH 4) (y : HonestInput msgLen)
    (t : Fin (nStates msgLen)) (x y' : Fin 5) (c : Fin 4) :
    KeccakOperands.stateWords (honestStates B y) t x y' c =
      KeccakHook.packLane B (KeccakBatch.trace (ghShape msgLen) (honestStarts y) t x y') c :=
  stateWords_packStates B (fun x y' => trace_allBool (honestStarts_allBool y) t x y') x y' c

/-- The decoded honest trace is the trace. -/
theorem statesOf_honestStates (B : PackedBasis KH 4) (y : HonestInput msgLen) :
    statesOf B (honestStates B y) = KeccakBatch.trace (ghShape msgLen) (honestStarts y) :=
  statesOf_packStates B (fun t x y' => trace_allBool (honestStarts_allBool y) t x y')

/-- **The honest `μ` output** is `HashBatchedCircuit.honestMu`'s. -/
theorem muOut_honestStates (B : PackedBasis KH 4) (y : HonestInput msgLen) :
    muOut B (honestStates B y) = honestMuOf y := by
  unfold muOut
  rw [statesOf_honestStates, endOf_trace]
  exact congrArg squeezeOut (funext fun k => congrArg keccakF (honestStarts_mu y k))

/-- **The honest `c̃'` output** is `HashBatchedCircuit.honestCommit`'s. -/
theorem cTildeOut_honestStates (B : PackedBasis KH 4) (y : HonestInput msgLen) :
    cTildeOut B (honestStates B y) = honestCommitOf y := by
  unfold cTildeOut
  rw [statesOf_honestStates, endOf_trace]
  exact congrArg squeezeOut (funext fun k => congrArg keccakF (honestStarts_commit y k))

/-- **The honest hash constraints**: the honest trace words lie in the subfield, the message and
`w1` bits are bits, the word-level absorbs hold (`wordAbsorb_complete`) and the Keccak batch
relation holds (`trace_rounds`). -/
theorem hashConstraints_honest (B : PackedBasis KH 4) (y : HonestInput msgLen) :
    HashConstraints B (trWires y.pk) (honestMsg y) (honestW1 y) (honestStates B y) where
  words v := packStates_mem B _ v
  msgBool := Falcon512.HashCircuit.wiresOfByteVec_allBool _
  w1Bool := Falcon512.HashCircuit.wiresOfByteVec_allBool _
  absorb :=
    { mu := wordAbsorb_complete (start := honestStarts y) (fun k => honestStarts_mu y k)
        (fun p x y' q => by
          rw [hookWords, stateWords_honestStates, trace_startState (honestStarts_chained y)])
        (fun p x y' q => by rw [outWords, stateWords_honestStates, trace_endState])
      cTilde := by
        rw [muOut_honestStates]
        exact wordAbsorb_complete (start := honestStarts y) (fun k => honestStarts_commit y k)
          (fun p x y' q => by
            rw [hookWords, stateWords_honestStates, trace_startState (honestStarts_chained y)])
          (fun p x y' q => by rw [outWords, stateWords_honestStates, trace_endState])
      sib := by
        rw [cTildeOut_honestStates]
        exact wordAbsorb_complete (start := honestStarts y) (fun k => honestStarts_sib y k)
          (fun p x y' q => by
            rw [hookWords, stateWords_honestStates, trace_startState (honestStarts_chained y)])
          (fun p x y' q => by rw [outWords, stateWords_honestStates, trace_endState]) }
  keccak := by
    refine (KeccakOperands.holds_iff _ (keccakGroups_le (msgLen := msgLen)) _).mpr ?_
    change (stateMap (ghShape msgLen)).Rounds roundIndex (statesOf B (honestStates B y))
    rw [statesOf_honestStates]
    exact trace_rounds (honestStarts_allBool y) (honestStarts_chained y)

/-! ### Domain A -/

section Algebra

open NativeAlgebraCircuit.Honest (hintBool wCoeff zCentered)

variable {F : Type} [Field F]

/-- **The honest UseHint advice** of coefficient `(i, k)` (`mldsa_gadgets.h:381-401`, the relation at `:402-428`): the sign,
the offset and the slack as one digit of base `T^2` each, and the output bits
(`UseHint.honest`). -/
-- spec-side
noncomputable def honestAdvice (y : HonestInput msgLen) (i : Fin nRows) (k : Fin N) :
    UseHint.Advice F 1 r1Bits :=
  UseHint.honest γ₂ (T * T) 1 r1Bits (hintBool y.h i k) (wCoeff y.key y.c y.z i k)

/-- **The honest source assignment** of an honest input: the message bits, the honest trace, the
bits of `w1Encode(w1)` (both copies), the bits of the selected positions, the ternary bits of the
challenge (both copies), the hint bits, the canonical `w'`, the centered `z` and the UseHint
advice.

Running time: that of `honestStates` (`nPerms msgLen` Keccak-f permutations), one evaluation of
`computeWApprox` (`k l` NTT products), and `O(k N)` UseHint advice computations on naturals
below `q`. This running time is argued here, not proved in Lean. -/
-- spec-side
noncomputable def honestAssignment (B : PackedBasis KH 4) (y : HonestInput msgLen) : Source KH F msgLen where
  msg := honestMsg y
  states := honestStates B y
  w1H := honestW1 y
  j t b := constBit (y.positions t) b
  chalH k := HashCircuit.ternaryBits (y.c k)
  h i k := ((hintBool y.h i k).toNat : F)
  cA k := ![(HashCircuit.ternaryBits (y.c k)).1, (HashCircuit.ternaryBits (y.c k)).2]
  w i k := ((wCoeff y.key y.c y.z i k).val : F)
  z j k := (zCentered y.z j k : F)
  w1A := honestW1 y
  np i k := (honestAdvice y i k).s
  offset i k := (honestAdvice y i k).lo 0
  slack i k := (honestAdvice y i k).hi 0

omit [DecidableEq KH] [CharP KH 2] in
/-- The ternary bits are bits. -/
theorem ternaryBits_bool {K : Type} [Field K] (z : ℤ) :
    ((HashCircuit.ternaryBits (K := K) z).1 = 0 ∨ (HashCircuit.ternaryBits (K := K) z).1 = 1) ∧
      ((HashCircuit.ternaryBits (K := K) z).2 = 0 ∨ (HashCircuit.ternaryBits (K := K) z).2 = 1) := by
  unfold HashCircuit.ternaryBits
  constructor <;> split_ifs <;> simp

variable [DecidableEq F] [CharP F _root_.MLDSA.modulus]

omit [DecidableEq KH] [CharP KH 2] [DecidableEq F] [CharP F _root_.MLDSA.modulus] in
/-- A reconstruction from one digit is the digit. -/
theorem reconstruct_fin_one (B : ℕ) (f : Fin 1 → F) : Range.reconstruct B (List.ofFn f) = f 0 := by
  simp [Range.reconstruct]

end Algebra

/-! ### The honest application -/

section App

open NativeAlgebraCircuit.Honest (hintBool wCoeff zCentered)

variable {P : Profile} {F S : Type} [Fintype KH] [Field F] [Fintype F] [DecidableEq F]
  [CharP F _root_.MLDSA.modulus] [Field S] (D : FieldData P KH F S)
  {y : HonestInput msgLen}

omit [DecidableEq KH] [CharP KH 2] [Fintype KH] [Fintype F] [DecidableEq F]
  [CharP F _root_.MLDSA.modulus] in
/-- **A crossing bit of the honest assignment** is the same bit in both fields: bit `t` of
`w1Encode(w1)`, or a ternary bit of the challenge. -/
theorem crossBits_honest (y : HonestInput msgLen) (t : Fin (P.macWidth * P.nch)) :
    ∃ b : Bool, HashCircuit.crossBits (mw := P.macWidth) (honestW1 (K := KH) y)
        (HashCircuit.cBits fun k => HashCircuit.ternaryBits (y.c k)) t = cond b 1 0 ∧
      HashCircuit.crossBits (mw := P.macWidth) (honestW1 (K := F) y)
        (HashCircuit.cBits fun k => HashCircuit.ternaryBits (y.c k)) t = cond b 1 0 := by
  unfold HashCircuit.crossBits
  split_ifs with ht
  · refine ⟨((honestW1Bytes y ⟨t / 8, by omega⟩).toNat).testBit (t % 8), ?_, ?_⟩ <;>
    · change Bits.constBit _ _ = _
      rw [SelectFirstTau.constBit_eq_ite_testBit]
      cases ((honestW1Bytes y ⟨t / 8, by omega⟩).toNat).testBit (t % 8) <;> rfl
  · unfold HashCircuit.cBits HashCircuit.ternaryBits
    split_ifs with hp
    · refine ⟨!decide (y.c ⟨(t - 8 * 768) / 2, ?_⟩ = 0), ?_, ?_⟩
      · have := t.isLt
        have hcov : P.macWidth * P.nch = 6656 := HashCircuit.cover (mw := P.macWidth)
        change _ < 256
        omega
      all_goals
        dsimp only
        split_ifs with hz <;> simp [hz]
    · refine ⟨decide (y.c ⟨(t - 8 * 768) / 2, ?_⟩ = -1), ?_, ?_⟩
      · have := t.isLt
        have hcov : P.macWidth * P.nch = 6656 := HashCircuit.cover (mw := P.macWidth)
        change _ < 256
        omega
      all_goals
        dsimp only
        split_ifs with hz <;> simp [hz]

omit [Fintype KH] [Fintype F] [DecidableEq F] [CharP F _root_.MLDSA.modulus] [CharP KH 2] in
/-- **The crossings of the honest assignment agree.** -/
theorem bitsAgree_honest (B : PackedBasis KH 4) (y : HonestInput msgLen) :
    BitsAgree (xhOf P (honestAssignment (F := F) B y)) (xaOf P (honestAssignment (F := F) B y)) := by
  have h := fun (c : Fin P.nch) (j : Fin P.macWidth) => crossBits_honest (P := P) (KH := KH) (F := F) y
    ⟨P.macWidth * c + j, MAC.chunk_index_lt c.isLt j.isLt⟩
  have hx : ∀ c j, ∃ b : Bool, xhOf P (honestAssignment (F := F) B y) c j = cond b 1 0 ∧
      xaOf P (honestAssignment (F := F) B y) c j = cond b 1 0 := fun c j => by
    obtain ⟨b, h1, h2⟩ := h c j
    exact ⟨b, h1, h2⟩
  refine ⟨fun c j => ?_, fun c j => ?_, fun c j => ?_⟩ <;> obtain ⟨b, h1, h2⟩ := hx c j
  · rw [h1]
    cases b <;> simp
  · rw [h2]
    cases b <;> simp
  · rw [h1, h2]
    cases b <;> simp

omit [Fintype KH] [Fintype F] [DecidableEq F] [CharP F _root_.MLDSA.modulus] [CharP KH 2] in
/-- The honest message bits read back the message. -/
theorem messageOf_honestMsg (y : HonestInput msgLen) :
    messageOf (honestMsg (KH := KH) y) = y.message := by
  funext i
  rw [messageOf, honestMsg, Falcon512.HashCircuit.natOfBits_byteWires_wiresOfByteVec
    (fun i => UInt8.toNat_lt _) i]
  exact UInt8.ofNat_toNat

omit [Fintype KH] [Fintype F] [DecidableEq KH] [CharP KH 2] [CharP F _root_.MLDSA.modulus] in
/-- **The extracted `w1` of the honest bits is `UseHint(h, w')`.** -/
theorem decodeW1_honest (y : HonestInput msgLen) :
    MLDSA44.PoP.Native.decodeW1 (honestW1 (K := F) y) =
      MLDSA44.PoP.Compose.honestW1 y.key y.c y.z y.h := by
  unfold MLDSA44.PoP.Native.decodeW1 MLDSA44.PoP.Compose.honestW1
  refine congrArg Vector.ofFn (funext fun i => congrArg MLDSA44.ofCoeff (funext fun k => ?_))
  rw [NativeAlgebraCircuit.w1Coeff, honestW1, honestW1Bytes, NativeAlgebraCircuit.Honest.outputBits_honest,
    NativeAlgebraCircuit.flat_apply,
    NativeAlgebraCircuit.flat_apply, Bits.natOfBits_constBit, Nat.mod_eq_of_lt
      ((MLDSA44.useHintCoeff_lt (by decide) (by decide) _ _).trans (by decide))]
  rfl

omit [DecidableEq KH] [CharP KH 2] [Fintype KH] [Fintype F] [DecidableEq F]
  [CharP F _root_.MLDSA.modulus] in
/-- The honest positions are bytes. -/
theorem positions_lt (hy : y.Valid) (t : Fin τ) : y.positions t < 2 ^ 8 :=
  (MLDSA44.acceptedCandidates_le mldsa44 hy.positions t).trans_lt (by
    have := t.isLt
    change (t : ℕ) < 39 at this
    change 256 - 39 + (t : ℕ) < 256
    omega)

omit [Fintype KH] [Fintype F] [CharP KH 2] [DecidableEq F] [CharP F _root_.MLDSA.modulus] in
/-- The bits of the honest positions read back the positions. -/
theorem natOfBits_positions (hy : y.Valid) (t : Fin τ) :
    natOfBits ((honestAssignment (F := F) D.packing y).j t) = y.positions t := by
  change natOfBits (fun b : Fin 8 => constBit (K := KH) (y.positions t) b) = _
  rw [natOfBits_constBit, Nat.mod_eq_of_lt (positions_lt hy t)]

end App

end GordieHowe.MLDSA44.Native
