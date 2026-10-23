-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Native.System.Application
public import GordieHowe.Applications.MLDSA44.PoP.Configuration
public import GordieHowe.Applications.MLDSA44.Circuits.HashStep
public import GordieHowe.Applications.MLDSA44.Circuits.NativeAlgebraHonest
public import GordieHowe.Applications.MLDSA44.System.Honest

@[expose] public section

/-!
# ML-DSA native: the honest application

The source assignment the honest prover of ML-DSA native computes from an honest input
(`GordieHowe.MLDSA44.PoP.HonestInput` at the empty context), following the C++ generators
(`lib/gordiehowe/examples/mldsa/mldsa_native.h`, `mldsa_gadgets.h`, `mldsa_hash.h`):

* **Domain H**: the message bits, the Keccak trace of the three SHAKE256 calls on the honest
  inputs (`honestStates`: the packed trace of the honest permutation inputs `honestStarts`, the
  sponge starts of the three calls), the bits of `w1Encode(w1)` (`w1 = UseHint(h, w')`), the bits
  of the selected positions and the ternary bits of the challenge `c`.
* **Domain A**: the hint bits, the challenge's support and sign bits, the canonical `w'`, the
  centered `z`, the bits of `w1Encode(w1)`, and the UseHint advice at one digit of base `T^2`
  (`UseHint.honest`: the sign, the offset and the slack).

**The honest application** (`appConstraints_honest`): on every honest input, this assignment
satisfies the application constraints (`algebraConstraints_honest`, from `signatureRows_honest`
and `useHint_honest`). On a valid honest input its `c̃'` is the input's `c̃` (`cTildeOf_honest`),
its stream bytes are the honest stream's (`sibBytes_honest`) and the selection's source holds
(`selects_honest`).

The parts ML-DSA emulated also uses are in `GordieHowe/Applications/MLDSA44/System/Honest.lean`.
-/

namespace GordieHowe.MLDSA44.Native

open IOP RealizedProgram.ProofSystem.PhaseLayout GordieHowe.Bits GordieHowe.Keccak GordieHowe.Shake256 GordieHowe.KeccakTrace GordieHowe.KeccakBatch
  GordieHowe.KeccakSponge GordieHowe.PackedClaim GordieHowe.HashCircuit Params
open _root_.MLDSA.Concrete (useHintCoeff)
open HashBatchedCircuit (nMu nCommit)

variable {KH : Type} [Field KH] [DecidableEq KH] [CharP KH 2] {msgLen : ℕ}

/-! ### Domain A -/

section Algebra

open NativeAlgebraCircuit.Honest (hintBool wCoeff zCentered)

variable {F : Type} [Field F]

variable [DecidableEq F] [CharP F _root_.MLDSA.modulus]

variable {B : PackedBasis KH 4} {y : HonestInput msgLen}

omit [DecidableEq KH] [CharP KH 2] [DecidableEq F] [CharP F _root_.MLDSA.modulus] in
/-- The honest challenge is ternary. -/
theorem c_ternary (y : HonestInput msgLen) (k : Fin N) : y.c k = 0 ∨ y.c k = 1 ∨ y.c k = -1 :=
  MLDSA44.PoP.challenge_ternary _ _ k

omit [CharP KH 2] [CharP F _root_.MLDSA.modulus] in
/-- **The honest challenge polynomial** `support - 2 sign` is the challenge's. -/
theorem cPoly_honest :
    Rows.cPoly (sigWit (honestAssignment (F := F) B y)) =
      MLDSA44.ofCoeff fun k => (y.c k : _root_.MLDSA.Coeff) := by
  unfold Rows.cPoly
  congr 1
  funext k
  change Rows.bitCoeff (HashCircuit.ternaryBits (K := F) (y.c k)).1 -
    2 * Rows.bitCoeff (HashCircuit.ternaryBits (K := F) (y.c k)).2 = _
  rcases c_ternary y k with hk | hk | hk <;>
    norm_num [hk, HashCircuit.ternaryBits, Rows.bitCoeff]

omit [CharP KH 2] in
/-- **The honest signature rows hold** (`Rows.rows_hold_of_eq`). -/
theorem signatureRows_honest :
    rowsHold (Rows.rows y.key) (sigWit (honestAssignment (F := F) B y)) := by
  apply Rows.rows_hold_of_eq (xw := wCoeff y.key y.c y.z)
    (xz := fun j k => MLDSA44.coeff (y.z.get j) k)
  · exact fun k => (ternaryBits_bool (y.c k)).1
  · exact fun k => (ternaryBits_bool (y.c k)).2
  · intro i k
    change Rows.embed (wCoeff y.key y.c y.z i k) = ((wCoeff y.key y.c y.z i k).val : F)
    conv_lhs => rw [← ZMod.natCast_zmod_val (wCoeff y.key y.c y.z i k)]
    rw [map_natCast]
  · intro j k
    change Rows.embed (MLDSA44.coeff (y.z.get j) k) = ((zCentered y.z j k : ℤ) : F)
    conv_lhs => rw [LatticeCrypto.centeredRepr_intCast (MLDSA44.coeff (y.z.get j) k)]
    rw [map_intCast]
    rfl
  · rw [cPoly_honest, NativeAlgebraCircuit.Honest.ofFn_ofCoeff_coeff]
    exact NativeAlgebraCircuit.Honest.ofFn_ofCoeff_coeff (MLDSA44.PoP.Compose.honestWApprox y.key y.c y.z)

omit [CharP KH 2] in
/-- **The honest UseHint advice passes** at coefficient `m` (`UseHint.native_complete` at one
digit of base `T^2`), with the honest output bits read from `w1Encode(w1)`
(`NativeAlgebraCircuit.Honest.outputBits_honest`). -/
theorem useHint_honest (m : Fin wDim) :
    UseHintHolds (NativeAlgebraCircuit.flat (honestAssignment (F := F) B y).h m)
      (NativeAlgebraCircuit.flat (honestAssignment (F := F) B y).w m)
      (NativeAlgebraCircuit.flat (honestAssignment (F := F) B y).np m)
      (NativeAlgebraCircuit.flat (honestAssignment (F := F) B y).offset m)
      (NativeAlgebraCircuit.flat (honestAssignment (F := F) B y).slack m)
      (NativeAlgebraCircuit.outputBits (honestAssignment (F := F) B y).w1A m) := by
  obtain ⟨hok, -⟩ := UseHint.native_complete (K := F) (γ₂ := γ₂) (B := T * T) (k := 1)
    (r := r1Bits) (by decide) (by decide) (by decide) (by decide)
    (NativeAlgebraCircuit.flat (hintBool y.h) m) (NativeAlgebraCircuit.flat (wCoeff y.key y.c y.z) m)
  obtain ⟨hle, -, hint, hdec⟩ := UseHint.native_ok_iff.mp hok
  have hbits : NativeAlgebraCircuit.outputBits (honestAssignment (F := F) B y).w1A m =
      (UseHint.honest (K := F) γ₂ (T * T) 1 r1Bits (NativeAlgebraCircuit.flat (hintBool y.h) m)
        (NativeAlgebraCircuit.flat (wCoeff y.key y.c y.z) m)).bits :=
    NativeAlgebraCircuit.Honest.outputBits_honest y.key y.c y.z y.h m
  rw [reconstruct_fin_one, reconstruct_fin_one] at hint
  rw [reconstruct_fin_one] at hdec
  rw [hbits]
  exact ⟨hle, hint, hdec⟩

omit [CharP KH 2] in
/-- **The honest algebra constraints**: the Bit checks, the signature rows and UseHint. -/
theorem algebraConstraints_honest :
    AlgebraConstraints y.key (honestAssignment (F := F) B y) where
  hBool i k := by
    change (((hintBool y.h i k).toNat : ℕ) : F) = 0 ∨ (((hintBool y.h i k).toNat : ℕ) : F) = 1
    cases hintBool y.h i k <;> simp
  cBool k t := by
    fin_cases t
    · exact (ternaryBits_bool (y.c k)).1
    · exact (ternaryBits_bool (y.c k)).2
  w1Bool := Falcon512.HashCircuit.wiresOfByteVec_allBool (K := F) fun p => (honestW1Bytes y p).toNat
  npBool i k := by
    change ((MLDSA44.useHintSign γ₂ _).toNat : F) = 0 ∨ ((MLDSA44.useHintSign γ₂ _).toNat : F) = 1
    cases MLDSA44.useHintSign γ₂ _ <;> simp
  signature := signatureRows_honest
  useHint := useHint_honest

omit [DecidableEq KH] [CharP KH 2] [DecidableEq F] [CharP F _root_.MLDSA.modulus] in
/-- An honest centered `z` coefficient is below `γ₁ - β` in magnitude (Algorithm 8's norm check). -/
theorem zCentered_natAbs_lt (hy : y.Valid) (j : Fin nCols) (k : Fin N) :
    (zCentered y.z j k).natAbs < normBound :=
  (MLDSA44.natAbs_centeredRepr_le_polyVecNorm y.z j k).trans_lt hy.checks.1

end Algebra

/-! ### The honest application -/

section App

open NativeAlgebraCircuit.Honest (hintBool wCoeff zCentered)

variable {P : Profile} {F S : Type} [Fintype KH] [Field F] [Fintype F] [DecidableEq F]
  [CharP F _root_.MLDSA.modulus] [Field S] (D : FieldData P KH F S)
  {y : HonestInput msgLen}

omit [Fintype KH] [Fintype F] in
/-- **The honest application constraints**: the honest hash and algebra constraints. -/
theorem appConstraints_honest (y : HonestInput msgLen) :
    AppConstraints D y.pk (honestAssignment (F := F) D.packing y) :=
  ⟨hashConstraints_honest D.packing y, algebraConstraints_honest⟩

omit [Fintype KH] [Fintype F] in
/-- **The honest `c̃'` is the input's `c̃`** (Algorithm 8's commitment check). -/
theorem cTildeOf_honest (hy : y.Valid) : cTildeOf D (honestAssignment (F := F) D.packing y) = y.ctilde := by
  have h := cTilde_eq_hashCommitment D (bitsAgree_honest D.packing y) (appConstraints_honest D y)
  have hc := hy.checks.2.1
  change _root_.MLDSA.Concrete.hashCommitment _ _
      (_root_.MLDSA.Concrete.w1Encode _ (MLDSA44.PoP.Native.decodeW1 (honestW1 (K := F) y))) = _ at h
  rw [decodeW1_honest, show messageOf (honestAssignment (F := F) D.packing y).msg = y.message from
    messageOf_honestMsg y] at h
  rw [← h, ← hc, List.ofFn_zero]

omit [Fintype KH] [Fintype F] in
/-- **The honest stream** is `SHAKE256(c̃, 272)`. -/
theorem sibBytes_honest (hy : y.Valid) (o : Fin sibLen) :
    natOfBits (sibBytes D (honestAssignment (F := F) D.packing y) o) =
      xofFin shake256 (y.ctilde.toList.map UInt8.toNat) sibLen o := by
  have h := (hashConstraints_honest D.packing y).sib_eq o
  change natOfBits (sibOut D.packing (honestStates D.packing y) o) = _
  rw [h]
  change xofFin shake256 (inputBytes (cTildeOut D.packing (honestAssignment (F := F) D.packing y).states))
    sibLen o = _
  rw [inputBytes_cTildeOut, cTildeOf_honest D hy]

omit [Fintype KH] [Fintype F] in
/-- **The honest stream is the input's stream** `PoP.MLDSA44.stream c̃`. -/
theorem sibStream_honest (hy : y.Valid) :
    (fun o => natOfBits (sibBytes D (honestAssignment (F := F) D.packing y) o)) =
      MLDSA44.PoP.stream y.ctilde :=
  funext fun o => by rw [sibBytes_honest D hy, MLDSA44.PoP.stream_eq]

omit [Fintype KH] [Fintype F] in
/-- **The honest selection**: the honest stream is Boolean and the selected bytes are the scan's
first accepted candidates (`HonestInput.Valid.positions`). -/
theorem selects_honest (hy : y.Valid) :
    RisingSelection.Selects (streamOf D (honestAssignment (F := F) D.packing y))
      (honestAssignment (F := F) D.packing y).j where
  streamBool i := (hashConstraints_honest D.packing y).sibOut_allBool _
  outBool t b := constBit_bool _ _
  first := by
    have h := hy.positions
    rw [← sibStream_honest D hy, SelectFirstTau.acceptedCandidates_eq] at h
    rw [funext (natOfBits_positions D hy)]
    exact h

end App

end GordieHowe.MLDSA44.Native
