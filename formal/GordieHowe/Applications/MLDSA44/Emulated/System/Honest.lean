-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Emulated.System.Algebra
public import GordieHowe.Applications.MLDSA44.System.MAC
public import GordieHowe.Applications.MLDSA44.System.Application
public import GordieHowe.Applications.MLDSA44.System.Honest

@[expose] public section

/-!
# ML-DSA emulated: the honest application

The source assignment the honest prover of ML-DSA emulated computes from an honest input
(`GordieHowe.MLDSA44.PoP.HonestInput` at the empty context), following the C++ generators
(`lib/gordiehowe/examples/mldsa/mldsa_emulated.h`, `mldsa_gadgets.h`, `mldsa_hash.h`, `mod.h`):

* **Domain H** and the crossing bits: ML-DSA native's (`GordieHowe.MLDSA44.Native.honestAssignment`: the message
  bits, the Keccak trace of the three SHAKE256 calls, the bits of `w1Encode(w1)` in both domains,
  the bits of the selected positions, the ternary bits of the challenge in both domains, the hint
  bits).
* **Domain A**: `signature.w` the canonical `w'` (the natural below `q`, `host::w_prime`), `z` the
  centered integer cast into the field (`p - |z|` below zero in Goldilocks, as
  `mldsa_emulated.h:269-283`, `mldsa_witness`), the UseHint advice at one digit of base `T^2`
  (`honestAdvice`: `UseHint.honest γ₂ (T^2) 1 r1Bits`, the sign, the offset and the slack;
  `mldsa_gadgets.h:381-401`), and the quotient digits of the signature relation: the base-`645`
  digits of the honest quotient `(sigInt - q qlo) / q` (`honestQuot`; `mod.h:541-650`,
  `committed_digits`, the digit generator at `:617-633`), which reads the key.

**The honest algebra constraints** (`algebraConstraints_honest`): on every valid honest input, this
assignment satisfies domain A's algebra constraints: the signature relation's committed-digit rows
(`sigRow_honest`, from the congruence `congruent_honest` and the quotient digits
`honestQuot_spec`, `honestQuot_lt`) and UseHint with the wrap (`useHint_honest`).

The honest facts of domain H are native's (`GordieHowe.MLDSA44.Native.cTildeOf_honest`,
`GordieHowe.MLDSA44.Native.sibBytes_honest`, `GordieHowe.MLDSA44.Native.selects_honest`).
-/

namespace GordieHowe.MLDSA44.Emulated

open IOP RealizedProgram.ProofSystem.PhaseLayout GordieHowe.Bits Params Range
open Native.Params (q N nRows nCols τ γ₂ r1Bits normBound normOffset normHonest wDim nSamples)
open NativeAlgebraCircuit.Honest (hintBool wCoeff zCentered)
open GordieHowe.MLDSA44.Native (HonestInput honestMsg honestStates honestW1 honestW1Bytes hashConstraints_honest FieldData Statement xhOf xaOf sibBytes signsOf streamOf cTildeOf messageOf sibLen)
open Rows (aKeyOf tKeyOf signedZ zVec Congruent)

variable {KH : Type} [Field KH] [DecidableEq KH] [CharP KH 2] {msgLen : ℕ}

/-! ### The honest values of domain A -/

section Values

variable {F : Type} [Field F]

/-- **The honest UseHint advice** of coefficient `(i, k)` (`mldsa_gadgets.h:381-401`, the relation
at `:403-428`): the sign, the offset and the slack as one digit of base `T^2` each, and the output
bits (`UseHint.honest`). -/
-- spec-side
noncomputable def honestAdvice (y : Native.HonestInput msgLen) (i : Fin nRows) (k : Fin N) :
    UseHint.Advice F 1 r1Bits :=
  UseHint.honest γ₂ wBound 1 r1Bits (hintBool y.h i k) (wCoeff y.key y.c y.z i k)

/-- **The honest `w'` coefficients** as naturals: the canonical representatives below `q`. -/
-- spec-side
noncomputable def honestWNat (y : Native.HonestInput msgLen) (i : Fin nRows) (k : Fin N) : ℕ :=
  (wCoeff y.key y.c y.z i k).val

/-- **The honest `z + (γ₁ - β - 1)`** as naturals (the centered `z` shifted by the norm's
offset). -/
-- spec-side
def honestZNat (y : Native.HonestInput msgLen) (j : Fin nCols) (k : Fin N) : ℕ :=
  (zCentered y.z j k + normOffset).toNat

/-- **The honest support bits** of the challenge as integers (`ternaryBits`'s first bit). -/
-- spec-side
def honestSup (y : Native.HonestInput msgLen) (k : Fin N) : ℤ := if y.c k = 0 then 0 else 1

/-- **The honest sign bits** of the challenge as integers (`ternaryBits`'s second bit). -/
-- spec-side
def honestSgn (y : Native.HonestInput msgLen) (k : Fin N) : ℤ := if y.c k = -1 then 1 else 0

/-- **The honest integer of the signature relation** at coordinate `(i, k)` (`sigInt` of the
honest naturals and bits). -/
-- spec-side
noncomputable def honestSigInt (y : Native.HonestInput msgLen) (i : Fin nRows) (k : Fin N) : ℤ :=
  sigInt y.key (honestWNat y) (honestZNat y) (honestSup y) (honestSgn y) i k

/-- **The honest quotient** of the signature relation at coordinate `(i, k)`:
`(sigInt - q qlo) / q` (`mod.h:541-650`, `committed_digits`; below `Qmax < 645^3`). -/
-- spec-side
noncomputable def honestQuot (y : Native.HonestInput msgLen) (i : Fin nRows) (k : Fin N) : ℕ :=
  ((honestSigInt y i k - q * sigQlo) / q).toNat

/-- **The honest source assignment** of an honest input: ML-DSA native's
(`Native.honestAssignment`: domain H, the crossing bits, the hint and the centered `z`
cast into the field), with `signature.w` the canonical `w'`, the UseHint advice at one digit of
base `T^2` (`honestAdvice`), and the quotient digits of the signature relation the base-`645`
digits of `honestQuot`.

Running time: that of native's honest assignment (`nPerms msgLen` Keccak-f permutations and one
evaluation of `computeWApprox`), `O(k N)` UseHint advice computations on naturals below `q`, and
for each of the `k N` coordinates the relation's integer (`l + 2` negacyclic coefficient sums of
`N` terms, over the key's `ExpandA` in coefficient form) and its three digits.
This running time is argued here, not proved in Lean. -/
-- spec-side
noncomputable def honestAssignment (B : PackedClaim.PackedBasis KH 4) (y : Native.HonestInput msgLen) :
    Source KH F msgLen where
  toSource := { Native.honestAssignment (F := F) B y with
    w := fun i k => (honestWNat y i k : F)
    np := fun i k => (honestAdvice y i k).s
    offset := fun i k => (honestAdvice y i k).lo 0
    slack := fun i k => (honestAdvice y i k).hi 0 }
  quot i k j := (digitsOf sigBase sigDigits (honestQuot y i k) j : F)

end Values

/-! ### The signature relation on the honest values -/

section Relation

variable {y : Native.HonestInput msgLen}

/-- The honest challenge is ternary. -/
theorem c_ternary (y : Native.HonestInput msgLen) (k : Fin N) : y.c k = 0 ∨ y.c k = 1 ∨ y.c k = -1 :=
  MLDSA44.PoP.challenge_ternary _ _ k

/-- **The honest bits recombine to the challenge**: `support - 2 sign = c`. -/
theorem honestSup_sub_honestSgn (y : Native.HonestInput msgLen) :
    (fun k => honestSup y k - 2 * honestSgn y k) = y.c := funext fun k => by
  unfold honestSup honestSgn
  rcases c_ternary y k with hk | hk | hk <;> simp [hk]

/-- The honest support bits have absolute value at most one. -/
theorem natAbs_honestSup_le (y : Native.HonestInput msgLen) (k : Fin N) : (honestSup y k).natAbs ≤ 1 := by
  unfold honestSup
  split_ifs <;> decide

/-- The honest sign bits have absolute value at most one. -/
theorem natAbs_honestSgn_le (y : Native.HonestInput msgLen) (k : Fin N) : (honestSgn y k).natAbs ≤ 1 := by
  unfold honestSgn
  split_ifs <;> decide

/-- An honest centered `z` coefficient is below `γ₁ - β` in magnitude (Algorithm 8's norm check). -/
theorem zCentered_natAbs_lt (hy : y.Valid) (j : Fin nCols) (k : Fin N) :
    (zCentered y.z j k).natAbs < normBound :=
  (MLDSA44.natAbs_centeredRepr_le_polyVecNorm y.z j k).trans_lt hy.checks.1

/-- The shifted honest `z` is the shifted centered integer. -/
theorem honestZNat_cast (hy : y.Valid) (j : Fin nCols) (k : Fin N) :
    (honestZNat y j k : ℤ) = zCentered y.z j k + normOffset := by
  have hz := zCentered_natAbs_lt hy j k
  have hb : 1 ≤ normBound := by decide
  unfold honestZNat
  rw [Int.toNat_of_nonneg (by simp only [normOffset]; omega)]

/-- The shifted honest `z` lies below `2 (γ₁ - β) - 1` (the norm request's honest bound). -/
theorem honestZNat_lt (hy : y.Valid) (j : Fin nCols) (k : Fin N) :
    honestZNat y j k < normHonest := by
  have hz := zCentered_natAbs_lt hy j k
  have hc := honestZNat_cast hy j k
  have hb : 1 ≤ normBound := by decide
  simp only [normOffset] at hc
  simp only [normHonest]
  omega

/-- The honest `w'` naturals lie below `T^2` (they lie below `q`). -/
theorem honestWNat_lt (y : Native.HonestInput msgLen) (i : Fin nRows) (k : Fin N) :
    honestWNat y i k < wBound :=
  (ZMod.val_lt _).trans (by decide)

/-- **The response read from the shifted honest naturals is the input's `z`.** -/
theorem zVec_honestZNat (hy : y.Valid) : zVec (honestZNat y) = y.z := by
  have hs : ((Rows.shift : ℕ) : ℤ) = (normOffset : ℤ) := rfl
  have hc : ∀ j m, ((signedZ (honestZNat y) j m : ℤ) : _root_.MLDSA.Coeff) =
      MLDSA44.coeff (y.z.get j) m := fun j m => by
    rw [signedZ, honestZNat_cast hy, hs, add_sub_cancel_right, zCentered,
      ← LatticeCrypto.centeredRepr_intCast]
  rw [zVec, ← NativeAlgebraCircuit.Honest.ofFn_ofCoeff_coeff y.z]
  exact congrArg Vector.ofFn (funext fun j => congrArg MLDSA44.ofCoeff (funext fun m => hc j m))

/-- **The honest naturals satisfy the congruence of `Emulated.Rows`**
`w' ≡ Σ_j A_ij z_j - c t_i (mod q)`: the honest `w'` is `computeWApprox(Â, c, z, t1)`
(`MLDSA44.PoP.Compose.honestWApprox`; `Rows.congruent_of_computeWApprox`). -/
theorem congruent_honest (hy : y.Valid) :
    Congruent (aKeyOf y.key) (tKeyOf y.key) (honestZNat y) (honestWNat y)
      fun k => honestSup y k - 2 * honestSgn y k := by
  rw [honestSup_sub_honestSgn]
  refine Rows.congruent_of_computeWApprox fun i k => ?_
  rw [zVec_honestZNat hy, honestWNat, ZMod.natCast_zmod_val]
  rfl

/-- **A congruence makes the relation's integer a multiple of `q`**. -/
theorem dvd_sigInt_of_congruent {pk : Native.Rows.PublicKey} {wv : Fin nRows → Fin N → ℕ}
    {zv : Fin nCols → Fin N → ℕ} {s g : Fin N → ℤ}
    (h : Congruent (aKeyOf pk) (tKeyOf pk) zv wv fun k => s k - 2 * g k) (i : Fin nRows)
    (k : Fin N) : (q : ℤ) ∣ sigInt pk wv zv s g i k := by
  have h1 := h i k
  have hT : (fun m => (tKeyOf pk i m : _root_.MLDSA.Coeff)) =
      fun m => (2 : _root_.MLDSA.Coeff) ^ Native.Params.dBits *
        (t1Key pk i m : _root_.MLDSA.Coeff) :=
    funext (tKeyOf_cast pk i)
  have hc : (fun m => ((s m - 2 * g m : ℤ) : _root_.MLDSA.Coeff)) =
      fun m => (s m : _root_.MLDSA.Coeff) - 2 * (g m : _root_.MLDSA.Coeff) := funext fun m => by
    push_cast
    ring
  simp only at h1
  rw [hT, hc, DFT.negacyclicConvCoeff_ternary,
    Falcon512.negacyclicConvCoeff_comm (fun m => ((s m : ℤ) : _root_.MLDSA.Coeff)),
    Falcon512.negacyclicConvCoeff_comm (fun m => ((g m : ℤ) : _root_.MLDSA.Coeff))] at h1
  have h0 : ((sigInt pk wv zv s g i k : ℤ) : _root_.MLDSA.Coeff) = 0 := by
    simp only [sigInt, Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_ofNat,
      Int.cast_natCast, Int.cast_sum, Rows.intCast_negacyclicConvCoeff]
    linear_combination h1
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0

/-- **The honest quotient**: `sigInt - q qlo = q Q` with `Q ≤ Qmax` (the honest integer is a
multiple of `q` in `[sigLo, sigHi]`). -/
theorem honestQuot_spec (hy : y.Valid) (i : Fin nRows) (k : Fin N) :
    honestSigInt y i k - q * sigQlo = q * (honestQuot y i k : ℤ) ∧ honestQuot y i k ≤ sigQmax := by
  obtain ⟨t, ht'⟩ := dvd_sigInt_of_congruent (congruent_honest hy) i k
  have ht : honestSigInt y i k = q * t := ht'
  obtain ⟨hlo, hhi⟩ := sigInt_mem (t1Bounded_pkDecode44 y.pk.key) (honestWNat_lt y)
    (honestZNat_lt hy) (natAbs_honestSup_le y) (natAbs_honestSgn_le y) i k
  change sigLo ≤ honestSigInt y i k at hlo
  change honestSigInt y i k ≤ sigHi at hhi
  rw [ht] at hlo hhi
  rw [sigLo_eq] at hlo
  rw [sigHi_eq] at hhi
  have hq : (q : ℤ) = 8380417 := rfl
  have hdiv : (honestSigInt y i k - q * sigQlo) / q = t - sigQlo := by
    rw [ht, ← mul_sub, Int.mul_ediv_cancel_left _ (by rw [hq]; decide)]
  rw [hq] at hlo hhi
  have hnn : 0 ≤ t - sigQlo := by
    rw [sigQlo_eq]
    omega
  have hQ : (honestQuot y i k : ℤ) = t - sigQlo := by
    rw [honestQuot, hdiv, Int.toNat_of_nonneg hnn]
  refine ⟨?_, ?_⟩
  · rw [hQ, ht]
    ring
  · rw [sigQlo_eq] at hQ
    rw [sigQmax_eq]
    omega

/-- The honest quotient lies below `645^3`. -/
theorem honestQuot_lt (hy : y.Valid) (i : Fin nRows) (k : Fin N) :
    honestQuot y i k < sigBase ^ sigDigits :=
  (honestQuot_spec hy i k).2.trans_lt sigQmax_lt

end Relation

/-! ### The honest algebra constraints -/

section Algebra

variable {F : Type} [Field F] [DecidableEq F] {B : PackedClaim.PackedBasis KH 4}
  {y : Native.HonestInput msgLen}

omit [CharP KH 2] [DecidableEq F] in
/-- **The honest signature relation's committed-digit row** at coordinate `(i, k)`: the value is the
cast of the honest integer (`intCast_sigInt`), which is `q qlo + q Q` for the honest quotient `Q`,
whose digits reconstruct it (`Q < 645^3`). -/
theorem sigRow_honest (hy : y.Valid) (i : Fin nRows) (k : Fin N) :
    SigRow y.key (honestAssignment (F := F) B y) i k := by
  obtain ⟨hQ, -⟩ := honestQuot_spec hy i k
  have hcast := intCast_sigInt (F := F) y.key (w := (honestAssignment (F := F) B y).w)
    (z := (honestAssignment (F := F) B y).z) (c := (honestAssignment (F := F) B y).cA)
    (wv := honestWNat y) (zv := honestZNat y) (s := honestSup y) (g := honestSgn y)
    (fun _ _ => rfl)
    (fun j k => by
      rw [← Int.cast_natCast, honestZNat_cast hy]
      push_cast
      rfl)
    (fun k => by
      change ((honestSup y k : ℤ) : F) = (HashCircuit.ternaryBits (K := F) (y.c k)).1
      unfold honestSup HashCircuit.ternaryBits
      split_ifs <;> simp)
    (fun k => by
      change ((honestSgn y k : ℤ) : F) = (HashCircuit.ternaryBits (K := F) (y.c k)).2
      unfold honestSgn HashCircuit.ternaryBits
      split_ifs <;> simp)
    i k
  have hrec : reconstruct sigBase (List.ofFn ((honestAssignment (F := F) B y).quot i k)) =
      (honestQuot y i k : F) := by
    change reconstruct sigBase (List.ofFn fun j =>
      (digitsOf sigBase sigDigits (honestQuot y i k) j : F)) = _
    rw [reconstruct_digitsOf, Nat.mod_eq_of_lt (honestQuot_lt hy i k)]
  have hF := congrArg (fun v : ℤ => (v : F)) hQ
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast] at hF
  unfold SigRow
  rw [← hcast, hrec]
  change ((honestSigInt y i k : ℤ) : F) - _ - _ = 0
  rw [Int.cast_mul, Int.cast_natCast]
  linear_combination hF

omit [CharP KH 2] in
/-- **The honest UseHint advice passes with the wrap** at coefficient `m` (`UseHint.wrap_complete`
at one digit of base `T^2`), the output bits read from `w1Encode(w1)`
(`NativeAlgebraCircuit.Honest.outputBits_honest`). -/
theorem useHint_honest (m : Fin wDim) :
    UseHint.WrapHolds γ₂ (NativeAlgebraCircuit.flat (honestAssignment (F := F) B y).h m)
      (NativeAlgebraCircuit.flat (honestAssignment (F := F) B y).w m)
      (NativeAlgebraCircuit.flat (honestAssignment (F := F) B y).np m)
      (NativeAlgebraCircuit.flat (honestAssignment (F := F) B y).offset m)
      (NativeAlgebraCircuit.flat (honestAssignment (F := F) B y).slack m)
      (NativeAlgebraCircuit.outputBits (honestAssignment (F := F) B y).w1A m) := by
  have hok := UseHint.wrap_complete (K := F) (γ₂ := γ₂) (B := wBound) (k := 1) (r := r1Bits)
    (by decide) (by decide) (by decide) (by decide) (NativeAlgebraCircuit.flat (hintBool y.h) m)
    (NativeAlgebraCircuit.flat (wCoeff y.key y.c y.z) m)
  dsimp only at hok
  have hbits : NativeAlgebraCircuit.outputBits (honestAssignment (F := F) B y).w1A m =
      (UseHint.honest (K := F) γ₂ wBound 1 r1Bits (NativeAlgebraCircuit.flat (hintBool y.h) m)
        (NativeAlgebraCircuit.flat (wCoeff y.key y.c y.z) m)).bits :=
    NativeAlgebraCircuit.Honest.outputBits_honest y.key y.c y.z y.h m
  rw [Native.reconstruct_fin_one, Native.reconstruct_fin_one] at hok
  rw [hbits]
  exact hok

omit [CharP KH 2] in
/-- **The honest algebra constraints**: the Bit checks, the signature relation's committed-digit
rows and UseHint with the wrap. -/
theorem algebraConstraints_honest (hy : y.Valid) :
    AlgebraConstraints y.key (honestAssignment (F := F) B y) where
  hBool i k := by
    change (((hintBool y.h i k).toNat : ℕ) : F) = 0 ∨ (((hintBool y.h i k).toNat : ℕ) : F) = 1
    cases hintBool y.h i k <;> simp
  cBool k t := by
    fin_cases t
    · exact (Native.ternaryBits_bool (y.c k)).1
    · exact (Native.ternaryBits_bool (y.c k)).2
  w1Bool := Falcon512.HashCircuit.wiresOfByteVec_allBool (K := F) fun p => (honestW1Bytes y p).toNat
  npBool i k := by
    change ((MLDSA44.useHintSign γ₂ _).toNat : F) = 0 ∨ ((MLDSA44.useHintSign γ₂ _).toNat : F) = 1
    cases MLDSA44.useHintSign γ₂ _ <;> simp
  signature := sigRow_honest hy
  useHint := useHint_honest

end Algebra

end GordieHowe.MLDSA44.Emulated
