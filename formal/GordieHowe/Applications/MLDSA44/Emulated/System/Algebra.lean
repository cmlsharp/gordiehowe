-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Emulated.System.Source
public import GordieHowe.Language.Realizations.Lowering
public import GordieHowe.Foundations.Algebra.IntLift
public import GordieHowe.Applications.MLDSA44.Emulated.System.Params
public import GordieHowe.Applications.MLDSA44.System.Params
public import GordieHowe.Applications.MLDSA44.Circuits.NativeAlgebra
public import GordieHowe.Applications.MLDSA44.Gadgets.UseHintWrap
public import GordieHowe.Applications.MLDSA44.Emulated.Rows

@[expose] public section

/-!
# ML-DSA emulated: the algebra of domain A

The algebra constraints of ML-DSA emulated's domain A (`lib/gordiehowe/examples/mldsa/mldsa_emulated.h`,
`mldsa_gadgets.h`), over a field of characteristic `pGold`, in which every ML-DSA value is an
integer:

* **The Bit checks** of the hint `h`, the challenge bits `challenge.c`, the UseHint output bits
  `hint.w1` and the sign advice `hint.nonpositive` (the core's Boolean check on Bit cells).
* **The signature relation** (`signature.relation`, `mldsa_emulated.h:189-210`):
  `assert_mod(w' + 2^d PolyBroadcast(t1)(support - 2 sign), PolyMatVec(a)(z), q)` over the
  integers, with `a = ExpandA(ρ)` in coefficient form (`key.a`, `GordieHowe.MLDSA44.Emulated.Rows.aKeyOf`) and
  `t1` in coefficient form (`key.t1`). Its value `lhs - rhs` at coordinate `(i, k)` is `sigValue`,
  the plan's four terms with coefficients `[1, 8192, -16384, -1]`: `w'`, `t1_i * support`,
  `t1_i * sign` and `Σ_j a_ij * z_j` (negacyclic products). It is a modular equality (interval
  `[sigLo, sigHi]`, modulus `q`) lowered in the committed-digit form: the quotient digits
  `signature.relation.d0..d2` (the source's `quot`), the affine row
  `lhs - rhs - q qlo - q Σ_j B^j d_j = 0` per coordinate (`SigRow`), and the digits' range
  requests.
* **UseHint with the wrap** (`hint.*`, `mldsa_gadgets.h:368-436` with `UseHintArm{kT, true}`, per
  coefficient, `UseHint.WrapHolds`).
* The range requests: `signature.w`, `norm.z`, `hint.offset`, `hint.slack`, `hint.nowrap`,
  `hint_weight.weight` and the relation's digits.

**Soundness.** The relation's value is the cast of an integer `sigInt` (`intCast_sigInt`), which
lies in `[sigLo, sigHi]` (`sigInt_mem`, from the Bit challenge, `w'` below `T^2`, `z`'s norm
request and `t1` below `2^10`). With the committed-digit row and the digits below `T` this gives
the modular equality, so `sigInt` at each coordinate is a multiple of `q`; modulo `q` this is the
congruence `GordieHowe.MLDSA44.Emulated.Rows.Congruent`, so the extracted `w'` is `computeWApprox(Â, c, z, t1)`
(`GordieHowe.MLDSA44.Emulated.Rows.Congruent.computeWApprox`). UseHint holds for the extracted `w'`
(`UseHint.wrap_sound` at `W = T^2`), `‖z‖∞ < γ₁ - β`, and the hint weight is at most `ω`.

**The key's `t1`.** The interval reads `t1`'s coefficients below `2^10` (the operator's entry bound
`EntryBound{kT1Bound}`, `mldsa_emulated.h:206`). That holds for the decoded key of every statement
(`t1Bounded_pkDecode44`), and the theorems here take it as the hypothesis `T1Bounded pk`, a property
of the statement.

**Cross-check against the C++** (`mldsa_emulated.h`, `mldsa_gadgets.h` at `28705d8e`): the
relation's terms and signs, the committed-digit row, UseHint's comparator, interval row and wrap
product, and the Bit checks agree.
-/

namespace GordieHowe.MLDSA44.Emulated

open GordieHowe.Bits Params Range
open Native.Params (q N nRows nCols γ₂ dBits r1Bits normBound normOffset normHonest wDim)
open _root_.MLDSA.Concrete (useHintCoeff)
open Rows (aKeyOf tKeyOf signedZ zVec Congruent)

variable {K : ℕ} {L : RealizedProgram.ProofSystem.PhaseLayout K} {KH F : Type} [Field F] {msgLen : ℕ}

/-! ### The key's `t1` -/

/-- **The coefficients of `t1_i`** as naturals below `q` (`key.t1`). -/
-- spec-side
def t1Key (pk : Native.Rows.PublicKey) (i : Fin nRows) (m : Fin N) : ℕ :=
  ((pk.t1.get i).get m).val

/-- **The key's `t1` coefficients lie below `2^10`** (`kT1Bound`, `mldsa_emulated.h:63`; the entry
bound of `PolyBroadcast(t1)`). -/
def T1Bounded (pk : Native.Rows.PublicKey) : Prop := ∀ i m, t1Key pk i m < t1Bound

/-- The decoded key of a statement has `t1` below `2^10` (`MLDSA44.pkDecode44_t1_lt`). -/
theorem t1Bounded_pkDecode44 (b : MLDSA44.EncodedKey44) : T1Bounded (MLDSA44.pkDecode44 b) :=
  fun i m => MLDSA44.pkDecode44_t1_lt b i m

/-- `t1_i·2^d` modulo `q` (`Rows.tKeyOf`) is `2^d` times `t1`'s coefficient. -/
theorem tKeyOf_cast (pk : Native.Rows.PublicKey) (i : Fin nRows) (m : Fin N) :
    (tKeyOf pk i m : _root_.MLDSA.Coeff) =
      (2 : _root_.MLDSA.Coeff) ^ dBits * (t1Key pk i m : _root_.MLDSA.Coeff) := by
  unfold tKeyOf KeyNTT.vals t1Key
  rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  exact MLDSA44.coeff_power2RoundShift (pk.t1.get i) m

/-! ### The signature relation -/

/-- **The value `lhs - rhs` of the signature relation** at coordinate `(i, k)`
(`mldsa_emulated.h:205-208`):
`w'_ik + 2^d (t1_i * support)_k - 2^(d+1) (t1_i * sign)_k - Σ_j (a_ij * z_j)_k`, negacyclic products
of the public coefficients (`t1Key`, `Rows.aKeyOf`) cast into the field. -/
noncomputable def sigValue (pk : Native.Rows.PublicKey) (w : Fin nRows → Fin N → F)
    (z : Fin nCols → Fin N → F) (c : Fin N → Fin 2 → F) (i : Fin nRows) (k : Fin N) : F :=
  w i k + 2 ^ dBits * LatticeCrypto.negacyclicConvCoeff (fun m => (t1Key pk i m : F))
      (fun m => c m 0) k -
    2 ^ (dBits + 1) * LatticeCrypto.negacyclicConvCoeff (fun m => (t1Key pk i m : F))
      (fun m => c m 1) k -
    ∑ j, LatticeCrypto.negacyclicConvCoeff (fun m => (aKeyOf pk i j m : F)) (z j) k

/-- **The committed-digit row of the signature relation** at coordinate `(i, k)` (`mod.h:541-650`):
`lhs - rhs - q qlo - q Σ_j B^j d_j = 0`, with `B = 645` and the digits the source's `quot`. -/
def SigRow (pk : Native.Rows.PublicKey) (a : Source KH F msgLen) (i : Fin nRows) (k : Fin N) :
    Prop :=
  sigValue pk a.w a.z a.cA i k - ((q * sigQlo : ℤ) : F) -
    (q : F) * reconstruct sigBase (List.ofFn (a.quot i k)) = 0

/-! ### The integer of the relation -/

variable [DecidableEq F]

/-- **The integer of the signature relation** at coordinate `(i, k)`, from naturals `wv` (`w'`),
`zv` (`z + (γ₁ - β - 1)`) and integers `s`, `g` (support and sign):
`wv + 2^d (t1_i * s)_k - 2^(d+1) (t1_i * g)_k - Σ_j (a_ij * (zv_j - (γ₁ - β - 1)))_k`. -/
-- spec-side
noncomputable def sigInt (pk : Native.Rows.PublicKey) (wv : Fin nRows → Fin N → ℕ)
    (zv : Fin nCols → Fin N → ℕ) (s g : Fin N → ℤ) (i : Fin nRows) (k : Fin N) : ℤ :=
  wv i k + 2 ^ dBits * LatticeCrypto.negacyclicConvCoeff (fun m => (t1Key pk i m : ℤ)) s k -
    2 ^ (dBits + 1) * LatticeCrypto.negacyclicConvCoeff (fun m => (t1Key pk i m : ℤ)) g k -
    ∑ j, LatticeCrypto.negacyclicConvCoeff (fun m => (aKeyOf pk i j m : ℤ)) (signedZ zv j) k

omit [DecidableEq F] in
/-- **The integer's cast is the relation's value** when the naturals and integers are the casts
of `w'`, `z + (γ₁ - β - 1)` and the challenge bits. -/
theorem intCast_sigInt (pk : Native.Rows.PublicKey) {w : Fin nRows → Fin N → F}
    {z : Fin nCols → Fin N → F} {c : Fin N → Fin 2 → F} {wv : Fin nRows → Fin N → ℕ}
    {zv : Fin nCols → Fin N → ℕ} {s g : Fin N → ℤ} (hw : ∀ i k, (wv i k : F) = w i k)
    (hz : ∀ j k, (zv j k : F) = z j k + (normOffset : F)) (hs : ∀ k, (s k : F) = c k 0)
    (hg : ∀ k, (g k : F) = c k 1) (i : Fin nRows) (k : Fin N) :
    ((sigInt pk wv zv s g i k : ℤ) : F) = sigValue pk w z c i k := by
  have hz' : ∀ j, (fun m => ((signedZ zv j m : ℤ) : F)) = z j := fun j => funext fun m => by
    simp only [signedZ, Int.cast_sub, Int.cast_natCast, hz]
    simp [Rows.shift, normOffset]
  simp only [sigInt, sigValue, Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_pow,
    Int.cast_ofNat, Int.cast_natCast, Int.cast_sum, Rows.intCast_negacyclicConvCoeff,
    hw, hs, hg, hz']

/-- **The relation's integer lies in its interval** `[sigLo, sigHi]`: `w'` below `T^2`, the two
broadcast terms each at most `2^d r` and `2^(d+1) r` in absolute value (`r = N (2^10 - 1)`, `t1`
below `2^10`, bits of absolute value at most one), and `Σ_j a_ij * z_j` at most
`L N (q - 1) (γ₁ - β - 1)` (`a` below `q`, `|z| ≤ γ₁ - β - 1`). `ht1` is a property of the
statement. -/
theorem sigInt_mem {pk : Native.Rows.PublicKey} (ht1 : T1Bounded pk)
    {wv : Fin nRows → Fin N → ℕ} {zv : Fin nCols → Fin N → ℕ} {s g : Fin N → ℤ}
    (hw : ∀ i k, wv i k < wBound) (hz : ∀ j m, zv j m < normHonest)
    (hs : ∀ m, (s m).natAbs ≤ 1) (hg : ∀ m, (g m).natAbs ≤ 1) (i : Fin nRows) (k : Fin N) :
    sigLo ≤ sigInt pk wv zv s g i k ∧ sigInt pk wv zv s g i k ≤ sigHi := by
  have hT : ∀ m, ((t1Key pk i m : ℤ)).natAbs ≤ t1Bound - 1 := fun m => by
    rw [Int.natAbs_natCast]
    have := ht1 i m
    omega
  have hA : ∀ j m, ((aKeyOf pk i j m : ℤ)).natAbs ≤ q - 1 := fun j m => by
    rw [Int.natAbs_natCast]
    have := Rows.aKeyOf_lt pk i j m
    exact Nat.le_sub_one_of_lt this
  have hZ : ∀ j m, (signedZ zv j m).natAbs ≤ normBound - 1 := fun j m => by
    have := hz j m
    have hb : normBound = 130994 := by decide
    simp only [signedZ, Rows.shift, normHonest, hb] at this ⊢
    omega
  have h1 : (LatticeCrypto.negacyclicConvCoeff (fun m => (t1Key pk i m : ℤ)) s k).natAbs ≤
      261888 := (Rows.natAbs_negacyclicConvCoeff_le hT hs k).trans (by decide)
  have h2 : (LatticeCrypto.negacyclicConvCoeff (fun m => (t1Key pk i m : ℤ)) g k).natAbs ≤
      261888 := (Rows.natAbs_negacyclicConvCoeff_le hT hg k).trans (by decide)
  have h3 : (∑ j, LatticeCrypto.negacyclicConvCoeff (fun m => (aKeyOf pk i j m : ℤ))
      (signedZ zv j) k).natAbs ≤ 1124122453082112 :=
    (Int.natAbs_sum_le _ _).trans ((Finset.sum_le_sum fun j _ =>
      Rows.natAbs_negacyclicConvCoeff_le (hA j) (hZ j) k).trans
        (by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]; decide))
  have e1 := LatticeCrypto.neg_le_and_le_of_natAbs_le h1
  have e2 := LatticeCrypto.neg_le_and_le_of_natAbs_le h2
  have e3 := LatticeCrypto.neg_le_and_le_of_natAbs_le h3
  have hwk := hw i k
  have hd : (2 : ℤ) ^ dBits = 8192 := by decide
  have hd1 : (2 : ℤ) ^ (dBits + 1) = 16384 := by decide
  rw [sigLo_eq, sigHi_eq, sigInt, hd, hd1]
  simp only [wBound, T] at hwk
  push_cast at e1 e2 e3
  constructor <;> omega

/-! ### UseHint, the constraints and the specification -/

/-- **The algebra constraints of domain A** at the public key: the Bit checks, the signature
relation's committed-digit rows and UseHint with the wrap at every coefficient. -/
structure AlgebraConstraints (pk : Native.Rows.PublicKey) (a : Source KH F msgLen) : Prop where
  /-- The hint is Boolean. -/
  hBool : ∀ i k, a.h i k = 0 ∨ a.h i k = 1
  /-- The challenge bits are Boolean. -/
  cBool : ∀ k t, a.cA k t = 0 ∨ a.cA k t = 1
  /-- The UseHint output bits are Boolean. -/
  w1Bool : AllBool a.w1A
  /-- The sign advice is Boolean. -/
  npBool : ∀ i k, a.np i k = 0 ∨ a.np i k = 1
  /-- The signature relation's committed-digit rows. -/
  signature : ∀ i k, SigRow pk a i k
  /-- UseHint with the wrap at every coefficient. -/
  useHint : ∀ m : Fin wDim, UseHint.WrapHolds γ₂ (NativeAlgebraCircuit.flat a.h m) (NativeAlgebraCircuit.flat a.w m)
    (NativeAlgebraCircuit.flat a.np m) (NativeAlgebraCircuit.flat a.offset m) (NativeAlgebraCircuit.flat a.slack m)
    (NativeAlgebraCircuit.outputBits a.w1A m)

end GordieHowe.MLDSA44.Emulated
