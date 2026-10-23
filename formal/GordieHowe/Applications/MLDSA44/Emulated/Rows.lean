-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Rows.NativeLinear
public import GordieHowe.Applications.MLDSA44.Native.Rows
public import GordieHowe.Applications.MLDSA44.Spec.KeyNTT
import all LatticeCrypto.MLDSA.Concrete.Rounding
import all LatticeCrypto.MLDSA.Concrete.NTT

@[expose] public section

/-!
# ML-DSA-44 emulated signature congruence

The emulated ML-DSA-44 A circuit (`signature_relation` in
`lib/gordiehowe/examples/mldsa/mldsa_emulated.h`, benchmarked by `MLDSAEmulated.DISABLED_Bench`, over
Goldilocks `F_{p²}`) checks the signature relation `w′ + 2^d·t1 * c ≡ Σ_j A_ij * z_j (mod q)` as an
integer congruence: `A` and `t1` enter in coefficient form, `c = sup − 2·sgn`, `z` is read through
the digits of the shifted `zsh = z + (b − 1)` with `b = γ₁ − β`, and the lowering subtracts a bias
that is a multiple of `q` and commits the quotient. The congruence follows from the integer equation
when the two sides differ by less than `p`.

`Congruent` is the congruence `w′ ≡ Σ_j A_ij * z_j − c * t_i (mod q)` with `z = zsh − (b − 1)`
(`signedZ`). The keys are the verifier's decoding of the public key `pk`: `A_ij = NTT⁻¹(Â_ij)`
(`aKeyOf pk`) and `t_i = t1_i·2^d` (`tKeyOf pk`). At these keys, `Congruent.computeWApprox` reads
the congruence as the coefficients of `computeWApprox(Â, c, z, t1)` (`GordieHowe.MLDSA44.coeff_computeWApprox`),
and `congruent_of_computeWApprox` is the converse. `natAbs_negacyclicConvCoeff_le` and
`intCast_negacyclicConvCoeff` bound and cast the negacyclic products.
-/

namespace GordieHowe.MLDSA44.Emulated.Rows

open Native.Rows

/-! ### Parameters -/

/-- `q`. -/
abbrev q : ℕ := _root_.MLDSA.modulus

/-- `b − 1 = γ₁ − β − 1`, the shift from `z` to the committed `zsh = z + (b − 1)`. -/
abbrev shift : ℕ := mldsa44.normBound - 1

example : q = 8380417 := rfl
example : shift = 130993 := by decide

variable {F : Type*} [Field F]

/-! ### Negacyclic products of bounded integer vectors -/

/-- A coefficient of the negacyclic product of vectors bounded by `A` and `B` is at most
`n·(A·B)` in absolute value. -/
theorem natAbs_negacyclicConvCoeff_le {n A B : ℕ} {f g : Fin n → ℤ}
    (hf : ∀ i, (f i).natAbs ≤ A) (hg : ∀ j, (g j).natAbs ≤ B) (k : Fin n) :
    (LatticeCrypto.negacyclicConvCoeff f g k).natAbs ≤ n * (A * B) := by
  rw [DFT.negacyclicConvCoeff_eq_sum]
  refine (Int.natAbs_sum_le _ _).trans ?_
  calc ∑ a, (if a ≤ k then f a * g (k - a) else -(f a * g (k - a))).natAbs
      ≤ ∑ _a : Fin n, A * B := Finset.sum_le_sum fun a _ => by
        split_ifs <;>
          simpa only [Int.natAbs_neg, Int.natAbs_mul] using Nat.mul_le_mul (hf a) (hg _)
    _ = n * (A * B) := by simp

/-- Casting integer vectors commutes with the negacyclic product. -/
theorem intCast_negacyclicConvCoeff {R : Type*} [CommRing R] {n : ℕ} (f g : Fin n → ℤ)
    (k : Fin n) :
    ((LatticeCrypto.negacyclicConvCoeff f g k : ℤ) : R) =
      LatticeCrypto.negacyclicConvCoeff (fun m => (f m : R)) (fun m => (g m : R)) k := by
  simpa [Function.comp_def] using DFT.negacyclicConvCoeff_map (Int.castRingHom R) f g k

/-! ### Integer meaning -/

/-- The signed `z = zsh − (b − 1)` of a shifted natural. -/
-- spec-side
def signedZ (zv : Fin nCols → Fin deg → ℕ) (j : Fin nCols) (m : Fin deg) : ℤ := zv j m - shift

/-- `w′ ≡ Σ_j A_ij * z_j − c * t_i (mod q)` coefficientwise, in the order of
`MLDSA44.coeff_computeWApprox`. -/
def Congruent (aKey : Fin nRows → Fin nCols → Fin deg → ℕ) (tKey : Fin nRows → Fin deg → ℕ)
    (zv : Fin nCols → Fin deg → ℕ) (wv : Fin nRows → Fin deg → ℕ) (c : Fin deg → ℤ) : Prop :=
  ∀ i k, (wv i k : _root_.MLDSA.Coeff) =
    ∑ j, LatticeCrypto.negacyclicConvCoeff (fun m => (aKey i j m : _root_.MLDSA.Coeff))
        (fun m => (signedZ zv j m : _root_.MLDSA.Coeff)) k -
      LatticeCrypto.negacyclicConvCoeff (fun m => (c m : _root_.MLDSA.Coeff))
        (fun m => (tKey i m : _root_.MLDSA.Coeff)) k

/-! ### The vendored form -/

/-- `A_ij = NTT⁻¹(Â_ij)` as naturals below `q`. -/
-- spec-side
noncomputable def aKeyOf (pk : PublicKey) (i : Fin nRows) (j : Fin nCols) : Fin deg → ℕ :=
  KeyNTT.vals (aEntry pk i j)

/-- `t1_i·2^d` as naturals below `q`. -/
-- spec-side
def tKeyOf (pk : PublicKey) (i : Fin nRows) : Fin deg → ℕ :=
  KeyNTT.vals (_root_.MLDSA.Concrete.power2RoundShift (pk.t1.get i))

theorem aKeyOf_lt (pk : PublicKey) (i : Fin nRows) (j : Fin nCols) (m : Fin deg) :
    aKeyOf pk i j m < q := KeyNTT.vals_lt _ m

/-- The signature response `z` from the shifted naturals. -/
-- spec-side
def zVec (zv : Fin nCols → Fin deg → ℕ) : _root_.MLDSA.RqVec _root_.MLDSA.mldsa44.l :=
  Vector.ofFn fun j => MLDSA44.ofCoeff fun m => (signedZ zv j m : _root_.MLDSA.Coeff)

/-- The right side of `Congruent` at the keys of `pk` is coefficient `k` of `A·z − c·t1·2^d` in
the form `MLDSA44.coeff_computeWApprox` states, with `z` read from the shifted naturals. -/
theorem congruent_rhs_eq (pk : PublicKey) (zv : Fin nCols → Fin deg → ℕ) (c : Fin deg → ℤ)
    (i : Fin nRows) (k : Fin deg) :
    ∑ j, LatticeCrypto.negacyclicConvCoeff (fun m => (aKeyOf pk i j m : _root_.MLDSA.Coeff))
        (fun m => (signedZ zv j m : _root_.MLDSA.Coeff)) k -
      LatticeCrypto.negacyclicConvCoeff (fun m => (c m : _root_.MLDSA.Coeff))
        (fun m => (tKeyOf pk i m : _root_.MLDSA.Coeff)) k =
    ∑ j : Fin nCols, LatticeCrypto.negacyclicConvCoeff
        (MLDSA44.coeff (_root_.MLDSA.Concrete.concreteNTTRingOps.fromHat
          (((aHat pk).get i).get j)))
        (MLDSA44.coeff ((zVec zv).get j)) k -
      LatticeCrypto.negacyclicConvCoeff (fun k' => (c k' : _root_.MLDSA.Coeff))
        (fun k' => (2 ^ _root_.MLDSA.droppedBits : _root_.MLDSA.Coeff) *
          MLDSA44.coeff (pk.t1.get i) k') k := by
  have hA : ∀ j, (fun m => (aKeyOf pk i j m : _root_.MLDSA.Coeff)) =
      MLDSA44.coeff (_root_.MLDSA.Concrete.concreteNTTRingOps.fromHat (((aHat pk).get i).get j)) :=
    fun j => funext fun m => by
      unfold aKeyOf KeyNTT.vals
      rw [ZMod.natCast_zmod_val]
      rfl
  have hZ : ∀ j, (fun m => (signedZ zv j m : _root_.MLDSA.Coeff)) = MLDSA44.coeff ((zVec zv).get j) :=
    fun j => by rw [zVec, Vector.get_ofFn, MLDSA44.coeff_ofCoeff]
  have hT : (fun m => (tKeyOf pk i m : _root_.MLDSA.Coeff)) =
      fun k' => (2 ^ _root_.MLDSA.droppedBits : _root_.MLDSA.Coeff) * MLDSA44.coeff (pk.t1.get i) k' :=
    funext fun m => by
      unfold tKeyOf KeyNTT.vals
      rw [ZMod.natCast_zmod_val]
      exact MLDSA44.coeff_power2RoundShift (pk.t1.get i) m
  simp only [hA, hZ, hT]

/-- **The congruence in the vendored form.** At the keys of `pk`, `Congruent` is coefficient `k`
of `w′_approx = A·z − c·t1·2^d` in the form `MLDSA44.coeff_computeWApprox` states, with `z` read from
the shifted naturals. -/
theorem Congruent.computeWApprox {pk : PublicKey} {zv : Fin nCols → Fin deg → ℕ}
    {wv : Fin nRows → Fin deg → ℕ} {c : Fin deg → ℤ}
    (h : Congruent (aKeyOf pk) (tKeyOf pk) zv wv c) (i : Fin nRows) (k : Fin deg) :
    (wv i k : _root_.MLDSA.Coeff) =
      ∑ j : Fin nCols, LatticeCrypto.negacyclicConvCoeff
          (MLDSA44.coeff (_root_.MLDSA.Concrete.concreteNTTRingOps.fromHat
            (((aHat pk).get i).get j)))
          (MLDSA44.coeff ((zVec zv).get j)) k -
        LatticeCrypto.negacyclicConvCoeff (fun k' => (c k' : _root_.MLDSA.Coeff))
          (fun k' => (2 ^ _root_.MLDSA.droppedBits : _root_.MLDSA.Coeff) *
            MLDSA44.coeff (pk.t1.get i) k') k :=
  (h i k).trans (congruent_rhs_eq pk zv c i k)

/-- **The congruence from `computeWApprox`**, the converse: naturals whose residues are the
coefficients of `computeWApprox(Â, c, z, t1)` satisfy `Congruent` at the keys of `pk`. -/
theorem congruent_of_computeWApprox {pk : PublicKey} {zv : Fin nCols → Fin deg → ℕ}
    {wv : Fin nRows → Fin deg → ℕ} {c : Fin deg → ℤ}
    (h : ∀ i k, (wv i k : _root_.MLDSA.Coeff) =
      MLDSA44.coeff ((_root_.MLDSA.computeWApprox _root_.MLDSA.mldsa44 prims
        (nttOps := _root_.MLDSA.Concrete.concreteNTTRingOps) (aHat pk)
        (MLDSA44.ofCoeff fun k' => (c k' : _root_.MLDSA.Coeff)) (zVec zv) pk.t1).get i) k) :
    Congruent (aKeyOf pk) (tKeyOf pk) zv wv c := fun i k => by
  rw [h i k, MLDSA44.coeff_computeWApprox, MLDSA44.coeff_ofCoeff, congruent_rhs_eq]

end GordieHowe.MLDSA44.Emulated.Rows
