-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Circuits.NativeAlgebra
public import GordieHowe.Applications.MLDSA44.PoP.ComposeHonest
public import GordieHowe.Applications.Rows.MAC
public import GordieHowe.Model.IOP.PadMasked

@[expose] public section

/-!
# Honest advice for the native ML-DSA-44 A circuit

Witness generation by the prover for the native A circuit, not circuit operations:

* `Pads`: the pads selected before either verifier challenge (the shared MAC pad secret, the row
  pads, the mask of the low MAC quotient digits and the mask of the dynamic histogram);
* `hintBool`, `wCoeff`, `zCentered`: the hint bits, the coefficients of the honest
  `w′ = A·z − c·t₁·2^d` as canonical representatives (`GordieHowe.MLDSA44.PoP.Compose.honestWApprox`), and
  `z` as centered integers;
* `outputBits_honest`: the honest UseHint output bits are the `w1Encode` bits of
  `w1 = UseHint(h, w′)`; both arms commit these bits;
* `card_hintBool_le`: the hint weight in the flat coefficient order;
* `ofFn_ofCoeff_coeff`: a vector of polynomials reassembled from its coefficients.
-/

namespace GordieHowe.MLDSA44.NativeAlgebraCircuit.Honest

open Native.Rows
open _root_.MLDSA.Concrete (Hint useHintCoeff w1Encode)

variable {K F : Type*} [Field K] [DecidableEq K] [Field F] [DecidableEq F] {mw : ℕ}
  {taps : Finset ℕ} {A : NativeArm mldsa44 mw taps}

/-- Reassembling a vector of polynomials from its coefficients. -/
theorem ofFn_ofCoeff_coeff {n : ℕ} (v : Vector _root_.MLDSA.Rq n) :
    (Vector.ofFn fun i => MLDSA44.ofCoeff fun k => MLDSA44.coeff (v.get i) k) = v := by
  apply Vector.ext
  intro i hi
  simp [MLDSA44.ofCoeff_coeff, Vector.get_eq_getElem]

/-! ### The honest witness -/

/-- The hint bit of coefficient `(i, k)`. -/
-- spec-side
def hintBool (h : Vector Hint _root_.MLDSA.mldsa44.k) (i : Fin nRows) (k : Fin deg) : Bool :=
  (h.get i).get k

/-- Coefficient `(i, k)` of the honest `w′`. -/
-- spec-side
noncomputable def wCoeff (pk : PublicKey) (c : Fin mldsa44.N → ℤ) (z : _root_.MLDSA.RqVec nCols)
    (i : Fin nRows) (k : Fin deg) : _root_.MLDSA.Coeff :=
  MLDSA44.coeff ((MLDSA44.PoP.Compose.honestWApprox pk c z).get i) k

/-- The centered integer of coefficient `(j, k)` of `z`. -/
-- spec-side
def zCentered (z : _root_.MLDSA.RqVec nCols) (j : Fin nCols) (k : Fin deg) : ℤ :=
  LatticeCrypto.centeredRepr (MLDSA44.coeff (z.get j) k)

omit [DecidableEq K] [DecidableEq F] in
/-- The honest UseHint output bits of coefficient `m` are the bits of `UseHint(h, w′)` at `m`:
bits `6·m + b` of `w1Encode(w1)` (`MLDSA44.w1Encode_testBit`). Both arms commit these bits. -/
theorem outputBits_honest (pk : PublicKey) (c : Fin mldsa44.N → ℤ) (z : _root_.MLDSA.RqVec nCols)
    (h : Vector Hint _root_.MLDSA.mldsa44.k) (m : Fin (nRows * deg)) :
    outputBits (Falcon512.HashCircuit.wiresOfByteVec (K := F) fun p => (MLDSA44.PoP.Compose.honestW1Bytes pk c z h p).toNat)
        m =
      fun b : Fin mldsa44.r1_bits => Bits.constBit
        (useHintCoeff (flat (hintBool h) m) (flat (wCoeff pk c z) m) mldsa44.γ₂) b := by
  obtain ⟨⟨i, k⟩, rfl⟩ := finProdFinEquiv.surjective m
  funext b
  rw [flat_apply, flat_apply]
  let G : ℕ → F := fun t =>
    if ((w1Encode _root_.MLDSA.mldsa44 (MLDSA44.PoP.Compose.honestW1 pk c z h)).getD (t / 8) 0).toNat.testBit
      (t % 8) then 1 else 0
  have hG : outputBits (Falcon512.HashCircuit.wiresOfByteVec (K := F) fun p =>
      (MLDSA44.PoP.Compose.honestW1Bytes pk c z h p).toNat) (finProdFinEquiv (i, k)) b =
      G (6 * (finProdFinEquiv (i, k) : ℕ) + b) := by
    show Bits.constBit _ _ = _
    rw [SelectFirstTau.constBit_eq_ite_testBit]
    rfl
  let b' : Fin 6 := ⟨b, b.isLt⟩
  have hidx : 6 * (finProdFinEquiv (i, k) : ℕ) + b =
      ((i : ℕ) * _root_.MLDSA.ringDegree + k) * 6 + (b' : ℕ) := by
    rw [finProdFinEquiv_apply_val]
    change 6 * ((k : ℕ) + 256 * i) + b = ((i : ℕ) * 256 + k) * 6 + b
    ring
  have hval : ((MLDSA44.PoP.Compose.honestW1 pk c z h).get i).get k =
      (useHintCoeff (hintBool h i k) (wCoeff pk c z i k) mldsa44.γ₂ : _root_.MLDSA.Coeff) :=
    MLDSA44.PoP.Compose.coeff_honestW1 pk c z h i k
  have hlt : useHintCoeff (hintBool h i k) (wCoeff pk c z i k) mldsa44.γ₂ < _root_.MLDSA.modulus :=
    (MLDSA44.useHintCoeff_lt (by decide) (by decide) _ _).trans (by decide)
  rw [hG, hidx]
  simp only [G]
  rw [MLDSA44.w1Encode_testBit (MLDSA44.PoP.Compose.honestW1 pk c z h) i k b', hval, ZMod.val_natCast,
    Nat.mod_eq_of_lt hlt, SelectFirstTau.constBit_eq_ite_testBit]

section Witness

variable (pk : PublicKey) (c : Fin mldsa44.N → ℤ) (z : _root_.MLDSA.RqVec nCols)
  (h : Vector Hint _root_.MLDSA.mldsa44.k)

omit [DecidableEq K] in
/-- The hint weight, reindexed to the flat coefficient order. -/
theorem card_hintBool_le (hω : _root_.MLDSA.Concrete.hintWeightVec h ≤ _root_.MLDSA.mldsa44.omega) :
    (Finset.univ.filter fun m => flat (hintBool h) m = true).card ≤ mldsa44.ω := by
  have hofFn : h = Vector.ofFn fun i => Vector.ofFn fun k => hintBool h i k := by
    apply Vector.ext
    intro i hi
    apply Vector.ext
    intro k hk
    simp [hintBool, Vector.get_eq_getElem]
  rw [hofFn, MLDSA44.hintWeightVec_ofFn] at hω
  refine le_of_eq_of_le (Finset.card_equiv finProdFinEquiv.symm fun m => ?_) hω
  simp [flat]

end Witness

end GordieHowe.MLDSA44.NativeAlgebraCircuit.Honest
