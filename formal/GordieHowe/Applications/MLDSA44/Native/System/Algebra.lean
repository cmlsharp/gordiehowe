-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.System.Source
public import GordieHowe.Language.Realizations.Lowering
public import GordieHowe.Foundations.Algebra.IntLift
public import GordieHowe.Applications.Shared.MACProfiles
public import GordieHowe.Applications.Params
public import GordieHowe.ProofSystem.Ligero.MaskTest.Pieces
public import GordieHowe.ProofSystem.Ligero.RelativeLayout
public import GordieHowe.ProofSystem.Ligero.SubfieldTest
public import GordieHowe.Foundations.ToMathlib.NNRealDyadic
public import GordieHowe.Foundations.Fields.Goldilocks
public import GordieHowe.Foundations.Fields.GoldilocksQuartic
public import GordieHowe.Foundations.Fields.GF2_256
public import GordieHowe.Foundations.Fields.GF2_128
public import GordieHowe.Applications.MLDSA44.System.Params
public import GordieHowe.Applications.MLDSA44.Circuits.NativeAlgebra

@[expose] public section

/-!
# ML-DSA native: the algebra of domain A

The algebra constraints of ML-DSA native's domain A (`lib/gordiehowe/examples/mldsa/mldsa_native.h`,
`mldsa_gadgets.h`), over a field of characteristic `q = 8380417`:

* **The Bit checks** of the hint `h`, the challenge bits `challenge.c`, the UseHint output bits
  `hint.w1` and the sign advice `hint.nonpositive` (the core's Boolean check on Bit cells).
* **The signature relation** (`signature.relation`, `mldsa_native.h:156-174`, `K N` affine rows):
  `w' - PolyMatVec(Â)(z) + 2^d PolyBroadcast(t1)(support - 2 sign) = 0`, the rows
  `GordieHowe.MLDSA44.Native.Rows.rows` (the same terms: `Â` in NTT form at `ψ = 1753`, `t1` in coefficient form).
* **UseHint** (`hint.*`, `mldsa_gadgets.h:368-436`, per coefficient, `UseHintHolds`): the output
  bits below `M` (`w1_bound`, a comparator: `Bits.leConst`), the interval row
  `offset + slack = (γ₂ - 1) + endpoint` and the decomposition `w' = 2 γ₂ raw_high + lower + offset`
  (the native arm has no wrap, `UseHintArm{kT}`), the relation of `UseHint` (`IntervalEq`,
  `relationResult`, `outputFromBits`).
* The range requests: `norm.z`, `hint.offset`, `hint.slack`, `hint.nowrap`,
  `hint_weight.weight`.

`AlgebraConstraints` collects these checks at a public key. **Soundness of UseHint**
(`useHint_sound`): at each coefficient, `w1 = UseHint(h, w')` (`UseHint.relation_sound` at one
digit of base `T^2`, then `GordieHowe.MLDSA44.useHintCoeff_of_relation`).
-/

namespace GordieHowe.MLDSA44.Native

open GordieHowe.Bits Params Range
open _root_.MLDSA.Concrete (useHintCoeff)

variable {KH F : Type} [Field F] [DecidableEq F] [CharP F _root_.MLDSA.modulus] {msgLen : ℕ}

/-- **UseHint at one coefficient** (`mldsa_gadgets.h:402-428`): the output bits encode a value
below `M` (`w1_bound`), the interval row and the decomposition, on the hint `h`, the coefficient
`w`, the sign advice `s`, the offset and the slack. -/
structure UseHintHolds (h w s offset slack : F) (bits : BitWires F r1Bits) : Prop where
  /-- `w1_bound`: the output is at most `M - 1`. -/
  le : Bits.leConst bits (UseHint.hiCount γ₂ - 1) = 1
  /-- The interval row. -/
  interval : UseHint.IntervalEq γ₂ h s offset slack (UseHint.outputFromBits (UseHint.hiCount γ₂) bits)
  /-- The decomposition. -/
  decompose : w = UseHint.relationResult γ₂ (UseHint.hiCount γ₂) h s offset
    (UseHint.outputFromBits (UseHint.hiCount γ₂) bits)

/-- **The algebra constraints of domain A** at the public key: the Bit checks, the signature rows
and UseHint at every coefficient. -/
structure AlgebraConstraints (pk : Rows.PublicKey) (a : Source KH F msgLen) : Prop where
  /-- The hint is Boolean. -/
  hBool : ∀ i k, a.h i k = 0 ∨ a.h i k = 1
  /-- The challenge bits are Boolean. -/
  cBool : ∀ k t, a.cA k t = 0 ∨ a.cA k t = 1
  /-- The UseHint output bits are Boolean. -/
  w1Bool : AllBool a.w1A
  /-- The sign advice is Boolean. -/
  npBool : ∀ i k, a.np i k = 0 ∨ a.np i k = 1
  /-- The signature rows. -/
  signature : rowsHold (Rows.rows pk) (sigWit a)
  /-- UseHint at every coefficient. -/
  useHint : ∀ m : Fin wDim, UseHintHolds (NativeAlgebraCircuit.flat a.h m) (NativeAlgebraCircuit.flat a.w m)
    (NativeAlgebraCircuit.flat a.np m) (NativeAlgebraCircuit.flat a.offset m) (NativeAlgebraCircuit.flat a.slack m)
    (NativeAlgebraCircuit.outputBits a.w1A m)

omit [DecidableEq F] [CharP F _root_.MLDSA.modulus] in
/-- The reconstruction of one digit is the digit. -/
theorem reconstruct_ofFn_one (B : ℕ) (x : F) : reconstruct B (List.ofFn ![x]) = x := by
  simp [reconstruct]

/-- **UseHint at one coefficient is sound** (`UseHint.relation_sound` with the offset and the slack
as single digits of base `T^2`, the established bounds of `hint.offset` and `hint.slack`): the hint
is a bit, the output is below `M`, `w` is the image of an integer, and every integer representative
of `w` has UseHint the output modulo `q`. -/
theorem useHint_sound {h w s offset slack : F} {bits : BitWires F r1Bits}
    (huh : UseHintHolds h w s offset slack bits) (hh : h = 0 ∨ h = 1) (hs : s = 0 ∨ s = 1)
    (hbits : AllBool bits) (hoff : IsNatBelow (T * T) offset) (hsl : IsNatBelow (T * T) slack) :
    UseHint.NativeHolds γ₂ h w (natOfBits bits) := by
  have hγ : 0 < γ₂ := by decide
  have hdvd : 2 * γ₂ ∣ _root_.MLDSA.modulus - 1 := by decide
  have hM : 0 < UseHint.hiCount γ₂ := by decide
  have hγp : γ₂ < _root_.MLDSA.modulus := by decide
  obtain ⟨hb, rfl⟩ := UseHint.exists_bool_of_bit hh
  obtain ⟨sb, rfl⟩ := UseHint.exists_bool_of_bit hs
  have hint : UseHint.IntervalEq γ₂ ((hb.toNat : ℕ) : F) (sb.toNat : ℕ)
      (reconstruct (T * T) (List.ofFn ![offset])) (reconstruct (T * T) (List.ofFn ![slack]))
      (UseHint.outputFromBits (UseHint.hiCount γ₂) bits) := by
    rw [reconstruct_ofFn_one, reconstruct_ofFn_one]
    exact huh.interval
  obtain ⟨hy, off, sl, hsum, hreseq⟩ := UseHint.relation_sound (B := T * T) (k := 1) hγ
    (by decide) hγp (by decide) hM hb sb hbits huh.le (fun l => by fin_cases l; exact hoff)
    (fun l => by fin_cases l; exact hsl) hint
  rw [reconstruct_ofFn_one] at hreseq
  have hres := huh.decompose
  rw [hreseq] at hres
  refine ⟨Or.imp id id hh, hy, ⟨_, hres.symm⟩, fun n hn' => ?_⟩
  rw [UseHint.decide_toNat_eq_one]
  have hcong : ((n : ℤ) : _root_.MLDSA.Coeff) = ((2 * γ₂ * MLDSA44.useHintRawHigh (UseHint.hiCount γ₂) hb sb _ +
      MLDSA44.useHintLow γ₂ (UseHint.hiCount γ₂) hb sb _ off : ℤ) : _root_.MLDSA.Coeff) :=
    (CharP.intCast_eq_intCast (ZMod _root_.MLDSA.modulus) _root_.MLDSA.modulus).mpr
      ((CharP.intCast_eq_intCast F _root_.MLDSA.modulus).mp (hn'.trans hres))
  exact MLDSA44.useHintCoeff_of_relation hγ hdvd hy hsum hcong

end GordieHowe.MLDSA44.Native
