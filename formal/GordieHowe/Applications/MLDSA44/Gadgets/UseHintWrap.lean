-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Gadgets.UseHint

@[expose] public section

/-!
# UseHint with the wrap as a Bit quotient

The GordieHowe emulated arm of UseHint (`lib/gordiehowe/examples/mldsa/mldsa_gadgets.h`,
`use_hint` with `UseHintArm{kT, wrap = true}`: the wrap is a Bit quotient with no cell). Per
coefficient, over a field of characteristic `p`, the gadget reads the hint `h`, the committed `w'`
coefficient `w`, the advice `nonpositive` (`s`), `offset`, `slack` and the output bits `w1`, and
asserts:

* `w1_bound`: `leq(w1, M - 1)`, a comparator on the bits (`Bits.leConst`);
* `interval`: `offset + slack - (γ₂ - 1) - endpoint = 0` (`IntervalEq`);
* `decompose`: with `e = w - (2 γ₂ raw_high + lower + offset)` (`relationResult`),
  `e (e - q) = 0`.

`e` lies in `{0, q}`: the wrap is the Bit quotient `e / q`, which has no cell. The corner gadget
`UseHint.emulated` commits that bit as `corner` and asserts `result + q corner = w`; this gadget
asserts the product instead, and the soundness proof recovers the corner bit from it
(`exists_corner`) and then runs `UseHint.emulated_sound`.

The C++ realizes `offset` and `slack` as range requests below `T^2` (two digits each, bound to them,
`mldsa_gadgets.h:408-409`); here they enter as single digits of base `B` (`IsNatBelow B`), the
established bound of those requests, as native's `useHint_sound` does with one digit of `T^2`. The
Booleanity of `h`, `s` and the output bits is the core's Boolean check on Bit cells, a hypothesis of
the soundness theorem.
-/

namespace GordieHowe.MLDSA44.UseHint

open _root_.MLDSA _root_.MLDSA.Concrete GordieHowe.MLDSA44

variable {K : Type*} [Field K] [DecidableEq K]

/-- **UseHint with the wrap at one coefficient** (`mldsa_gadgets.h:402-428`, `ARM.wrap`): the output
bits encode a value at most `M - 1` (`w1_bound`), the interval row, and the decomposition up to a
Bit multiple of `q` (`decompose`, `e (e - q) = 0`), on the hint `h`, the coefficient `w`, the sign
advice `s`, the offset and the slack. -/
structure WrapHolds (γ₂ : ℕ) (h w s offset slack : K) {r : ℕ} (bits : BitWires K r) : Prop where
  /-- `w1_bound`: the output is at most `M - 1`. -/
  le : Bits.leConst bits (hiCount γ₂ - 1) = 1
  /-- The interval row. -/
  interval : IntervalEq γ₂ h s offset slack (outputFromBits (hiCount γ₂) bits)
  /-- The decomposition with the wrap: `e (e - q) = 0` for `e = w - result`. -/
  wrap : (w - relationResult γ₂ (hiCount γ₂) h s offset (outputFromBits (hiCount γ₂) bits)) *
    (w - relationResult γ₂ (hiCount γ₂) h s offset (outputFromBits (hiCount γ₂) bits) -
      (modulus : K)) = 0

omit [DecidableEq K] in
/-- **The wrap is a Bit quotient**: `e (e - q) = 0` makes `e = q c` for a bit `c`, that is
`w = result + q c` with `c` the corner bit of `UseHint.emulated`. -/
theorem exists_corner {w res : K} (h : (w - res) * (w - res - (modulus : K)) = 0) :
    ∃ c : Bool, res + (modulus : K) * ((c.toNat : ℕ) : K) = w := by
  rcases mul_eq_zero.mp h with h0 | h1
  · exact ⟨false, by simp only [Bool.toNat_false, Nat.cast_zero, mul_zero, add_zero]
                     exact (sub_eq_zero.mp h0).symm⟩
  · refine ⟨true, ?_⟩
    simp only [Bool.toNat_true, Nat.cast_one, mul_one]
    linear_combination -h1

omit [DecidableEq K] in
/-- **The corner bit gives the wrap**: `w = result + q c` with `c` a bit satisfies `e (e - q) = 0`. -/
theorem wrap_of_corner {w res c : K} (hc : c = 0 ∨ c = 1) (h : res + (modulus : K) * c = w) :
    (w - res) * (w - res - (modulus : K)) = 0 := by
  rw [← h]
  rcases hc with rfl | rfl <;> ring

omit [DecidableEq K] in
/-- `b (b - 1) = 0` for a bit. -/
theorem mul_sub_one_of_bit {x : K} (h : x = 0 ∨ x = 1) : x * (x - 1) = 0 := by
  rcases h with rfl | rfl <;> ring

omit [DecidableEq K] in
/-- The reconstruction of one digit is the digit. -/
theorem reconstruct_ofFn_single (B : ℕ) (x : K) : Range.reconstruct B (List.ofFn ![x]) = x := by
  simp [Range.reconstruct]

/-- **UseHint with the wrap is sound** (`UseHint.emulated_sound` on the corner bit of
`exists_corner`, with the offset and the slack as single digits of base `B`). Over a field of
characteristic `p`: the hint is a bit, the output is below `M`, and every natural `n < W` that `w`
is the cast of has UseHint the output modulo `q`. `hγ`, `hdvd`, `hchar`, `hr` and `hWp` are
parameter conditions (`W` bounds the caller's natural for `w`, `W + 2q ≤ p`); `hh`, `hs`, `hbits`
are the Boolean checks of the Bit cells; `hoff`, `hsl` the range requests of `offset` and `slack`
at their established bound `B`. -/
theorem wrap_sound {p : ℕ} [CharP K p] {γ₂ B r W : ℕ} (hγ : 0 < γ₂)
    (hdvd : 2 * γ₂ ∣ modulus - 1) (hchar : 2 * (B - 1) < p) (hr : hiCount γ₂ < 2 ^ r)
    (hWp : W + 2 * modulus ≤ p) {h w s offset slack : K} {bits : BitWires K r}
    (huh : WrapHolds γ₂ h w s offset slack bits) (hh : h = 0 ∨ h = 1) (hs : s = 0 ∨ s = 1)
    (hbits : Bits.AllBool bits) (hoff : Range.IsNatBelow B offset)
    (hsl : Range.IsNatBelow B slack) :
    EmulatedHolds γ₂ W h w (Bits.natOfBits bits) := by
  obtain ⟨c, hc⟩ := exists_corner huh.wrap
  have hok : (emulated γ₂ B 1 h w s ((c.toNat : ℕ) : K) ![offset] ![slack] bits).ok = true := by
    refine emulated_ok_iff.mpr ⟨mul_sub_one_of_bit hh, mul_sub_one_of_bit hs,
      mul_sub_one_of_bit (by cases c <;> simp), fun b => mul_sub_one_of_bit (hbits b), huh.le, ?_,
      ?_⟩
    · rw [reconstruct_ofFn_single, reconstruct_ofFn_single]
      exact huh.interval
    · rw [reconstruct_ofFn_single]
      exact hc
  refine emulated_sound hγ hdvd (by rwa [pow_one]) hr hWp hok fun v hv => ?_
  simp only [emulated_needles, List.ofFn_succ, Matrix.cons_val_zero, List.ofFn_zero,
    List.interleavePairs, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl
  · exact hoff
  · exact hsl

/-- **UseHint with the wrap is complete**: the honest advice of `UseHint.emulated`
(`UseHint.honest`, the sign, the offset and slack limbs, the output bits) satisfies the constraints
at the canonical representative `w = wc.val`, with the offset and the slack the reconstructions of
the honest limbs. The wrap is `honestCorner` (`UseHint.emulated_complete`). `hγ`, `hdvd`, `hr` and
`hγB` are parameter conditions. -/
theorem wrap_complete {γ₂ B k r : ℕ} (hγ : 0 < γ₂) (hdvd : 2 * γ₂ ∣ modulus - 1)
    (hr : hiCount γ₂ < 2 ^ r) (hγB : γ₂ < B ^ k) (hb : Bool) (wc : Coeff) :
    let a := honest (K := K) γ₂ B k r hb wc
    WrapHolds γ₂ ((hb.toNat : ℕ) : K) (wc.val : K) a.s (Range.reconstruct B (List.ofFn a.lo))
      (Range.reconstruct B (List.ofFn a.hi)) a.bits := by
  intro a
  obtain ⟨hok, -⟩ := emulated_complete (K := K) hγ hdvd hr hγB hb wc
  obtain ⟨-, -, hcbit, -, hle, hint, hres⟩ := emulated_ok_iff.mp hok
  exact ⟨hle, hint, wrap_of_corner (bit_of_mul_sub hcbit) hres⟩

end GordieHowe.MLDSA44.UseHint
